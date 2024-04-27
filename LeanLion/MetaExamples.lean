import Lean
open Lean Meta Elab Command Syntax
/-!
## Meta-programming in Lean

Lean has a powerful meta-programming framework that allows you to write programs that generate Lean code.
-/

namespace lean_lion
/-!
## Getting bitten by multiple instances

The first example is inspired by conversations from this workshop. One of the annoying and mysterious errors is when two instances of the same typeclass are used in a term.
-/
instance Collapse : HAdd String String String where
  hAdd := String.append

def collapse (a b: String): String :=
  @HAdd.hAdd String String String Collapse a b

instance Collapse' : HAdd String String String where
  hAdd := fun a b => a ++ " " ++ b

def collapse' (a b: String): String :=
  @HAdd.hAdd String String String Collapse' a b


example (a b  : String) : collapse' a b = collapse a b := by
  unfold collapse collapse'
  -- rfl
  sorry

/-!
We write code to check if two instances of the same typeclass are used in a term.
-/
def clashInstances (a b : Expr) : MetaM Bool := do
  let aType ← inferType a
  let bType ← inferType b
  match ((← isClass? aType), (← isClass? bType)) with
  | (some x, some y) =>
    if (x = y) && (← isDefEq aType  bType) then
        let instancesEqual ← isDefEq a b
        return !instancesEqual
      else
        return false
  | _ =>
    return false

open Term
elab "check_clashes" a:term "with" b:term : term => do
  let a ← elabTerm a none
  let b ← elabTerm b none
  let res ← clashInstances a b
  return toExpr res

#eval check_clashes Collapse with Collapse' -- true
#eval check_clashes Collapse with Collapse -- false
#eval check_clashes 1 with 2 -- false

/-!
## Subexpressions

Our next step is to extract all subexpressions of a given expression.
-/
def subExprs : Expr →  List Expr
| .app f a => subExprs f ++ subExprs a
| .lam _ d b _ => subExprs d ++ subExprs b
| .forallE _ d b _ => subExprs d ++ subExprs b
| .letE _ t v b _ => subExprs t ++ subExprs v ++ subExprs b
| .lit e => [.lit e]
| .const n l => [.const n l]
| _ => []


elab "sub_exprs" e:term : term => do
  let e ← elabTerm e none
  let res := subExprs e
  let subs ← res.mapM fun e => do
    let fmt ← ppExpr e
    pure fmt.pretty
  return toExpr subs.eraseDups

#eval sub_exprs fun (n : Nat) ↦ (1 + n) * 3

open Lean.Elab.Tactic
elab "check_clashes" : tactic => do
  withMainContext do
    let goal ← getMainTarget
    let subExprs := subExprs goal
    for e in subExprs do
      for e' in subExprs do
        let res ← clashInstances e e'
        if res then
          let type ← inferType e
          logError m!"Clash found: `{← ppExpr e}` and `{← ppExpr e'}` are instances of the same typeclass `{← ppExpr type}` with different instances."
          throwAbortTactic
  return ()

-- example (a b  : String) : collapse' a b = collapse a b := by
--   unfold collapse collapse'
--   check_clashes

/-!
The first layer of meta-programming is `Core`, where we can access and modify the environment.
-/
#check findDocString? -- Lean.findDocString? (env : Environment) (declName : Name) (includeBuiltin : Bool := true) : IO (Option String)

#check Environment.constants  -- Lean.Environment.constants (self : Environment) : ConstMap

#print ConstMap -- SMap Name ConstantInfo

#check SMap.map₁ -- Lean.SMap.map₁.{u, v} {α : Type u} {β : Type v} [inst✝ : BEq α] [inst✝¹ : Hashable α] (self : SMap α β) : HashMap α β

def docStringM? (name: Name) : CoreM (Option String) := do
  let env ← getEnv
  findDocString? env name

#eval docStringM? ``List.filterMap

def constantsWithList : CoreM (List Name) := do
  let env ← getEnv
  let m := env.constants.map₁
  let names := m.toList.map (·.1)
  let names := names.filter (``List).isPrefixOf
  return names

#eval constantsWithList

partial def identifiersFromSyntax (stx: Syntax) : List Name :=
  match stx with
  | .ident _ _ name .. => [name]
  | .node _ _ args .. => args.foldl (init := []) fun acc arg => acc ++ identifiersFromSyntax arg
  | _ => []

open PrettyPrinter Delaborator in
def identifiersFromName (name: Name) : MetaM (List Name) := do
  let env ← getEnv
  let info? := env.find? name
  let expr? := match info? with
    | some (.defnInfo dfn) =>
        some dfn.value
    | some (.thmInfo dfn) =>
        some dfn.value
    | _ => none
  let stx ← delab expr?.get!
  let m := env.constants.map₁
  let names := m.toList.map (·.1)
  let ids := identifiersFromSyntax stx
  return ids.filter (names.contains)

def getCtors (name: Name) : MetaM (List Name) := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
  | some (.inductInfo ind) =>
    return ind.ctors
  | _ => throwError "Not an inductive type"

#eval getCtors ``Expr
#eval getCtors ``ConstantInfo

#check ConstantInfo.rec

#check @Nat.rec (motive := fun _ => String)

def fct (n: Nat) : Nat :=
match n with
| 0 => 1
| n + 1 => (n + 1) * (fct n)

#eval fct 5

noncomputable def fct' : Nat → Nat :=
  Nat.rec 1 (fun n val => (n + 1) * val)

example : fct' 0 = 1 := rfl
example (n: Nat) : fct' (Nat.succ n) =
        (n + 1) * (fct' n) := rfl

#eval identifiersFromName ``Nat.le_of_succ_le_succ

elab "fn" a:ident "::" t:term "|->" b:term : term => do
  let type ← elabType t
  let name := a.getId
  withLocalDecl name BinderInfo.default type fun x => do
    let body ← elabTerm b none
    mkLambdaFVars #[x] body

#check mkIdent

def f := fn a :: Nat |-> a + 1

#eval f 3


/-!
## Extracting identifiers in a proof/definition

We can work directly with `Expr` objects to extract identifiers. However, this gives a lot of information that we might not need, indeed we would like suppressed.

Alternatively, we can use the `PrettyPrinter` module to delaborate the `Expr` object into a `Term` (i.e. `Syntax.term`) object, which shows relevant information.
-/

#check Environment.find? -- Lean.Environment.find? (env : Environment) (n : Name) : Option ConstantInfo

#check ConstantInfo.defnInfo -- Lean.ConstantInfo.defnInfo (val : DefinitionVal) : ConstantInfo

#check PrettyPrinter.delab -- Lean.PrettyPrinter.delab (e : Expr) (optionsPerPos : PrettyPrinter.Delaborator.OptionsPerPos := ∅) : MetaM Term

/-!
## New Syntax: Macros and Elaborators

A macro creates new syntax and transforms it into previously defined syntax. As an example we introduce python-like list comprehension syntax,
for example `[x * x  for x in [1, 2, 3]]`.

In Lean, the above should be translated to `List.map (fun x => x * x) [1, 2, 3]`.
-/
#check List.map -- List.map.{u, v} {α : Type u} {β : Type v} (f : α → β) (a✝ : List α) : List β

macro "[" y:term "forr" x:ident "in" l:term "]" : term => do
  `(List.map (fun $x => $y) $l)

#eval [x * x forr x in [1, 2, 3, 4, 5]]



/-!
Suppose we want a more sophisticated variant, where the same syntax can handle both `List` and `Array` comprehensions, using `List.map` and `Array.map` respectively.

For this we need more than just a macro, we need an elaborator. An elaborator is a function that takes a syntax object and returns an expression object.
-/

elab "[" y:term "forrr" x:ident "in" l:term "]" : term => do
  let lExpr ← elabTerm l none
  match ← inferType lExpr with
  | .app (.const name _) _ =>
    match name with
    | ``List =>
      let stx ← `(List.map (fun $x => $y) $l)
      elabTerm stx none
    | ``Array =>
      let stx ← `(Array.toList (Array.map (fun $x => $y) $l))
      elabTerm stx none
    | _ => throwError s!"expected a list or array, got {name}"
  | _ => throwError s!"expected a list or array, got {← Meta.ppExpr lExpr}"


#eval [x * x forrr x in [2, 3]]



/-!
Our next example is a macro, but a more complex one. Suppose we want to handle nested list comprehensions, for example `[x * x for x in l for l in [[1, 5, 2], [3, 4, 5]]]`. This has to be resolved to:

`List.bind [[1, 5, 2], [3, 4, 5]] (fun l => List.map (fun x => x * x) l)`.

In general, the innermost `for` is resolved to a `List.map`, and the all the outer `for`s are resolved to a `List.bind`.
-/
#check List.bind -- List.bind.{u, v} {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β

declare_syntax_cat python_for
syntax "for#" ident "in" term : python_for

syntax "[" term python_for* "]" : term

macro_rules
| `([ $y:term $l:python_for ]) => do
  match l with
  | `(python_for| for# $x:ident in $l) => do
    `(List.map (fun $x => $y) $l)
  | _ => Macro.throwUnsupported
| `([ $y:term $ls:python_for* $l:python_for]) => do
  let init ← `([ $y:term $ls:python_for* ])
  match l with
  | `(python_for| for# $x:ident in $l) => do
    `(List.bind $l (fun $x => $init))
  | _ => Macro.throwUnsupported

#eval [x * x for# x in [1, 2, 3, 4, 5]]
#eval [x * x for# x in l for# l in [[1, 5, 2], [3, 4, 5]]]
