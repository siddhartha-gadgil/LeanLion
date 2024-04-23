import Lean
open Lean Meta Elab Command Syntax
/-!
## Meta-programming in Lean

Lean has a powerful meta-programming framework that allows you to write programs that generate Lean code.
-/

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

/-!
Suppose we want a more sophisticated variant, where the same syntax can handle both `List` and `Array` comprehensions, using `List.map` and `Array.map` respectively.

For this we need more than just a macro, we need an elaborator. An elaborator is a function that takes a syntax object and returns an expression object.
-/

/-!
Our next example is a macro, but a more complex one. Suppose we want to handle nested list comprehensions, for example `[x * x for x in l for l in [[1, 5, 2], [3, 4, 5]]]`. This has to be resolved to:

`List.bind [[1, 5, 2], [3, 4, 5]] (fun l => List.map (fun x => x * x) l)`.

In general, the innermost `for` is resolved to a `List.map`, and the all the outer `for`s are resolved to a `List.bind`.
-/
#check List.bind -- List.bind.{u, v} {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β
