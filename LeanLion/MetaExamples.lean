import Lean

open Lean Meta Elab Term


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
    | _ => none
  let stx ← delab expr?.get!
  let m := env.constants.map₁
  let names := m.toList.map (·.1)
  let ids := identifiersFromSyntax stx
  return ids.filter (names.contains)

#eval identifiersFromName ``List.filterMap

elab "fn" a:ident "::" t:term "|->" b:term : term => do
  let type ← elabType t
  let name := a.getId
  withLocalDecl name BinderInfo.default type fun x => do
    let body ← elabTerm b none
    mkLambdaFVars #[x] body

#check mkIdent

def f := fn a :: Nat |-> a + 1

#eval f 3

macro "[" y:term "forr" x:ident "in" l:term "]" : term => do
  `(List.map (fun $x => $y) $l)

#eval [x * x forr x in [1, 2, 3, 4, 5]]

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
