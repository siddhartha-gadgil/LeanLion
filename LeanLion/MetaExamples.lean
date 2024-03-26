import Lean

open Lean Meta Elab Term

macro "[" y:term "forr" x:ident "in" l:term "]" : term => do
  `(List.map (fun $x => $y) $l)

#eval [x * x forr x in [1, 2, 3, 4, 5]]

elab "[" y:term "forrr" x:ident "in" l:term "]" : term => do
  let lExpr ← elabTerm l none
  match ← inferType lExpr with
  | .app (.const name _) _ =>
    match name with
    | `List =>
      let stx ← `(List.map (fun $x => $y) $l)
      elabTerm stx none
    | ``Array =>
      let stx ← `(Array.toList (Array.map (fun $x => $y) $l))
      elabTerm stx none
    | _ => throwError s!"expected a list or array, got {name}"
  | _ => throwError s!"expected a list or array, got {← ppExpr lExpr}"


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
