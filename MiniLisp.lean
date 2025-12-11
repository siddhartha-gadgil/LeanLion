import Mathlib
open Lean

inductive LispVal
  | natVal (n : Nat) : LispVal
  | boolVal (b : Bool) : LispVal
  | invalid : LispVal
  deriving Repr

declare_syntax_cat lisp_expr

syntax "T" : lisp_expr
syntax "NIL" : lisp_expr

syntax (name := num_as_lisp) num : lisp_expr

syntax "(" ")" : lisp_expr -- false

syntax "(" "+" lisp_expr* ")" : lisp_expr

syntax "(" "<" lisp_expr lisp_expr ")" : lisp_expr

syntax "(" "if" lisp_expr lisp_expr lisp_expr ")"
  : lisp_expr

mutual
  partial def getNatFromLispExpr : TSyntax `lisp_expr → MetaM Nat
  | `(lisp_expr| $n:num) => return n.getNat
  | `(lisp_expr| (+ $xs*)) => do
    let ns ← xs.mapM getNatFromLispExpr
    return ns.foldl (· + ·) 0
  | `(lisp_expr| (if $cond $thenBranch $elseBranch)) => do
    let b ← getBoolFromLispExpr cond
    if b then
      getNatFromLispExpr thenBranch
    else
      getNatFromLispExpr elseBranch
  | _ => Elab.throwUnsupportedSyntax

  partial def getBoolFromLispExpr : TSyntax `lisp_expr → MetaM Bool
  | `(lisp_expr| T) => return true
  | `(lisp_expr| NIL) => return false
  | `(lisp_expr| (< $x $y)) => do
    let nx ← getNatFromLispExpr x
    let ny ← getNatFromLispExpr y
    return nx < ny
  | _ => Elab.throwUnsupportedSyntax
end


elab "lisp_nat%" n:lisp_expr : term => do
  let nat ← getNatFromLispExpr n
  return toExpr nat

#eval lisp_nat% (+ 3 4 (+ 5 3)) -- 15

#eval lisp_nat% (if (< (+ 2 3) (+ 4 5)) (+ 10 20) (+ 30 40)) -- 30
