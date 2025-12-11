import Mathlib
open Lean

inductive LispVal
  | natVal (n : Nat) : LispVal
  | boolVal (b : Bool) : LispVal
  | invalid : LispVal
  deriving Repr, Inhabited

abbrev LispM := StateT  (Std.HashMap Name LispVal) MetaM

def LispM.addVar (name : Name) (val : LispVal) :
    LispM Unit := do
  modify (·.insert name val)

def LispM.eraseVar (name : Name) :
    LispM Unit := do
  modify (·.erase name)

def LispVal.add : LispVal → LispVal → LispVal
  | LispVal.natVal n1, LispVal.natVal n2 => LispVal.natVal (n1 + n2)
  | _, _ => LispVal.invalid

def LispVal.lt : LispVal → LispVal → LispVal
  | LispVal.natVal n1, LispVal.natVal n2 => LispVal.boolVal (n1 < n2)
  | _, _ => LispVal.invalid

def LispVal.ifThenElse : LispVal → LispVal → LispVal → LispVal
  | LispVal.boolVal true, thenBranch, _ => thenBranch
  | LispVal.boolVal false, _, elseBranch => elseBranch
  | _, _, _ => LispVal.invalid

declare_syntax_cat lisp_expr

syntax "T" : lisp_expr
syntax "NIL" : lisp_expr

syntax (name := num_as_lisp) num : lisp_expr

syntax "(" ")" : lisp_expr -- false

syntax "(" "+" lisp_expr* ")" : lisp_expr

syntax "(" "<" lisp_expr lisp_expr ")" : lisp_expr

syntax "(" "if" lisp_expr lisp_expr lisp_expr ")"
  : lisp_expr

syntax "(" "let" ident lisp_expr lisp_expr ")"
  : lisp_expr

syntax ident : lisp_expr

partial def parseLispVal : TSyntax `lisp_expr → LispM LispVal
  | `(lisp_expr| T) => return LispVal.boolVal true
  | `(lisp_expr| NIL) => return LispVal.boolVal false
  | `(lisp_expr| $n:num) => return LispVal.natVal n.getNat
  | `(lisp_expr| (+ $xs*)) => do
    let vals ← xs.mapM parseLispVal
    return vals.foldl (·.add ·) (LispVal.natVal 0)
  | `(lisp_expr| (< $x $y)) => do
    let vx ← parseLispVal x
    let vy ← parseLispVal y
    return vx.lt vy
  | `(lisp_expr| (if $cond $thenBranch $elseBranch)) => do
    let vcond ← parseLispVal cond
    let vthen ← parseLispVal thenBranch
    let velse ← parseLispVal elseBranch
    return vcond.ifThenElse vthen velse
  | `(lisp_expr| (let $id:ident $val $body)) =>   do
    let vval ← parseLispVal val
    LispM.addVar id.getId vval
    let result ← parseLispVal body
    LispM.eraseVar id.getId
    return result
  | `(lisp_expr| $id:ident) => do
    let env ← get
    match env.get? id.getId with
    | some v => return v
    | none => return LispVal.invalid
  | _ => Elab.throwUnsupportedSyntax


elab "lisp%" e:lisp_expr : term => do
  let lispVal ← (parseLispVal e).run' {}
  match lispVal with
  | LispVal.natVal n => return toExpr n
  | LispVal.boolVal b => return toExpr b
  | LispVal.invalid => Elab.throwUnsupportedSyntax

#eval lisp% (+ 3 4 (+ 5 3)) -- 15
#eval lisp% (if (< (+ 2 3) (+ 4 5)) (+ 10 20) (+ 30 40)) -- 30

#eval lisp% (let x (+ 2 3) (let y (+ x 4) (+ y 5))) -- 14
