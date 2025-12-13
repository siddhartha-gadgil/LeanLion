import Lean
import Std

open Lean Meta Elab Term

/-!
# IMP: A tiny imperative language

* Int ::= the domain of (unbounded) integer numbers, with usual operations on them
* Bool ::= the domain of Booleans Id ::= standard identifiers
* AExp ::= Int | Id |  AExp + AExp | AExp / AExp * BExp ::= Bool | AExp <= AExp | | !BExp | BExp && BExp

* Block ::= {} | { Stmt}
* Stmt ::= Block | Id = AExp; | Stmt Stmt | if(BExp) Block else Block | while(BExp) Block
* Pgm ::= int List{Id}; Stmt

- When we run a program, we only change state
- We can drop the requirement of declaration in advance, so we just have statements.
-/
partial def getNatM (e: Expr) : MetaM Nat := do
  if ← isDefEq e (mkConst ``Nat.zero)
    then return 0
  else
    let n ← mkFreshExprMVar (mkConst ``Nat)
    let nSucc ← mkAppM ``Nat.succ #[n]
    if ← isDefEq e nSucc
    then
      let pred ← getNatM n
      return pred + 1
    else
      throwError s!"Expression {← ppExpr e} is not a natural number"

def getNatRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Nat := do
  match vars with
  | [] =>
    let e ← elabTermEnsuringType t (mkConst ``Nat)
    getNatM e
  | (n, val) :: tail =>
    withLetDecl n (mkConst ``Nat) (toExpr val)
      fun _ => getNatRelVarsM tail t

elab "get_nat%" t:term : term => do
  let e ← elabTerm t (mkConst ``Nat)
  let n ← getNatM e
  return toExpr n

#eval get_nat% 4 * 5

elab "get_nat_rel_n%" t:term : term => do
  let n ← getNatRelVarsM [(`n, 3)] t
  return toExpr n

#eval get_nat% 3 * 5

#eval get_nat_rel_n% (3 * 5 + n)

def getBoolM (e: Expr) : MetaM Bool := do
  if ← isDefEq e (mkConst ``Bool.false)
    then return false
  else
    if ← isDefEq e (mkConst ``Bool.true)
    then
      return true
    else
      throwError s!"Expression {← ppExpr e} is not a boolean"

def getBoolRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Bool := do
  match vars with
  | [] =>
    let e ← elabTermEnsuringType t (mkConst ``Bool)
    getBoolM e
  | (n, val) :: tail =>
    withLetDecl n (mkConst ``Bool) (toExpr val)
      fun _ => getBoolRelVarsM tail t


namespace ImpLang

-- variables with name
abbrev ImpLangM :=
  StateT  (Std.HashMap Name Int) TermElabM

def getVar (name: Name) : ImpLangM Int := do
  let m ← get
  return m.get! name

def setVar (name : Name) (value : Int) :
  ImpLangM Unit := do
  modify (fun m => m.insert name value)

declare_syntax_cat arith_exp
syntax num : arith_exp
syntax ident : arith_exp
syntax arith_exp "+" arith_exp : arith_exp
syntax arith_exp "/" arith_exp : arith_exp
syntax "(" arith_exp ")" : arith_exp
syntax "[" term "]" : arith_exp -- for testing

declare_syntax_cat bool_exp
syntax "T" : bool_exp
syntax "F" : bool_exp
syntax "!" bool_exp:70 : bool_exp
syntax bool_exp:35 "&&" bool_exp:36 : bool_exp
syntax "(" bool_exp ")" : bool_exp
syntax arith_exp "≤" arith_exp : bool_exp

declare_syntax_cat imp_statement

syntax imp_block := "{" (imp_statement)? "}"

syntax imp_block : imp_statement

syntax imp_statement imp_statement : imp_statement

syntax ident ":=" arith_exp ";" : imp_statement

syntax "if" ppSpace "(" bool_exp ")" ppSpace imp_block "else" imp_block : imp_statement

syntax "while" "(" bool_exp ")" ppSpace imp_block : imp_statement

inductive Statement where
| block (s: Option Statement)
| pair (first second: Statement)
| assignment (var: Name) (value: Int)
| if_statement (condition: Bool)
  (then_statement else_statement : Option Statement)
| while_statement (condition: Bool) (body: Option Statement)
deriving Repr, Inhabited, ToExpr

partial def getIntM : TSyntax `arith_exp → ImpLangM Int
| `(arith_exp| ($e:arith_exp)) => getIntM e
| `(arith_exp| [$e:term]) => do
  let m ← get
  getNatRelVarsM (m.toList.map (fun (k, v) => (k, v.toNat))) e
| `(arith_exp| $n:num) => return n.getNat
| `(arith_exp| $a:arith_exp + $b:arith_exp) => do
  let aInt ← getIntM a
  let bInt ← getIntM b
  return aInt + bInt
| `(arith_exp| $a:arith_exp / $b:arith_exp) => do
  let aInt ← getIntM a
  let bInt ← getIntM b
  return aInt / bInt
| `(arith_exp| $n:ident) => do
  getVar n.getId
| _ => Elab.throwUnsupportedSyntax

partial def getBoolM : TSyntax `bool_exp → ImpLangM Bool
| `(bool_exp| T) => return true
| `(bool_exp| F) => return false
| `(bool_exp| ! $b) => do
  let bVal ← getBoolM b
  return ¬bVal
| `(bool_exp| $b && $b' ) => do
  let bVal ← getBoolM b
  let bVal' ← getBoolM b'
  return bVal && bVal'
| `(bool_exp | $x:arith_exp ≤ $y:arith_exp) => do
  let xVal ← getIntM x
  let yVal ← getIntM y
  return xVal ≤ yVal
| `(bool_exp| ($b)) => getBoolM b
| _ => throwUnsupportedSyntax

partial def runStatementM :
  TSyntax `imp_statement → ImpLangM Unit
| `(imp_statement| {}) => return
| `(imp_statement| {$s}) => do
    runStatementM s
| `(imp_statement| $s₁ $s₂) => do
  runStatementM s₁
  runStatementM s₂
| `(imp_statement| $name:ident := $val ;) => do
  let value ← getIntM val
  let n := name.getId
  setVar n value
| `(imp_statement| if ($p) $t else $e) => do
  let c ← getBoolM p
  if c
    then runBlockM t
    else runBlockM e
| w@`(imp_statement| while ($p) $b) => do
  let c ← getBoolM p
  if c then
    runBlockM b
    runStatementM w
| _ => throwUnsupportedSyntax
where runBlockM (bs : TSyntax ``imp_block): ImpLangM Unit :=
  match bs with
  | `(imp_block| {}) => return
  | `(imp_block| {$s}) =>
    runStatementM s
  | _ => throwUnsupportedSyntax


-- Side effects not controlled. Only for testing.
partial def getStatementM :
  TSyntax `imp_statement → ImpLangM Statement
| `(imp_statement| {}) => return .block (none)
| `(imp_statement| {$s}) => do
  let stat ← getStatementM s
  return .block (some stat)
| `(imp_statement| $s₁ $s₂) => do
  let stat₁ ← getStatementM s₁
  let stat₂ ← getStatementM s₂
  return .pair stat₁ stat₂
| `(imp_statement| $name:ident := $val ;) => do
  let value ← getIntM val
  let n := name.getId
  setVar n value
  return .assignment n value
| `(imp_statement| if ($p) $t else $e) => do
  let c ← getBoolM p
  let then_block ← getBlockM t
  let else_block ← getBlockM e
  return .if_statement c then_block else_block
| `(imp_statement| while ($p) $b) => do
  let c ← getBoolM p
  let body ← getBlockM b
  return .while_statement c body
| _ => throwUnsupportedSyntax
where getBlockM (bs : TSyntax ``imp_block): ImpLangM (Option Statement) :=
  match bs with
  | `(imp_block| {}) => return none
  | `(imp_block| {$s}) =>
    -- Error: will give side-effects on all branches
    getStatementM s
  | _ => throwUnsupportedSyntax


elab "#run_stat" s:imp_statement "go" : command  =>
  Command.liftTermElabM do
  let (_, m) ← runStatementM s |>.run {}
  logInfo m!"Final variable state: {m.toList}"


#run_stat
  n := 3; m := 4 + 5;
  if (2 ≤ n) {n := (5 + 3 + [2 * 7]);} else {n := 2; m := 7;}
  go

#run_stat
  n := 10; sum := 0;
  i := 1;
  while (i ≤ n) {sum := sum + i; i := i + 1;} go


elab "bool%" b:bool_exp ";" : term => do
  let bVal ← getBoolM b |>.run' {}
  return toExpr bVal

#eval bool% (!T) && F;

#eval (!true) && false

#eval 3 + 4

#eval bool% 3 ≤ 2 ;

elab "imp_stat%" s:imp_statement : term  => do
  let (stat, m) ← getStatementM s |>.run {}
  logInfo m!"Final variable state: {m.toList}"
  return toExpr stat

#eval imp_stat% n := 3; m := 4;
  if (2 ≤ n) {} else {n := 2;}

#eval 1 + 2

#check withLetDecl

elab "checklet" t:term : term => do
  withLetDecl `n (mkConst ``Nat) (mkConst ``Nat.zero) fun _ => do
    let e ← elabTerm t none
    logInfo e
    let v ←
      getNatM e
    logInfo m!"value: {v};"
    return mkConst ``Nat.zero

#eval checklet (n + 3)

#check mkLetFVars
