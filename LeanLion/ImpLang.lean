import Lean
import Std

open Lean Meta Elab Term

/-!
# IMP: A tiny imperative language

* Nat ::= the domain of (unbounded) Nateger numbers, with usual operations on them
* Bool ::= the domain of Booleans Id ::= standard identifiers
* AExp ::= Nat | Id |  AExp + AExp | AExp / AExp * BExp ::= Bool | AExp <= AExp | | !BExp | BExp && BExp

* Block ::= {} | { Stmt}
* Stmt ::= Block | Id = AExp; | Stmt Stmt | if(BExp) Block else Block | while(BExp) Block
* Pgm ::= Nat List{Id}; Stmt

- When we run a program, we only change state
- We can drop the requirement of declaration in advance, so we just have statements.
-/
def exprRelVars (vars: List (Name × Nat)) (stx: Syntax.Term) : MetaM Syntax.Term :=
  match vars with
  | [] => return stx
  | (n, val) :: tail => do
    let nId := mkIdent n
    let nat := mkIdent ``Nat
    let inner ←
      exprRelVars tail stx
    let arg := Syntax.mkNumLit <| toString val
    `((fun ($nId : $nat) => $inner) $arg)

partial def getNatM (e: Expr) : TermElabM Nat := do
  let e ← instantiateMVars e
  Term.synthesizeSyntheticMVarsNoPostponing
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
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Nat (mkConst ``Nat) e

def getNatRelVarsM' (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Nat := do
  match vars with
  | [] =>
    let e ← elabTermEnsuringType t (mkConst ``Nat)
    getNatM e
  | (n, val) :: tail =>
    withLetDecl n (mkConst ``Nat) (toExpr val)
      fun _ => getNatRelVarsM' tail t

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

def getBoolM (e: Expr) : TermElabM Bool := do
  let e ← instantiateMVars e
  Term.synthesizeSyntheticMVarsNoPostponing
  if ← isDefEq e (mkConst ``Bool.false)
    then return false
  else
    if ← isDefEq e (mkConst ``Bool.true)
    then
      return true
    else
      throwError s!"Expression {← ppExpr e} is not a boolean"

def getBoolRelVarsM' (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Bool := do
  match vars with
  | [] =>
    let e ← elabTermEnsuringType t (mkConst ``Bool)
    getBoolM e
  | (n, val) :: tail =>
    withLetDecl n (mkConst ``Nat) (toExpr val)
      fun _ => getBoolRelVarsM' tail t

def getBoolRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Bool := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``Bool)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Bool (mkConst ``Bool) e

namespace ImpLang

-- variables with name
abbrev ImpLangM :=
  StateT  (Std.HashMap Name Nat) TermElabM

def getVar (name: Name) : ImpLangM Nat := do
  let m ← get
  return m.get! name

def setVar (name : Name) (value : Nat) :
  ImpLangM Unit := do
  modify (fun m => m.insert name value)

def getNatInCtxM (stx: Syntax.Term) : ImpLangM Nat := do
  let m ← get
  getNatRelVarsM m.toList stx

def getBoolInCtxM (stx: Syntax.Term) : ImpLangM Bool := do
  let m ← get
  getBoolRelVarsM m.toList stx


declare_syntax_cat imp_statement

syntax imp_block := "{" (imp_statement)? "}"

syntax imp_block : imp_statement

syntax imp_statement imp_statement : imp_statement

syntax ident ":=" term ";" : imp_statement

syntax "if" ppSpace "(" term ")" ppSpace imp_block "else" imp_block : imp_statement

syntax "while" "(" term ")" ppSpace imp_block : imp_statement

partial def runStatementM :
  TSyntax `imp_statement → ImpLangM Unit
| `(imp_statement| {}) => return
| `(imp_statement| {$s}) => do
    runStatementM s
| `(imp_statement| $s₁ $s₂) => do
  runStatementM s₁
  runStatementM s₂
| `(imp_statement| $name:ident := $val ;) => do
  let value ← getNatInCtxM val
  let n := name.getId
  setVar n value
| `(imp_statement| if ($p) $t else $e) => do
  let c ← getBoolInCtxM p
  if c
    then runBlockM t
    else runBlockM e
| w@`(imp_statement| while ($p) $b) => do
  let c ← getBoolInCtxM p
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

elab "#run_stat" s:imp_statement "go" : command  =>
  Command.liftTermElabM do
  let (_, m) ← runStatementM s |>.run {}
  logInfo m!"Final variable state: {m.toList}"


#run_stat
  n := 3; m := 4 + 5;
  if (n ≤ 4) {n := (5 + 3 + (2 * 7));} else {n := 2; m := 7;}
  go

#run_stat
  n := 10; sum := 0;
  i := 1;
  while (i ≤ n) {sum := sum + i; i := i + 1;} go

#run_stat
  n := 5;
  i := 2;
  check := 0;
  while (i ≤ n) {
    if (i ∣ n) {
      check := 1;
    } else {}
    i := i + 1;
  } go

end ImpLang
