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


def getNatRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Nat := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Nat (mkConst ``Nat) e


elab "get_nat_rel_n%" t:term : term => do
  let n ← getNatRelVarsM [(`n, 3)] t
  return toExpr n

#eval get_nat_rel_n% (3 * 5 + n)

def getBoolRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM Bool := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``Bool)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Bool (mkConst ``Bool) e

def getStrRelVarsM (vars: List (Name × Nat))
  (t: Syntax.Term) : TermElabM String := do
  let stx ← exprRelVars vars t
  let e ← elabTermEnsuringType stx (mkConst ``String)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr String (mkConst ``String) e

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

syntax imp_block := "{" sepBy(imp_statement, ";", ";", allowTrailingSep) "}"

syntax imp_program := sepBy(imp_statement, ";", ";", allowTrailingSep)

syntax imp_block : imp_statement

syntax ident ":=" term : imp_statement

syntax "if" ppSpace "(" term ")" ppSpace imp_block "else" imp_block : imp_statement

syntax "while" "(" term ")" ppSpace imp_block : imp_statement

syntax "print" term  : imp_statement

partial def runStatementM :
  TSyntax `imp_statement → ImpLangM Unit
| `(imp_statement| {$s;*}) => do
    let stmts := s.getElems
    for stmt in stmts do
      runStatementM stmt
| `(imp_statement| $name:ident := $val) => do
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
| stat@`(imp_statement| print $s) => do
  let m ← get
  let str ← getStrRelVarsM m.toList s
  logInfoAt stat str
| _ => throwUnsupportedSyntax
where runBlockM (bs : TSyntax ``imp_block): ImpLangM Unit :=
  match bs with
  | `(imp_block| {}) => return
  | `(imp_block| {$s;*}) =>
    let stmts := s.getElems
    for stmt in stmts do
      runStatementM stmt
  | _ => throwUnsupportedSyntax

def runProgramM (pgm: TSyntax ``imp_program) : ImpLangM Unit := do
  match pgm with
  | `(imp_program| $s;*) =>
    let stmts := s.getElems
    for stmt in stmts do
      runStatementM stmt
  | _ => throwUnsupportedSyntax

elab "##run_imp" ss:imp_program r:"return" : command  =>
  Command.liftTermElabM do
  let (_, m) ← runProgramM ss |>.run {}
  logInfoAt r m!"Final variable state: {m.toList}"


##run_imp
  n := 3; m := 4 + 5;
  if (n ≤ 4) {n := (5 + 3 + (2 * 7));} else {n := 2; m := 7}
  return

##run_imp
  n := 10; sum := 0;
  i := 1;
  while (i ≤ n) {sum := sum + i; i := i + 1} return

##run_imp
  n := 59;
  i := 2;
  is_prime := 1;
  while (i < n && is_prime = 1) {
    if (i ∣ n) {
      is_prime := 0
    } else {};
    i := i + 1
  };
  if (is_prime = 1) {
    print s!"{n} is prime"
  } else {
    print s!"{n} is not prime; divisor: {i - 1}"
  }
  return

end ImpLang
