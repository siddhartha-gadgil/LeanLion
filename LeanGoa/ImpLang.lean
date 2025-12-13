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
| `(arith_exp| ($e)) => getIntM e
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
  return .assignment name.getId value
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
  | `(imp_block| {$s}) => getStatementM s
  | _ => throwUnsupportedSyntax

elab "bool%" b:bool_exp ";" : term => do
  let bVal ← getBoolM b |>.run' {}
  return toExpr bVal

#eval bool% (!T) && F;

#eval (!true) && false

#eval 3 + 4

#eval bool% 3 ≤ 2 ;

elab "imp%" s:imp_statement : term  => do
  let stat ← getStatementM s |>.run' {}
  return toExpr stat

#eval imp% n := 3; m := 4;
  if (2 ≤ 3) {} else {n := 2;}
