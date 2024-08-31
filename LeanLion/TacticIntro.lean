import Lean
import Mathlib
open Lean Meta Elab Tactic

/-!
# Meta-programming for Tactics

* **Metaprogramming* is writing funtions and programs that *work with* programs or their components.
  - We can generate, analyse or modify code representing programs, terms, commands, tactis etc.
* In principle this can be done by manipulating the text source code, but this is hard and brittle.
* Instead, we work with *internal representations* of code.
* In Lean, this is at two levels: `Syntax` and `Expr`.
  - `Syntax` is a tree structure representing the surface syntax of Lean code.
  - `Expr` is the internal representation of a lean *term* in its foundations.

## Interpreting/Compilation of Lean code

* Lean code is processed in two steps:
  * **Parsing** - the text is converted into a `Syntax` tree. This could represent a term, a tactic, a command, an identifier etc.
  * **Elaboration** - the `Syntax` tree for a *term* is converted into an `Expr` tree. This is the internal representation in the foundations of Lean. We also elaborate *commands*.

## Metaprogramming with Syntax

* The syntax of Lean is extensible.
* We can create new syntax, and even new syntax categories.
* A `macro` is a function that takes a `Syntax` object and returns a `Syntax` object.
* Macros are applied recursively to the syntax tree. The result should be previously valid syntax.
-/

example : 2 ≤ 4 := by
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

example : 2 ≤ 4 := by
  repeat (first|apply Nat.le_refl|apply Nat.le_step)

macro "nat_le" : tactic => do
  `(tactic|repeat (first|apply Nat.le_refl|apply Nat.le_step))

example : 20 ≤ 30 := by nat_le

macro "repeat_apply" t₁:term "then" t₂:term : tactic => do
  `(tactic|repeat (first|apply $t₁ | apply $t₂))

example : 20 ≤ 40 := by
  repeat_apply Nat.le_refl then Nat.le_step

theorem eg₁ : 2 ≤ 4 := by
  repeat_apply Nat.succ_le_succ then Nat.zero_le

#print eg₁

/-!
## What are tactics?

* An expression of the form `by $tacticSeq` is just syntax for a term.
* If the tactic sequence is valid and of the correct type, it is elaborated into a term of the specified type.
-/

elab "evil" : tactic => do
  setGoals []

-- example : 3 ≤ 5 := by
--   evil

#check sorryAx

elab "scowl" s:str : tactic => do
  logInfo m!"Message: {s}"
  let goalType ← getMainTarget
  let sorryExp ← mkAppM ``sorryAx #[goalType, mkConst ``false]
  closeMainGoal sorryExp

example : 3 ≤ 5 := by
  scowl "This is a bad proof"

elab "use_till" n:num "then" tac:tacticSeq : tactic => withMainContext do
  let n := n.getNat
  let s ← saveState
  for j in [0:n] do
    let s ← saveState
    try do
      let jLit := Syntax.mkNumLit <| toString j
      evalTactic <| ← `(tactic|use $jLit:term)
      if (← getGoals).isEmpty then
        return ()
      evalTactic tac
      unless (← getGoals).isEmpty do
        throwError "tactic failed"
      return ()
    catch _ =>
      restoreState s
  restoreState s
  throwError "tactic failed"

example : ∃ n: Nat, n * n = 64 := by
  use_till 10 then rfl

#check Nat.le

def matchLe (e: Expr) : MetaM (Option (Expr × Expr)) := do
  let nat := mkConst ``Nat
  let a ← mkFreshExprMVar nat
  let b ← mkFreshExprMVar nat
  let e' ←  mkAppM ``Nat.le #[a, b]
  if ← isDefEq e e' then
    return some (a, b)
  else
    return none

elab "match_le" : tactic => withMainContext do
  let e ← getMainTarget
  let e' ← matchLe e
  match e' with
  | some (a, b) => logInfo m!"Inequality: {a} ≤ {b}"
  | none => logWarning "Not a ≤ b for natural numbers"
  return ()

example (x y : Nat) (h : x ≤ y) : x ≤ y :=
  by
    match_le
    assumption

elab "rw_le" t:term : tactic => withMainContext do
  let e ← Tactic.elabTerm t (some (mkConst ``Nat))
  let p₁? ← matchLe <| ← inferType e
  let p₂? ← matchLe (← getMainTarget)
  match p₁?, p₂? with
  | some (a₁, b₁), some (a₂, b₂) => do
    let left_match ← isDefEq a₁ a₂
    let right_match ← isDefEq b₁ b₂
    if left_match && right_match then
      closeMainGoal e
    else
    if left_match then
      let ineq ← mkFreshExprMVar <| ← mkAppM ``Nat.le #[b₁, b₂]
      let trans ← mkAppM ``Nat.le_trans #[e, ineq]
      let goal ← getMainGoal
      goal.assign trans
      setGoals [ineq.mvarId!]
    else
    if right_match then
      let ineq ← mkFreshExprMVar <| ← mkAppM ``Nat.le #[a₂, a₁]
      let trans ← mkAppM ``Nat.le_trans #[ineq, e]
      let goal ← getMainGoal
      goal.assign trans
      setGoals [ineq.mvarId!]
    else
      logError "Endpoints do not match on either side"
      throwAbortTactic
  | _, _ =>
    logError m!"Could not rewrite as not inequalities {e} {← getMainTarget}"
    throwAbortTactic

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₂
    assumption

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ y :=
  by
    rw_le h₁
