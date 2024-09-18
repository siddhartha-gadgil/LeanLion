import Lean
import Mathlib
open Lean Meta Elab Tactic
set_option linter.unusedTactic false

elab "#stx" "[" t:term "]" : command => do
  logInfo m!"Syntax: {t};\n{repr t}"

elab "#expr" "[" t:term "]" : command =>
  Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let t ← instantiateMVars t
  logInfo m!"Expression: {t}:\n{repr t}"
  let t ← reduce t
  let t ← instantiateMVars t
  logInfo m!"Reduced: {t}:\n{repr t}"

/-!
# Meta-programming for Tactics

* **Metaprogramming** is writing functions and programs that *work with* programs or their components.
  - We can *generate*, *analyse* or *modify* code representing *programs*, *terms*, *commands*, *tactics* etc.
* In principle this can be done by manipulating the text source code, but this is hard and brittle.
* Instead, we work with *internal representations* of code.
* In Lean, this is at two levels: `Syntax` and `Expr`.
  - `Syntax` is a tree structure representing the surface syntax of Lean code.
  - `Expr` is the internal representation of a lean *term* in its foundations.

## Interpreting/Compilation of Lean code

* Lean code is processed in two steps:
  * **Parsing** - the text is converted into a `Syntax` tree. This could represent a term, a tactic, a command, an identifier etc.
  * **Elaboration** - the `Syntax` tree for a *term* is converted into an `Expr` tree. This is the internal representation in the foundations of Lean. We also elaborate *commands*.
-/
#stx [2 + 4]
#expr [(2 : Nat) + 4]
#stx [Nat → Nat]
#expr [Nat → Nat]
#expr [fun (n : Nat) ↦ n + 2]

/-!
## Metaprogramming with Syntax

* The syntax of Lean is extensible.
* We can create new syntax, and even new syntax categories.
* A `macro` is a function that takes a `Syntax` object and returns a `Syntax` object.
* Macros are applied recursively to the syntax tree. The result should be syntax that can be elaborated (without expanding with the newly written macro).
-/

def eg₁ : 2 ≤ 4 := by
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

/-!
We can avoid repeating the `apply` by using `repeat`.
-/


example : 21 ≤ 42 := by
  repeat
    (first | apply Nat.le_refl | apply Nat.le_step)
  done

/-!
Macros can help us avoid remembering the exact syntax among other things.
-/


macro "nat_le" : tactic => do
  `(tactic|repeat (first|apply Nat.le_refl|apply Nat.le_step| simp))

example : 20 ≤ 30 := by nat_le

macro "repeat_apply" t₁:term "then" t₂:term : tactic => do
  `(tactic|repeat (first|apply $t₁ | apply $t₂))

example : 3 ≤ 6 := by
  repeat_apply Nat.le_refl then Nat.le_step

example : 4 ≤ 8 := by
  repeat_apply Nat.succ_le_succ then Nat.zero_le

/-!
## What are tactics?

* An expression of the form `by $tacticSeq` is just syntax for a term.
* If the tactic sequence is valid and of the correct type, it is elaborated into a term of the specified type.
-/

#print eg₁

/-!
* In interactive mode, at each step we have a *tactic state* consisting of:
  - A list of goals, each with a target type.
  - A local context of hypotheses and definitions.
  - A set of metavariables (including the goals).
* A tactic is essentially a function that takes a tactic state and returns a new tactic state.
* More formally, a tactic is a term of type `TacticM Unit`.

## State Monads

* If `BlahM` is a *state monad* with state `Blah.State`, then a term of type `BlahM α` corresponds to:
  - given an initial state in `Blah.State`
  - return a value of type `α`
  - and a final state in `Blah.State`.
* Thus, this is essentially a function `Blah.State → α × Blah.State`.
* The monadic structure and `do` notation allow us to
  - Compose in a convenient way (with the updated state passed automatically).
  - Automatically handle the state.
* A term of type `α` can be turned into a term of type `BlahM α` by using, for `x :α`, `pure x: s ↦ (x, s)`, i.e., ignoring and fixing the state
* `return x` is roughly a synonym for `pure x`.
* In general, given a type `s` (the state), we have a state monad `State s α`

## The Monad `TacticM`

* To first approximation, `TacticM` is a state monad with state `Tactic.State`.
* Hence, a term of type `TacticM Unit` is a function that:
  - Given a `Tactic.State` (the tactic state)
  - Returns a value of type `Unit`: the unique value of type `Unit`.
  - And a new `Tactic.State`.
* Thus, a tactic is a function that takes a tactic state and returns a new tactic state.

## More on `TacticM`

* We in fact have a hierarchy of Monads, `CoreM`, `MetaM`, `TermElabM`, `TacticM`.
* So, to the next level of approximation,
  - `TacticM α = State Tactic.State (TermElabM α)`,
  - `TermElabM α = State Term.State (MetaM α)`
  - `MetaM α = State Meta.State (CoreM α)`
  - etc.
* A term in a lower monad can be lifted to a higher monad using compositions of `pure`.
* Actually all these monads are `State` monads equipped with a `ReaderT`, which means they also have a **read-only `Context`**.
* There are a few other subtleties which we can ignore for now.

## First examples: Closing without proofs
-/
elab "evil" : tactic => do
  setGoals []

-- example : 3 ≤ 5 := by
--   evil

#check sorryAx -- (α : Sort u) → optParam Bool false → α

elab "scowl" s:str : tactic => do
  let target ← getMainTarget
  let e ← mkAppM ``sorryAx #[target, mkConst ``false]
  logInfo m!"Message: {s}"
  closeMainGoal `scowl e

example : 2 ≤ 4 := by
  scowl "Do you really want me to prove this?"

/-!
### Next example: `use_till`

We write a tactic to plug in various natural numbers into `use` until the tactic followed by another succeeds.
-/
example : ∃ n: Nat, n * n = 64 := by
  use 8

elab "use_till" n:num "then" tac:tacticSeq : tactic =>
  withMainContext do
  let n := n.getNat
  let s₀ ← saveState
  for j in [0:n] do
    let s ← saveState
    try
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
  restoreState s₀
  throwError "tactic failed"

example : ∃ n: Nat, n * n = 64 := by
  use_till 10 then rfl


/-!
### Next example: `le_rw`

We now give a more substantial example. This can be done with just macros, but we will use metaprogramming to illustrate the principles.

The tactic `rw_le h` works if the goal is of the form `a ≤ b` and `h` is a proof of `c ≤ d`, with `a`, `b`, `c` and `d` all natural numbers. If `a = c` or `b = d` or both, then it rewrites the goal.

We do this in three steps:

* Recognize when an expression is of the form `a ≤ b`.
* Write a tactic that says whether the goal is of the form `a ≤ b`.
* Write a tactic that rewrites the goal if the goal is of the form `a ≤ b` and the argument is a proof of `c ≤ d` with at least one end matching.
-/
#check Nat.le

def matchLe (e: Expr) : MetaM (Option (Expr × Expr)) :=
  do
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
  let e ← Tactic.elabTerm t none
  let p₁? ← matchLe <| ← inferType e
  let p₂? ← matchLe (← getMainTarget)
  match p₁?, p₂? with
  | some (a₁, b₁), some (a₂, b₂) => do
    let left_match ← isDefEq a₁ a₂
    let right_match ← isDefEq b₁ b₂
    if left_match && right_match then
      closeMainGoal `rw_le e
    else
    if left_match then
      let newGoal ← mkFreshExprMVar <| ← mkAppM ``Nat.le #[b₁, b₂]
      let trans ← mkAppM ``Nat.le_trans #[e, newGoal]
      let goal ← getMainGoal
      goal.assign trans
      replaceMainGoal [newGoal.mvarId!]
    else
    if right_match then
      let ineq ← mkFreshExprMVar <| ← mkAppM ``Nat.le #[a₂, a₁]
      let trans ← mkAppM ``Nat.le_trans #[ineq, e]
      let goal ← getMainGoal
      goal.assign trans
      replaceMainGoal [ineq.mvarId!]
    else
      logError "Endpoints do not match on either side"
      throwAbortTactic
  | _, _ =>
    logError m!"Could not rewrite as not inequalities {e} {← getMainTarget}"
    throwAbortTactic



example (x y : Nat) (h : x ≤ y) : x ≤ y :=
  by
    match_le
    assumption

/-!
We now write the tactic `rw_le` that rewrites.
-/

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₁
    exact h₂

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₂
    exact h₁


example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ y :=
  by
    rw_le h₁

/-!
## Correctly checking tactics

In a previous example, we just checked whether the remaining goals were empty to check if a tactic succeeded. This is incorrect as we may have other goals, so we incorrectly think the tactic failed.

We now do this (and a bit more) correctly. We define a function that runs a tactic and returns the number of remaining goals (for that tactic only).
-/
#check Elab.runTactic

-- example : 2 ≤ 4 := by
--   cases 0
--   check_tactic decide
