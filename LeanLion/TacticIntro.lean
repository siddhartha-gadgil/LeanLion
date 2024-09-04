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

/-!
Macros can help us avoid remembering the exact syntax.
-/

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
* A term of type `α` can be turned into a term of type `BlahM α` by using `pure α: s ↦ (α, s)`, i.e., ignoring and fixing the state
* `return x` is roughly a synonym for `pure x`.
* In general, given a type `s` (the state), we have a state monad `State s α`

## The Monad `TacticM`

* To first approximation, `TacticM` is a state monad with state `Tactic.State`.
* Hence, a term of type `TacticM Unit` is a function that:
  - Given a `Tactic.State` (the tactic state)
  - Returns a value of type `Unit`: the unique value of type `Unit`.
  - And a new `Tactic.State`.
* Thus, a tactis is a function that takes a tactic state and returns a new tactic state.

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

/-!
### Next example: `use_till`

We write a tactic to plug in various natural numbers into `use` until the tactic followed by another succeeds.
-/
example : ∃ n: Nat, n * n = 64 := by
  use 8


-- example : ∃ n: Nat, n * n = 64 := by
--   use_till 10 then rfl

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


-- example (x y : Nat) (h : x ≤ y) : x ≤ y :=
--   by
--     match_le
--     assumption

/-!
We now write the tactic `rw_le` that rewrites.
-/

-- example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
--   by
--     rw_le h₂
--     assumption

-- example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ y :=
--   by
--     rw_le h₁

/-!
## Correctly checking tactics

In a previous example, we just checked whether the remaining goals were empty to check if a tactic succeeded. This is incorrect as we may have other goals, so we incorrectly think the tactic failed.

We now do this (and a bit more) correctly. We define a function that runs a tactic and returns the number of remaining goals (for that tactic only).
-/
#check Elab.runTactic

-- example : 2 ≤ 4 := by
--   cases 0
--   check_tactic decide
