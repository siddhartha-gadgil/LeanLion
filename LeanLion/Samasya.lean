import Mathlib

/-!
# Invitation to Lean

__Lean__ is an __open-source programming language__ and __proof assistant__ that enables correct, maintainable, and formally verified code

We introduce various aspects of Lean.

* Use as a calculator.
* Some definitions.
* First theorems.
* A non-trivial theorem: `∃ k : ℕ, n * (n + 1) = 2 * k`.
* Some comments on types, propositions, proofs.
-/

#eval 2 + 2 -- 4

#eval (2 : ℕ) + 2 -- 4

#eval "Hello, Lean!" ++ " How are you?"

def square (n : ℕ) : ℕ := n * n

#eval square 3 -- 9

def cube : ℕ → ℕ := fun n ↦ n * n * n

def sum_of_squares  : ℕ → ℕ → ℕ :=
    fun m n ↦ square m +
        square n

theorem one_plus_one_eq_two : 1 + 1 = 2 := by
  rfl

example : 3 ≤ 6 := by
  decide

theorem n_times_n_plus_one_is_even (n : ℕ) :
        ∃ k : ℕ, n * (n + 1) = 2 * k := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        let ⟨k', hk'⟩ := ih
        use k' + (n + 1)
        grind
