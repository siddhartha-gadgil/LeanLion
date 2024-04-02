import LeanAideTools
/-!
## Tactics in the background

First we see in a simple example
-/

example : 1 ≤ 2 := by sorry

/-!
We next illustrate the use of the `byy` tactic where the proof cannot be found straightaway.
-/

opaque sillyN : Nat
axiom silly : sillyN = 2

example : sillyN ≤ 3 := by sorry

/-!
We now show that stuff keeps running in the background
-/
set_option aided_by.delay 0 in
example : sillyN ≤ 7 := by sorry

/-!
We do not continue within `case` and `match` blocks. So there is an alternative way to use `byy` in the following example.
-/
example (n : Nat) : n/2 ≤ n := by sorry

/-!
We can add a tactic as an auto-tactic
-/
#auto simp [silly]

example : sillyN ≤ 3 := by sorry
