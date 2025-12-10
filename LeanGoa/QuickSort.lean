import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
## Quicksort Algorithm (Pivot from Head)

Quicksort is a divide-and-conquer sorting algorithm known for its efficiency. It works by recursively partitioning the list around a chosen element (pivot) and then sorting the sub-lists.

Our implementation of quicksort for lists follows the following steps:

* If the list is empty, return the empty list.
* Otherwise, let `pivot` be the first element (`head`) of the list.
* Let `smaller` be the list of elements smaller (`≤`) than `pivot` and `larger` be the list of elements larger (`>`) than `pivot`.
* Recursively sort `smaller` and `larger` lists and concatenate them with `pivot` in between.

We begin by defining `smaller` and `larger` lists. We define them as abbreviations so that they are automatically unfolded by Lean.
-/


/-!
We define `smaller` and `larger` using `List.filter`. We need some theorems relating to filtering.
-/
variable {α : Type}[LinearOrder α]

@[simp, grind]
def smaller (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x ≤  pivot)

@[simp, grind]
def larger (pivot : α) (l : List α) : List α :=
  l.filter (fun x => pivot < x)

def quickSort : List α → List α
  | _ => sorry


@[simp, grind]
theorem quickSort_nil : quickSort ([] : List α) = [] := by
  sorry

@[simp, grind]
theorem quickSort_cons (pivot : α) (l : List α) :
    quickSort (pivot :: l) = (quickSort (smaller pivot l)) ++
    pivot :: (quickSort (larger pivot l)) := by
  sorry

@[grind]
theorem mem_iff_below_or_above_pivot (pivot : α)
  (l : List α)(x : α) :
    x ∈ l ↔ x ∈ smaller pivot l ∨ x ∈ larger pivot l := by
  sorry

theorem mem_iff_mem_quickSort (l: List α)(x : α) :
    x ∈ l ↔ x ∈ quickSort l := by
  sorry

inductive Sorted : List α → Prop
  | nil : Sorted []
  | singleton (x : α) : Sorted [x]
  | step (x y : α) (l : List α) (hxy: x ≤ y)
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l)

@[grind]
theorem head_le_of_sorted  (a: α) (l : List α) :
  Sorted (a :: l) → ∀ x ∈ l, a ≤ x := by
  sorry

theorem cons_sorted (l : List α) :  Sorted l → (a : α) →
  (∀ y ∈ l, a ≤ y) → Sorted (a :: l)  := by
  sorry

theorem sorted_sandwitch (l₁ : List α) (h₁ : Sorted l₁)
    (l₂ : List α) (h₂ : Sorted l₂)
    (bound : α)
    (h_bound₁ : ∀ x ∈ l₁, x ≤ bound)
    (h_bound₂ : ∀ x ∈ l₂, bound ≤ x) :
    Sorted (l₁ ++ bound :: l₂) := by
  sorry

theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by
  sorry
-- Exploration commands

set_option pp.match false in
set_option pp.proofs false in
set_option pp.fieldNotation false in
#print quickSort

set_option pp.match false in
set_option pp.proofs false in
#print quickSort.match_1

#print WellFounded
#check invImage
/-
{α : Sort u} →
  {C : α → Sort v} → {r : α → α → Prop} → WellFounded r → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → C x
-/
#check WellFounded.fix

/- {α : Sort u} →
  {r : α → α → Prop} → WellFounded r → {C : α → Sort v} → (a : α) → ((x : α) → ((y : α) → r y x → C y) → C x) → C a
-/
#check WellFounded.recursion
