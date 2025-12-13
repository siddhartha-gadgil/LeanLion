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

variable {α : Type}[LinearOrder α]

@[grind]
def smaller (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x ≤  pivot)

@[grind]
def larger (pivot : α) (l : List α) : List α :=
  l.filter (fun x => pivot < x)

def quickSort : List α → List α
  | [] => []
  | pivot :: l =>
    have hs : (smaller pivot l).length < (pivot :: l).length := by
      grind
    have hl : (larger pivot l).length < (pivot :: l).length := by
      grind
    (quickSort (smaller pivot l)) ++ pivot :: (quickSort (larger pivot l))
termination_by l => l.length


@[simp, grind]
theorem quickSort_nil : quickSort ([] : List α) = [] := by
  simp [quickSort]

@[simp, grind]
theorem quickSort_cons (pivot : α) (l : List α) :
    quickSort (pivot :: l) = (quickSort (smaller pivot l)) ++
    pivot :: (quickSort (larger pivot l)) := by
  simp [quickSort]

@[grind]
theorem mem_iff_below_or_above_pivot (pivot : α)
  (l : List α)(x : α) :
    x ∈ l ↔ x ∈ smaller pivot l ∨ x ∈ larger pivot l := by
  apply Iff.intro
  · intro h
    if h' : x ≤ pivot then
      grind
    else
      simp only [not_le] at h'
      grind
  · grind

theorem mem_iff_mem_quickSort (l: List α)(x : α) :
    x ∈ l ↔ x ∈ quickSort l := by
  cases l with
  | nil =>
    simp
  | cons pivot l =>
    have : (smaller pivot l).length < (pivot :: l).length := by
      grind
    have : (larger pivot l).length < (pivot :: l).length := by
      grind
    have ihb := mem_iff_mem_quickSort (smaller pivot l)
    have iha := mem_iff_mem_quickSort (larger pivot l)
    grind
termination_by l.length

inductive Sorted : List α → Prop
  | nil : Sorted []
  | singleton (x : α) : Sorted [x]
  | step (x y : α) (l : List α) (hxy: x ≤ y)
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l)

@[grind]
theorem head_le_of_sorted  (a: α) (l : List α) :
  Sorted (a :: l) → ∀ x ∈ l, a ≤ x := by
  intro h
  match h with
  | Sorted.singleton .. => simp
  | Sorted.step .(a) y l hxy tail_sorted =>
    intro z hz
    simp at hz
    cases hz
    · grind
    · have ih := head_le_of_sorted y l tail_sorted
      trans y
      · assumption
      · grind

@[grind]
theorem cons_sorted (l : List α) :  Sorted l → (a : α) →
  (∀ y ∈ l, a ≤ y) → Sorted (a :: l)  := by
  intro h₁ a h₀
  match l with
  | [] =>
    apply Sorted.singleton
  | x :: l' =>
    apply Sorted.step a x
    · grind
    · assumption

theorem sorted_sandwitch (l₁ : List α) (h₁ : Sorted l₁)
    (l₂ : List α) (h₂ : Sorted l₂)
    (bound : α)
    (h_bound₁ : ∀ x ∈ l₁, x ≤ bound)
    (h_bound₂ : ∀ x ∈ l₂, bound ≤ x) :
    Sorted (l₁ ++ bound :: l₂) := by
    induction h₁ with
    | nil => grind
    | singleton x =>
      simp only [List.cons_append, List.nil_append]
      apply Sorted.step <;> grind
    | step x y l hxy tail_sorted ih =>
      simp only [List.cons_append]
      apply Sorted.step <;> grind

theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by
  cases l with
  | nil =>
    simp [quickSort_nil]
    apply Sorted.nil
  | cons pivot l =>
    rw [quickSort_cons]
    apply sorted_sandwitch
    · have : (smaller pivot l).length < (pivot :: l).length :=
        by grind
      apply quickSort_sorted (smaller pivot l)
    · have : (larger pivot l).length < (pivot :: l).length :=
        by grind
      apply quickSort_sorted (larger pivot l)
    · intro x
      rw [← mem_iff_mem_quickSort]
      grind
    · intro x
      rw [← mem_iff_mem_quickSort]
      grind [le_of_lt]
termination_by l.length

#eval quickSort [3,6,8,10,1,2,1]
