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
#check List.mem_filter -- ∀ {α : Type u_1} {x : α} {p : α → Bool} {as : List α}, x ∈ List.filter p as ↔ x ∈ as ∧ p x = true
#check List.length_filter_le -- ∀ {α : Type u_1} (p : α → Bool) (l : List α), List.length (List.filter p l) ≤ List.length l
