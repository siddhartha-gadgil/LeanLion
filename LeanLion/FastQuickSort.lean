import Mathlib

open Std.Internal.IO Async
-- example (n: Nat)(h : Nat.Prime n) : n + 1 ≤ 30 := by slim_check
-- example (n: Nat)(h : Nat.Prime n) : n % 2 = 1 := by slim_check
-- example (n: Nat)(h : Nat.Prime n) : n + 1 ≤ 300 :=
--   by slim_check (config := {maxSize := 1000, numInst := 1000})


variable {α : Type}[LinearOrder α][Inhabited α]

partial def quickSortArr (arr : Array α) : Array α :=
  if arr.size <= 1 then arr
  else
    let pivot := arr[arr.size / 2]!
    let left := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x < pivot)
    let right := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x >= pivot)
    (quickSortArr left).push pivot |>.append (quickSortArr right)

-- #check concurrently

partial def quickSortTask (arr : Array α)(depth : Nat) : Task (Array α) :=
  match depth with
  | 0 => Task.spawn fun _ => (quickSortArr arr)
  | n + 1 =>
    let pivot := arr[arr.size / 2]!
    let left := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x < pivot)
    let right := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x >= pivot)
    let leftTask := quickSortTask left n
    let rightTask := quickSortTask right n
    Task.bind (rightTask) (fun right =>
      leftTask.map fun left => (left.push pivot).append right)

partial def quickSortConc (arr : Array α)(depth : Nat) : Array α :=
  (quickSortTask arr depth).get

partial def quickSortAsync (arr : Array α)(depth : Nat) : Async (Array α) :=
  match depth with
  | 0 => return quickSortArr arr
  | n + 1 => do
    let pivot := arr[arr.size / 2]!
    let left := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x < pivot)
    let right := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x >= pivot)
    let (leftSorted, rightSorted) ←
      concurrently (quickSortAsync left n) (quickSortAsync right n)
    return (leftSorted.push pivot).append rightSorted

-- #check Async.toIO
