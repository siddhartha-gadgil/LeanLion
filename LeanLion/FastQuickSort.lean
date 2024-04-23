import Mathlib
#check Array.eraseIdx

variable {α : Type}[LinearOrder α][Inhabited α]

partial def quickSort (arr : Array α) : Array α :=
  if arr.size <= 1 then arr
  else
    let pivot := arr.get! (arr.size / 2)
    let left := (arr.eraseIdx (arr.size / 2)).filter (fun x => x < pivot)
    let right := (arr.eraseIdx (arr.size / 2)).filter (fun x => x >= pivot)
    (quickSort left).push pivot |>.append (quickSort right)

partial def quickSortTask (arr : Array α)(depth : Nat) : Task (Array α) :=
  match depth with
  | 0 => Task.pure (quickSort arr)
  | n + 1 =>
    let pivot := arr.get! (arr.size / 2)
    let left := (arr.eraseIdx (arr.size / 2)).filter (fun x => x < pivot)
    let right := (arr.eraseIdx (arr.size / 2)).filter (fun x => x >= pivot)
    let leftTask := quickSortTask left n
    let rightTask := quickSortTask right n
    Task.bind (rightTask) (fun right =>
      leftTask.map fun left => (left.push pivot).append right)

partial def quickSortAsync (arr : Array α)(depth : Nat) : Array α :=
  (quickSortTask arr depth).get
