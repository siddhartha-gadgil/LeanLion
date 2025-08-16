import LeanLion.FastQuickSort
import LeanLion.QuickSort

def main (args: List String) : IO Unit := do
  let n := args.head? |>.bind String.toNat? |>.getD 1000000
  let m := args[1]? |>.bind String.toNat? |>.getD (n * 10)
  IO.eprintln s!"Generating random list of size {n} with max value {m}"
  let mut l := #[]
  for _ in [0:n] do
    l := l.push (← IO.rand 0 m)
  IO.eprintln s!"Sorting random list of size {n} with max value {m}"
  let start ← IO.monoMsNow
  let sorted := quickSortConc l 3
  IO.eprintln s!"Done: got {sorted.size} elements."
  let done ← IO.monoMsNow
  IO.eprintln s!"Time for sorting: {done - start}ms"
  for i in [0:10] do
    IO.eprintln s!"* {sorted[i]!}"
  IO.eprintln "Sorting without concurrency"
  let start ← IO.monoMsNow
  let sorted := quickSortArr l
  IO.eprintln s!"Done: got {sorted.size} elements."
  let done ← IO.monoMsNow
  IO.eprintln s!"Time for sorting: {done - start}ms"
  for i in [0:10] do
    IO.eprintln s!"* {sorted[i]!}"
  return ()
