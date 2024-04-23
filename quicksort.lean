import LeanLion.FastQuickSort

def main (args: List String) : IO Unit := do
  let n := args.head? |>.bind String.toNat? |>.getD 100000
  let m := args[1]? |>.bind String.toNat? |>.getD (n * 10)

  let l ←  List.range n |>.mapM fun _ => IO.rand 0 m
  let l := l.toArray
  IO.println s!"Sorting random list of size {n} with max value {m}"
  let start ← IO.monoMsNow
  let sorted := quickSortAsync l 3
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sorted.size} elements. First 10: {sorted.toList.take 10}"
  return ()
