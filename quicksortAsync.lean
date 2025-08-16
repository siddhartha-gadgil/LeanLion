import LeanLion.FastQuickSort
import LeanLion.QuickSort
open Std.Internal.IO.Async Async

def main (args: List String) : IO Unit := do
  let n := args.head? |>.bind String.toNat? |>.getD 1000000
  let m := args[1]? |>.bind String.toNat? |>.getD (n * 10)
  IO.eprintln s!"Generating random list of size {n} with max value {m}"
  let start ← IO.monoMsNow
  let mut l := #[]
  for _ in [0:n] do
    l := l.push (← IO.rand 0 m)
  IO.eprintln s!"Done: got {l.size}"
  let done ← IO.monoMsNow
  IO.eprintln s!"Time for generating: {done - start}ms"
  IO.eprintln s!"Sorting random list of size {n} with max value {m}"
  let start ← IO.monoMsNow
  let sorted := quickSortConc l 6
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
  IO.eprintln "Sorting with Async"
  let start ← IO.monoMsNow
  let sortedTask ←  quickSortAsync l 6 |>.toIO
  let sorted ← sortedTask.block
  IO.eprintln s!"Done: got {sorted.size} elements."
  let done ← IO.monoMsNow
  IO.eprintln s!"Time for sorting: {done - start}ms"
  for i in [0:10] do
    IO.eprintln s!"* {sorted[i]!}"
--   IO.eprintln "Generating again, this time with Async"
--   let start ← IO.monoMsNow
--   let base : Array Nat := Array.replicate n 0
--   let arrAsync : Async (Array (AsyncTask Nat)) :=
--     concurrentlyAll (base.map (fun _ => async <| IO.rand 0 m))
--   let arrTask ← arrAsync.toIO
--   let arrT ← arrTask.block
--   let arr ← arrT.mapM (fun x => x.block)
--   IO.eprintln s!"Done: got {arr.size} elements."
--   let done ← IO.monoMsNow
--   IO.eprintln s!"Time for generating: {done - start}ms"

-- #check async
