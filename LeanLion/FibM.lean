import Batteries

open Batteries

structure State (s α: Type) where
  run : s → α × s

namespace State
def get : State s s := ⟨fun s => (s, s)⟩
def update (f: s → s) : State s Unit := ⟨fun s => ((), f s)⟩

def run'(x: State s α) (s: s) : α := (x.run s).1
end State

instance : Monad (State s) where
  pure x := ⟨fun s => (x, s)⟩
  bind x f := ⟨fun s =>
    let (a, s') := x.run s
    (f a).run s'⟩
open State



abbrev FibM := State (HashMap Nat Nat)


def fibM (n: Nat) : FibM Nat := do
  let s ← get
  match s.find? n with
  | some y => return y
  | none =>
    match n with
    | 0 => return 1
    | 1 =>  return 1
    | k + 2 => do
      let f₁ ← fibM k
      let f₂ ← fibM (k + 1)
      let sum := f₁ + f₂
      update fun m => m.insert n sum
      return sum

#eval fibM 72 |>.run' ∅
#check State.run'
