import Lean
import Mathlib
open Lean Meta Elab Tactic

/-!
# Meta-programming for Tactics

* **Metaprogramming* is writing funtions and programs that *work with* programs or their components.
  - We can generate, analyse or modify code representing programs, terms, commands, tactis etc.
* In principle this can be done by manipulating the text source code, but this is hard and brittle.
* Instead, we work with *internal representations* of code.
* In Lean, this is at two levels: `Syntax` and `Expr`.
  - `Syntax` is the surface syntax of Lean code.
  - `Expr` is the internal representation of Lean code in its foundations.
-/
