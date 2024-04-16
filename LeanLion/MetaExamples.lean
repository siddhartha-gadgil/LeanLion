import Lean
open Lean Meta Elab Command Syntax
/-!
## Meta-programming in Lean

Lean has a powerful meta-programming framework that allows you to write programs that generate Lean code.
-/

/-!
The first layer of meta-programming is `Core`, where we can access and modify the environment.
-/
#check findDocString? -- Lean.findDocString? (env : Environment) (declName : Name) (includeBuiltin : Bool := true) : IO (Option String)

#check Environment.constants  -- Lean.Environment.constants (self : Environment) : ConstMap

#print ConstMap -- SMap Name ConstantInfo

#check SMap.map₁ -- Lean.SMap.map₁.{u, v} {α : Type u} {β : Type v} [inst✝ : BEq α] [inst✝¹ : Hashable α] (self : SMap α β) : HashMap α β

/-!
## Extracting identifiers in a proof/definition

We can work directly with `Expr` objects to extract identifiers. However, this gives a lot of information that we might not need, indeed we would like suppressed.

Alternatively, we can use the `PrettyPrinter` module to delaborate the `Expr` object into a `Term` (i.e. `Syntax.term`) object, which shows relevant information.
-/

#check Environment.find? -- Lean.Environment.find? (env : Environment) (n : Name) : Option ConstantInfo

#check ConstantInfo.defnInfo -- Lean.ConstantInfo.defnInfo (val : DefinitionVal) : ConstantInfo

#check PrettyPrinter.delab -- Lean.PrettyPrinter.delab (e : Expr) (optionsPerPos : PrettyPrinter.Delaborator.OptionsPerPos := ∅) : MetaM Term

/-!
## New Syntax: Macros and Elaborators

A macro creates new syntax and transforms it into previously defined syntax. As an example we introduce python-like list comprehension syntax,
for example `[x * x  for x in [1, 2, 3]]`.

In Lean, the above should be translated to `List.map (fun x => x * x) [1, 2, 3]`.
-/
#check List.map -- List.map.{u, v} {α : Type u} {β : Type v} (f : α → β) (a✝ : List α) : List β

/-!
Suppose we want a more sophisticated variant, where the same syntax can handle both `List` and `Array` comprehensions, using `List.map` and `Array.map` respectively.

For this we need more than just a macro, we need an elaborator. An elaborator is a function that takes a syntax object and returns an expression object.
-/

/-!
Our next example is a macro, but a more complex one. Suppose we want to handle nested list comprehensions, for example `[x * x for x in l for l in [[1, 5, 2], [3, 4, 5]]]`. This has to be resolved to:

`List.bind [[1, 5, 2], [3, 4, 5]] (fun l => List.map (fun x => x * x) l)`.

In general, the innermost `for` is resolved to a `List.map`, and the all the outer `for`s are resolved to a `List.bind`.
-/
#check List.bind -- List.bind.{u, v} {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β
