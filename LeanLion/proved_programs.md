---
marp: true
theme: default
---
# Programs with Proofs & Meta-programs in Lean

---

## Lean as a Programming Language

Lean is a _dependently typed_, _functional_ programming language:

* Lean's type system is rich enough to express arbitrary mathematical theorems;
* Lean has a fast runtime, good enough that Lean is *self-hosting*;
* A powerful tactic system allows for *interactive theorem proving*;
* The meta-programming system is powerful and convenient.
* Proving, programming and meta-programming are all seamlessly integrated.

---

## Lean as a functional language

* Functions in Lean are **terms**.
* Thus, they are *first-class citizens*: they can be passed as arguments, returned from functions, and stored in data structures.
* A name can be used in only one definition, so *variables* are immutable (in the core language).
* The only form of looping is *recursion*.
* No explicit flow control exists: commands are executed in order and modify the environment.
* All these facilitate reasoning about programs.
* Various optimizations are applied to generate compiled code to avoid a performance penalty.

---

## Lean as a dependently-typed language

* In Lean, types are **terms**.
* Thus, types are first-class citizens: they can be passed as arguments, returned from functions, and stored in data structures.
* Lean's type constructors are rich enough to express arbitrary mathematical theorems.
* Propositions are types, and proofs are terms of these types.
* Proofs are erased at runtime, so there is no performance penalty for proving theorems.

---

## SATurn: A SAT Solver-Prover in Lean

* The Boolean satisfiability problem (SAT) is the problem of determining if a given collection of Boolean formulas is satisfiable.
* [SATurn](https://github.com/siddhartha-gadgil/Saturn) is an implementation in Lean of the DPLL algorithm for SAT solving.
* Given a SAT problem, SATurn returns one of:
  * A proof that the problem is not satisfiable: a *resolution tree* is returned, and it is proved that such trees are proofs of unsatisfiability.
  * A satisfying assignment to the variables and proof that they are correct.
* Remarkably, SATurn ran correctly as soon as it compiled.

---
 
# SATurn demo: $n$-queens etc.

---

## LeanAide: Autoformalization of Statements

Given a statement, [LeanAide](https://github.com/siddhartha-gadgil/LeanAide) generates a Lean formalization of the statement.

* We find documentation strings (in Mathlib, Std, Core) that are similar (w.r.t. OpenAI's embeddings) to the statement.
* From these, a prompt with example translations and the given statement is generated.
* GPT-4 is queried with the prompt, with (say) 10 completions sought.
* We elaborate OpenAI completions in Lean and filter out those that fail.
* We further group these by *provable equivalence*, where we try to prove equivalence using the Aesop tactic and pick the first completion in the largest group.

---

# LeanAide demo

---

## LeanAideTools: Running tactics in the background

* Often tactics like `exact?`, `aesop`, `simp`, `norm_num` can finish a goal.
* It is a nuisance to run these tactics manually every time.
* Using **meta-programming** and **concurrency** using `Task` supported by Lean, we implement a tool that runs chosen tactics in the background.

---

# LeanAideTools demo

---

# Programming example: Quicksort

---


## Meta-programming

From Wikipedia:
> Metaprogramming is a programming technique in which computer programs have the ability to treat other programs as their data. It means that a program can be designed to read, generate, analyse or transform other programs, and even modify itself while running

* A hacky way to do this is to manipulate the code as strings.
* A more principled way is to use a *meta-programming system*, which allows working with the internal representations of programs and their components.
* Principled **implies** less error-prone and easier to **understand**, **maintain**, and **extend**.

---

## Lean code: Source, Syntax, and Expressions.

* The **source** code of Lean programs, commands, and terms is strings, which are *linear sequences of characters.*
* **Parsers** convert source code into `Syntax` **trees**.
* **Elaborators** convert syntax trees into `Expr`'s: type-correct kernel **expressions** that are *terms in the foundations of the Lean language.*
* `Expr` and `Syntax` are both types, so *syntax* and _kernel expressions_ are **terms** (first-class citizens) in Lean.
* Lean uses parser-combinators: parsers can use the results of parsing parts of the input.
* The syntax is extensible: new syntax and even new *kind*s of syntax can be added.
* *Delaborators* convert `Expr`s back into syntax trees, and *pretty-printers* convert syntax trees back into source code.

---

* **Core:** Lean provides functions to inspect the environment, including declarations.
* **Macro:** We can define new syntax (and new kinds of syntax) and functions transforming the new syntax (presumably eventually to older syntax).
* **Meta:** Expressions can use meta-variables as placeholders, with expressions assigned to them later. Definitions cannot have unassigned meta-variables.
* **TermElab:** We can define new syntax, together with functions transforming the new syntax to kernel expressions.
* **Tactic:** Tactics are functions that construct an expression of a *target* type and assign it to the *goal* meta-variable. The expression may depend on other meta-variables, which then become new goals.
* The **Infoview** is also a rich source of data.

---

## Data from LeanAide

* Documentation strings.
* Premises used in proofs of results.
* Composite terms in proofs.
* Lemmas used: any proposition that is the type of some sub-expression of a proof term.
* Premises and composite terms in proofs of lemmas.
* We have about 10 million theorem-lemma pairs, where theorems include lemmas in proofs as above.

---

# Meta-programming examples