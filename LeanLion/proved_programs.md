---
marp: true
theme: default
---


# Lean as a Programming Language

Lean is a *dependently-typed*, *functional* programming language:

* Lean's type system is rich enough to express arbitrary mathematical theorems;
* Lean has a fast runtime; good enough that Lean is *self-hosting*;
* A powerful tactic system allows for *interactive theorem proving*;
* The meta-programming system is powerful and convenient.
* Proving, programming, and meta-programming are all seamlessly integrated.

---

## Lean as a functional language

* Functions in Lean are **terms**.
* Thus, they are *first-class citizens*: they can be passed as arguments, returned from functions, and stored in data structures.
* A name can be used in only one definition: so *variables* are immutable (in the core language).
* The only form of looping is *recursion*.
* There is no explicit flow control: commands are executed in order and modify the state of the program.
* All these make programs easier to reason about.
* In generating compiled code, various optimizations are applied to avoid a performance penalty.

---

## Lean as a dependently-typed language

* In Lean, types are **terms**.
* This means that types can depend on values.
* Indeed, types are first-class citizens: they can be passed as arguments, returned from functions, and stored in data structures.
* Lean's type constructors are rich enough to express arbitrary mathematical theorems.
* Propositions are types, and proofs are terms of these types.
* Proofs are erased at runtime, so there is no performance penalty for proving theorems.

---

## Meta-progamming

From Wikipedia:
> Metaprogramming is a programming technique in which computer programs have the ability to treat other programs as their data. It means that a program can be designed to read, generate, analyse or transform other programs, and even modify itself while running

* A hacky way to do this is to simply manipulate the code as strings.
* A more principled way is to use a *meta-programming system*, which allows working with the internal representations of programs and their components.
* Principled **implies** less error-prone and easier to **understand**, **maintain**, and **extend**.

---

## Lean code: Source, Syntax and Expressions.

* The **source** code of Lean programs, commands and terms is strings: *linear sequences of characters.*
* **Parsers** convert source code into `Syntax` **trees**.
* **Elaborators** convert syntax trees into `Expr`'s: type-correct kernel **expressions** that are *terms in the foundations of the Lean language.*
* `Expr` and `Syntax` are both types, so *syntax* and *kernel expresssions* are both **terms** (first-class citizens) in Lean.
* Lean uses parser-combinators: parsers can use the results of parsing parts of the input.
* Syntax is extensible: new syntax and even new syntax *kind*s can be added.
* *Delaborators* convert `Expr`'s back into syntax trees, and *pretty-printers* convert syntax trees back into source code.