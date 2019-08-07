
Semantics of Programming Languages
==================================

This directory contains Agda proofs and a literate agda programme
designed as a basic course for the sematics of programming. Included
are basical operational and denotational semantic approaches.

The terms which prove termination at a value, double as runable
evaluation functions!

Structure
---------

* **Topic 0:** Some basic functional programming in a dependently typed language: **Preliminaries.pdf**

* **Topic 1:** Operational semantics for simple arithmetic expressions.

The examples given in the slides are contained in the file: **OperationalSemantics.agda**

* **Topic 2:** Induction

A limited number of examples from the slides are present in the file: **Induction.agda**

Some of the consistency proofs are given in **Consistency.agda**. 

There is a proof that (∀ E → Σ[ n ∈ ℕ ] E ⟶⋆ num n) in **SmallStepEval.agda**.  It makes use of transfinite induction rather than strong mathematical induction. Induction is performed over the size of proofs.

* **Topic 3:** A (first-order) functional programming language.

Not yet completed: PCF would be a possible choice for implementation.

* **Topic 4:** The While programming language

The While programming language and progress proof along with a proof of partial correctness is in the file: **While.agda**

The consistency proofs are in the file **WhileConsistency.agda**

* **Topic 5:** Handling Exceptions

Not yet completed

* **Topic 6:** Functions as data

Not yet completed


