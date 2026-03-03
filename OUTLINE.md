---
title: Outline
nav_order: 2
---

# Course Outline

The course outline is still subject to change, but will roughly be as follows.

---

## P01_Introduction

Why formalize maths? The tech stack: how to properly organize a formalization project.

| | |
|---|---|
| **Slides** | [P01_Introduction.pdf](lecture-slides/P01_Introduction.pdf) |

| Section | Topic |
|---------|-------|
| S04_NumberTheoryExample | Infinitely many primes — a taste of Lean |
| S04_TopologyExample | Composition of continuous functions |
| S05_ProgrammingLanguage | Lean as a programming language |

---

## P02_Logic

Foundations of logic in Lean: what is a type and what does being classical vs. intuitionistic mean?

| Section | Topic | Exercises |
|---------|-------|-----------|
| S01_Fundamentals | `rfl`, `assumption`, `exact`, `intro`, `rw` | 2 blocks (8 exercises) |
| S02_Reasoning | `apply`, `have`, `suffices`; graph of implications | 2 blocks |
| S03_Connectives | `constructor`, `obtain`, `rcases`, `rintro`; `∧`, `∨`, `↔` | — |
| S04_Negation | `contradiction`, `exfalso`, `by_contra`, `by_cases`, `push_neg` | 2 blocks |
| S05_Quantifiers | `use`, `choose`, `ext`; `tauto`, `grind` | 1 block |

---

## P03_SetTheory

Set theory in Lean: why you should rarely do set theory in Lean.

| Section | Topic | Exercises |
|---------|-------|-----------|
| S01_SubsetsComplements | Subset relations, set equality, complements | 2 blocks |
| S02_IntersectionsUnions | `∩`, `∪`, commutativity, associativity, De Morgan | 2 blocks |
| S03_SetFamily | `⋂₀`, `⋃₀`, families of sets | 2 blocks (core + challenge) |

---

## P04_TypeTheory

Dependent type theory: where do the axioms live?

| Section | Topic | Exercises |
|---------|-------|-----------|
| S01_DependentTypes | Types as objects, universes, implicit arguments | 1 block |
| S02_InductiveType | Defining inductive types, pattern matching, recursion | 1 block |
| S03_StructuresTypeClasses | Structures, type classes, instances | 1 block |
| S04_PropositionsProofs | Curry-Howard correspondence, axioms | 1 block |

---

## P05_NaturalNumbers

Natural numbers in Lean: why inductive types are so powerful.

| Section | Topic | Exercises |
|---------|-------|-----------|
| S01_Definition | `MyNat`, `zero_ne_succ` | 1 block |
| S02_Addition | `zero_add`, `succ_add`, `add_comm`, `add_assoc` | 3 blocks |
| S03_Multiplication | `mul_zero`, `mul_succ`, distributivity, `mul_assoc` | 3 blocks |
| S04_Power | `pow_zero`, `pow_succ`, `pow_add`, `mul_pow`, `pow_pow` | 1 block |
| S05_AdvancedAddition | Cancellation laws, zero properties | 1 block |
| S06_Inequalities | `le_refl`, `le_trans`, `le_antisymm`, `le_total`; state FLT | 2 blocks |
| S07_AdvancedMultiplications | `mul_le_mul_right`, `mul_left_cancel` | 2 blocks |
| S08_MoreTactics | `simp`, `decide`, `calc` | 3 blocks |

---

## P06_InfinitePrimes

Your first real proof in Lean.

| Section | Topic |
|---------|-------|
| S01_TFAE | Five equivalent formulations |
| S02_Euclid | Euclidean proof via factorial + 1 |
| S03_Folklore | Mersenne numbers, finite fields |
| S04_Furstenberg | Topological proof via arithmetic progressions |
| S05_Goldbach | Fermat numbers, pairwise coprimality |

---

## P07_Mantel

Graph theory and combinatorics in Lean.

| Section | Topic |
|---------|-------|
| S01_HandshakingLemma | Degree sums and edge counting |
| S02_AMGM | Mantel's theorem via AM-GM |
| S03_CauchyInequality | Mantel's theorem via Cauchy-Schwarz |

---

## Examination

Final exam and distribution of formalization projects for Master-level students.
