---
title: Tactics
nav_order: 5
---

# Tactic Reference

Tactics are commands used inside `by` blocks to construct proofs step by step. The tables below list every tactic used in this course, grouped by where it is first introduced. For detailed documentation, see the [Lean Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/).

## S01_Fundamentals (P02_Logic)

| Tactic | Effect |
|--------|--------|
| `rfl` | Close a goal of the form `a = a` (definitional equality). |
| `assumption` | Close the goal with a matching hypothesis from the context. |
| `exact e` | Close the goal with the term `e`. |
| `exact?` | Search for a closing term and suggest it. |
| `intro h` | Assume the antecedent of `→` or `∀` as hypothesis `h`. |
| `rw [h]` | Rewrite the goal using equality or iff `h`; `← h` for reverse. |
| `rw [h] at k` | Rewrite hypothesis `k` instead of the goal. |
| `nth_rw n [h]` | Rewrite only the n-th occurrence. |
| `symm` | Swap sides of an equality or iff. |

## S02_Reasoning (P02_Logic)

| Tactic | Effect |
|--------|--------|
| `apply e` | Backward reasoning: reduce the goal using `e`. |
| `revert h` | Move `h` back into the goal (inverse of `intro`). |
| `have h : T := ...` | Introduce a new fact `h` of type `T`. |
| `suffices h : T` | Like `have`, but prove the main goal first. |

## S03_Connectives (P02_Logic)

| Tactic | Effect |
|--------|--------|
| `constructor` | Split a goal `P ∧ Q` or `P ↔ Q` into two subgoals. |
| `left` / `right` | Choose which side of `P ∨ Q` to prove. |
| `obtain ⟨a, b⟩ := h` | Destructure `h : P ∧ Q`, `P ∨ Q`, or `∃ x, P x`. |
| `rcases h with ...` | Recursive pattern matching on hypotheses. |
| `rintro ⟨a, b⟩` | Combine `intro` and `rcases`. |
| `h.1` / `h.2` | Project left or right component of `h : P ∧ Q`. |
| `h.mp` / `h.mpr` | Forward or backward direction of `h : P ↔ Q`. |

## S04_Negation (P02_Logic)

| Tactic | Effect |
|--------|--------|
| `contradiction` | Close the goal from conflicting hypotheses. |
| `exfalso` | Change the goal to `False`. |
| `by_contra h` | Assume `¬ goal` as `h` and derive `False` (classical). |
| `by_cases h : P` | Split into `P` and `¬P` branches (classical). |
| `push_neg` | Push negation inward through connectives and quantifiers. |
| `trivial` | Try `rfl`, `assumption`, `contradiction`, and similar. |

## S05_Quantifiers (P02_Logic)

| Tactic | Effect |
|--------|--------|
| `use a` | Supply witness `a` for an existential goal. |
| `choose f hf using h` | Extract a witness function from `∀ x, ∃ y, P x y`. |
| `ext x` | Prove `f = g` by showing `f x = g x` for arbitrary `x`. |

## S05_Quantifiers — Automation (P02_Logic)

| Tactic | Effect |
|--------|--------|
| `tauto` | Close propositional tautologies in one step. |
| `grind` | SMT-style solver handling quantifiers and arithmetic. |

## P05_NaturalNumbers

| Tactic | Effect |
|--------|--------|
| `induction n with ...` | Structural induction on `n`. |
| `simp [lemmas]` | Simplifier: repeatedly apply rewrite rules. |
| `decide` | Prove decidable propositions by computation. |
| `calc` | Chain equalities or inequalities through intermediate steps. |

## P06_InfinitePrimes / P07_Mantel

| Tactic | Effect |
|--------|--------|
| `linarith` | Prove goals from linear arithmetic over ordered fields. |
| `ring` | Prove polynomial equalities in commutative rings. |
| `omega` | Decision procedure for linear integer/natural arithmetic. |
| `norm_num` | Evaluate closed numerical expressions. |

## Combinators

These modify how other tactics are applied:

| Combinator | Effect |
|------------|--------|
| `all_goals t` | Run tactic `t` on every open goal. |
| `repeat t` | Apply `t` until it fails. |
| `try t` | Attempt `t`; succeed silently if it fails. |
| `first \| t₁ \| t₂` | Try `t₁`, fall back to `t₂`. |
| `<;> t` | Apply `t` to all goals produced by the previous tactic. |
