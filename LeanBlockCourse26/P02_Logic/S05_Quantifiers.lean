/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-
# Quantifiers in Lean
=====================

This module introduces Lean's quantifiers:

- The **universal quantifier** (`∀`) appears naturally as function arguments.
- The **existential quantifier** (`∃`) asserts that some witness exists,
  and we can also express unique existence.
- The **order of quantifiers** is significant.
- We also introduce tactics for handling quantifiers:
  - `choose` to extract witness functions from existential hypotheses,
  - `use` to supply a witness for an existential goal,
  - `ext` for function (and set) extensionality.
-/

/-
## Universal Quantification

We have already seen universal quantification (`∀`) as arguments to functions.
We can now make them explicit and use them in nested proofs.
-/

-- Here `(P : Prop)` is stated as an argument as we have done so far ...
example (P : Prop) : P → P := by
  intro p -- Note that here we do *not* need to `intro P` ...
  exact p

-- ... which also has this term mode proof.
example (P : Prop) : P → P :=
  fun p => p -- ... and neither do we here

-- But internally there are no arguments and a separate output type,
-- everything is just one large type. This is also why in Lean everything
-- just uses `def` instead of distinguishing between defining variables /
-- constants and methods / functions. Note that just `Prop → ...` is valid,
-- but it leaves the actual proposition unnamed, so here we need `P : Prop`.
example : (P : Prop) → P → P := by
  intro P p -- Note that here we need to `intro P` ...
  exact p

example : (P : Prop) → P → P :=
  fun P p => p -- ... as we do here ...

-- But there is a third way of expressing the same type.
example : ∀ (P : Prop), P → P := by
  intro P p -- ... and here ...
  exact p

example : ∀ (P : Prop), P → P :=
  fun P p => p -- ... and here

/-
So there are three different kinds of syntax with two being a "convenience
layer" on top of the core type notation:

(i)   Type notation `(P : Prop) → P → P` (needs an extra `intro`)
(ii)  Functional notation `(P : Prop) : P → P` (does not need extra `intro`)
(iii) Quantified / mathematical notation `∀ (P : Prop), P → P` (needs an extra `intro`)
-/

/-
## Existential Quantifier and Unique Existence

The existential quantifier (`∃`) asserts the existence of a witness.
We also show how to extract such a witness using the `choose` tactic,
and how to supply one with the `use` tactic. `choose` is used around
800 times in mathlib and `use` around 2,500 times.
-/

-- To produce a witness of existence we can use the `use` tactic ...
theorem use_example : ∃ n, n = 2 := by
  use 2

-- ... but we can also explicitly pass both the element to use
-- and a proof of the fact that it satisfies the required property
example : ∃ n, n = 2 := by
  exact ⟨2, rfl⟩

#check Exists -- `use` tactic just wraps `Exists.intro`

#print use_example

example (m : ℕ) (h : m = 2) : ∃ n, n = m := by
  use 2
  exact h.symm

-- From unique existence (`∃!`) we can deduce existence (`∃`)
example : ∀ (X : Type) (P : X → Prop), (∃! (x : X), P x) → ∃ (x : X), P x := by
  intro X P
  intro h   -- `∃! x, P x`
  obtain ⟨x, satisfies_property, is_unique⟩ := h
  use x

example : ∀ (X : Type) (P : X → Prop), (∃! (x : X), P x) → ∃ (x : X), P x := by
  intro X P
  intro h   -- `∃! x, P x`
  obtain ⟨x, satisfies_property, is_unique⟩ := h
  exact ⟨x, satisfies_property⟩

example : ∀ (X : Type) (P : X → Prop), (∃! (x : X), P x) → ∃ (x : X), P x := by
  intro X P ⟨x, satisfies_property, is_unique⟩
  exact ⟨x, satisfies_property⟩

example : ∀ (X : Type) (P : X → Prop), (∃! (x : X), P x) → ∃ (x : X), P x :=
  fun _ _ ⟨x, satisfies_property, _⟩ => ⟨x, satisfies_property⟩

-- This is `Classical.axiomOfChoice` in Lean (Init.Classical), also `Classical.skolem.mp`
-- You can "extract" a function from a statement with an ∀∃ statement with `choose`
theorem choose_function (X : Type) (P : X → X → Prop) (h : ∀ x : X, ∃ y : X, P x y) :
    ∃ (f : X → X), ∀ x : X, P x (f x) := by
  choose f hf using h
  use f

#print choose_function -- uses `Classical.choose`

/-
## Function Extensionality

Two functions are equal if they return the same output for every input.
The `ext` tactic proves function extensionality, reducing a goal `f = g`
to proving `f x = g x` for arbitrary `x`. It is used around 11,000 times in mathlib.
-/

-- This is `funext` in Lean (Init.Core); `funext_iff` (Init.Ext) provides the biconditional
theorem func_ext (X Y : Type) (f g : X → Y) (h : ∀ x : X, f x = g x) : f = g := by
  ext x
  exact h x

#print func_ext

/-
## Exercise Block B01
-/

/-
For some arbitrary given type `α`, the type `p : α → Prop` models if a statement
holds for a specific instance of `α`, so for example `α` could be `ℕ` and
`Prop` the statement "a given natural number is even", so `p 0 = True`,
`p 1 = False`, ...

The curly brackets in `{α : Type}` make it implicit, so an invocation of the
theorem does not need to explicitly pass `α`. In order not to need to define
it for every exercise, we define it once globally through `variable {α : Type}`.
-/

variable {α : Type} (p q : α → Prop)

-- Exercise 1.1

-- We can grind through this ourselfs ...
example : (∀ x : α, p x ∧ q x) ↔ ((∀ x : α, p x) ∧ (∀ x : α, q x)) := by
  constructor
  · intro h
    constructor
    · intro x
      obtain ⟨px, qx⟩ := h x
      exact px
    · intro x
      obtain ⟨px, qx⟩ := h x
      exact qx
  · intro ⟨h₁, h₂⟩
    intro x
    have px := h₁ x
    have qx := h₂ x
    exact ⟨px, qx⟩

-- ... or have lean do it for us using the `grind` tactic ...
example : (∀ x : α, p x ∧ q x) ↔ ((∀ x : α, p x) ∧ (∀ x : α, q x)) := by
  grind

-- ... though the term mode proof is also quite compact.
example : (∀ x : α, p x ∧ q x) ↔ ((∀ x : α, p x) ∧ (∀ x : α, q x)) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

-- Exercise 1.2
example : ((∀ x : α, p x) ∨ (∀ x : α, q x)) → (∀ x : α, p x ∨ q x) := by
  intro h x
  obtain px | qx := h
  · left; exact px x
  · right; exact qx x

-- Exercise 1.3
example : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x) := by
  intro ⟨x, px, qx⟩
  constructor
  all_goals use x

-- Exercise 1.4
-- Hint: use the `choose` tactic
example (R : α → α → Prop) (h : ∀ x, ∃ y, R x y) :
    ∃ f : α → α, ∀ x, R x (f x) := by
  choose f hf using h
  use f

-- Exercise 1.5 (Master)
-- Note that this introduces the (cartesian) product of two types `α × β`
example {β} (r : β → Prop)
    (h₁ : ∃ x, p x) (h₂ : ∃ y, r y) : ∃ z : α × β, p z.1 ∧ r z.2 := by
  obtain ⟨x, px⟩ := h₁
  obtain ⟨y, qy⟩ := h₂
  use ⟨x, y⟩

-- Exercise 1.6 (Master)
example (α : Type) (p q : α → Prop) :
    (∃ x : α, p x ∨ q x) ↔ ((∃ x : α, p x) ∨ (∃ x : α, q x)) := by
  constructor
  · intro h
    obtain ⟨x, px | qx⟩ := h
    · left; use x
    · right; use x
  · intro h
    obtain ⟨x, px⟩ | ⟨x, qx⟩ := h
    · use x; left; exact px
    · use x; right; exact qx
