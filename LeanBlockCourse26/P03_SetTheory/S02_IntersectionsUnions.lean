/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NthRewrite
import LeanBlockCourse26.P03_SetTheory.S01_SubsetsComplements

variable {α : Type*}

/-
# Sets: Intersections and Unions
=====================

## Intersection Basics

The intersection of two sets `S` and `T`, denoted `S ∩ T`, is defined as the
set of elements `x` for which `x ∈ S ∧ x ∈ T`.
-/

example (S T : Set α) : S ∩ T = {x | x ∈ S ∧ x ∈ T} := rfl

lemma mem_inter_iff (x : α) (S T : Set α) : x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by
  rfl

#check Set.mem_inter_iff

lemma mem_of_mem_inter_right {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := by
  rw [mem_inter_iff] at h -- optional because we are just rewriting with equal definition
  exact h.2

example {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := h.2

lemma inter_subset_left (S T : Set α) : S ∩ T ⊆ S := by
  rw [subset_def]
  intro x h
  rw [mem_inter_iff] at h
  exact h.left

example (S T : Set α) : S ∩ T ⊆ S := 
  fun _ h => h.left

lemma mem_inter {x : α} {S T : Set α} (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T := by
  rw [mem_inter_iff]
  constructor
  all_goals assumption

example {x : α} {S T : Set α} (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T :=  ⟨h₁, h₂⟩

/-
## Exercise Block B01
-/

namespace P03S02B02

variable (S T : Set α) 

-- Exercise 1.1
lemma inter_subset_swap : S ∩ T ⊆ T ∩ S := by
  intro x ⟨xs, xt⟩
  constructor
  · exact xt
  · exact xs

example : S ∩ T ⊆ T ∩ S := by
  intro _ ⟨xs, xt⟩
  exact ⟨xt, xs⟩

example : S ∩ T ⊆ T ∩ S :=
  fun _ ⟨xs, xt⟩ => ⟨xt, xs⟩

example : S ∩ T ⊆ T ∩ S := 
  fun _ x => ⟨x.2, x.1⟩

-- Exercise 1.2
lemma subset_inter (R : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T := by
  intro x xr
  rw [mem_inter_iff]
  exact ⟨h₁ xr, h₂ xr⟩ 

example (R : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T := 
  fun _ xr => ⟨h₁ xr, h₂ xr⟩ 

-- Exercise 1.3
lemma inter_comm : S ∩ T = T ∩ S := by
  ext x
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

example : S ∩ T = T ∩ S := by
  ext x
  repeat rw [mem_inter_iff]
  exact And.comm

example : S ∩ T = T ∩ S := by
  apply Set.ext
  intro x
  exact And.comm

example : S ∩ T = T ∩ S :=
  Set.ext (fun _ => And.comm)

-- Exercise 1.4
lemma inter_assoc (R : Set α) : (R ∩ S) ∩ T = R ∩ (S ∩ T) := by
  ext x
  repeat rw [mem_inter_iff]
  exact and_assoc

example (R : Set α) : (R ∩ S) ∩ T = R ∩ (S ∩ T) :=
  Set.ext (fun _ => and_assoc)

-- Note the inconsistent default bracketing ...
example (R : Set α) :    R ∩ S ∩ T = (R ∩ S) ∩ T   := rfl
example (P Q R : Prop) : P ∧ Q ∧ R ↔ P ∧ (Q ∧ R)   := by rfl

end P03S02B02

/-
## Union Basics

The union of two sets `S` and `T`, denoted `S ∪ T`, is defined as the
set of elements `x` for which `x ∈ S ∨ x ∈ T`.
-/

lemma mem_union (x : α) (S T : Set α) : x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T := by rfl

/-
## Exercise Block B02
-/

namespace P03S02B02

variable (S T : Set α) 

-- Exercise 2.1
lemma subset_union_right : T ⊆ S ∪ T := by
  sorry

-- Exercise 2.2
lemma union_subset (R : Set α) (h₁ : R ⊆ T) (h₂ : S ⊆ T) : R ∪ S ⊆ T := by
  sorry

-- Exercise 2.3
lemma union_subset_swap : S ∪ T ⊆ T ∪ S := by
  sorry

-- Exercise 2.4
lemma union_comm : S ∪ T = T ∪ S := by
  sorry

-- Exercise 2.5 (Master)
lemma compl_inter : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ := by
  sorry

-- Exercise 2.6 (Master)
lemma compl_union : (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
  sorry

-- Exercise 2.7 (Master)
lemma union_assoc (R : Set α) : (R ∪ S) ∪ T = R ∪ (S ∪ T) := by
  sorry

-- Exercise 2.8 (Master)
lemma inter_distrib_left (R : Set α) : R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T) := by
  sorry

-- Exercise 2.9 (Master)
example (R : Set α) (h₁ : R ∪ T ⊆ S ∪ T) (h₂ : R ∩ T ⊆ S ∩ T) : R ⊆ S := by
  sorry

-- Exercise 2.10 (Master)
example (R : Set α) (h₁ : R ∪ T ⊆ S ∪ T) (h₂ : R ∩ T ⊆ S ∩ T) : R ⊆ S := by
  sorry

end P03S02B02
