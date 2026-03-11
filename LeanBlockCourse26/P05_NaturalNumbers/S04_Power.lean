/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse26.P05_NaturalNumbers.S03_Multiplication
import ProofGolf

/-
# Exponentiation
=====================
-/

namespace MyNat

-- Define exponentiation recursively
def pow (n m : MyNat) : MyNat :=
  match m with
  | zero => 1
  | succ k => pow n k * n

-- Register the `^` notation via the `Pow` typeclass
instance instPow : Pow MyNat MyNat where pow := pow

-- The two definitional lemmas for exponentiation
theorem pow_zero (n : MyNat) : n ^ (0 : MyNat) = 1 := rfl

theorem pow_succ (n m : MyNat) : n ^ (succ m) = n ^ m * n := rfl


/-
## Exercise Block B01
-/

-- Exercise 1.1
theorem zero_pow_zero : (0 : MyNat) ^ (0 : MyNat) = 1 := rfl

-- Exercise 1.2
-- Rewrite with `pow_succ` to get `0 ^ m * 0`, then apply `mul_zero`.
theorem zero_pow_succ (m : MyNat) : (0 : MyNat) ^ (succ m) = 0 := by
  rw [pow_succ, mul_zero]

-- Exercise 1.3
-- Unfold `1` as `succ 0`, rewrite with `pow_succ` and `pow_zero`, then
-- apply `one_mul`.
theorem pow_one (n : MyNat) : n ^ (1 : MyNat) = n := by
  rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]

-- Exercise 1.4
-- By induction on `n`. The base case follows from `pow_zero`. For the
-- inductive step, rewrite with `pow_succ` and apply the inductive
-- hypothesis and `mul_one`.
theorem one_pow (n : MyNat) : (1 : MyNat) ^ n = 1 := by
  induction n with
  | zero => rw [← zero_eq_zero, pow_zero]
  | succ m ih => rw [pow_succ, ih, mul_one]

-- Exercise 1.5
-- Unfold `2` as `succ 1`, rewrite with `pow_succ` and `pow_one`.
theorem pow_two (n : MyNat) : n ^ (2 : MyNat) = n * n := by
  rw [two_eq_succ_one, pow_succ, pow_one]

-- Exercise 1.6
-- By induction on `k`. The base case follows from `add_zero`, `pow_zero`,
-- and `mul_one`. For the inductive step, rewrite with `add_succ` and
-- `pow_succ` on both sides, apply the inductive hypothesis, and
-- rearrange with `mul_assoc`.
theorem pow_add (n m k : MyNat) : n ^ (m + k) = n ^ m * n ^ k := by
  induction k with
  | zero => rw [← zero_eq_zero, add_zero, pow_zero, mul_one]
  | succ k' ih => rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]

-- Exercise 1.7
-- By induction on `k`. The base case follows from `pow_zero` and `mul_one`.
-- For the inductive step, rewrite all three `pow_succ` terms, apply the
-- inductive hypothesis, and rearrange with `mul_assoc` and `mul_comm`.
theorem mul_pow (n m k : MyNat) : (n * m) ^ k = n ^ k * m ^ k := by
  induction k with
  | zero => rw [← zero_eq_zero, pow_zero, pow_zero, pow_zero, mul_one]
  | succ k' ih =>
    rw [pow_succ, pow_succ, pow_succ, ih]
    repeat rw [mul_assoc]
    rw [mul_comm n (_ * m), mul_assoc, mul_comm m n]

-- Exercise 1.8
-- By induction on `k`. The base case follows from `mul_zero` and `pow_zero`.
-- For the inductive step, rewrite with `pow_succ`, apply the inductive
-- hypothesis, then use `mul_succ` and `pow_add`.
theorem pow_pow (n m k : MyNat) : (n ^ m) ^ k = n ^ (m * k) := by
  induction k with
  | zero => rw [← zero_eq_zero, mul_zero, pow_zero, pow_zero]
  | succ k' ih => rw [pow_succ, ih, mul_succ, pow_add]

-- Exercise 1.9 (Master)
-- Expand all squares with `pow_two`, distribute with `mul_add` and `add_mul`,
-- rewrite `2 * n * m` with `two_mul` and `add_mul`, and rearrange with
-- `add_assoc`, `add_right_comm`, and `mul_comm`.
theorem add_sq (n m : MyNat) :
    (n + m) ^ (2 : MyNat) = n ^ (2 : MyNat) + m ^ (2 : MyNat) + 2 * n * m := by
  rw [pow_two, pow_two, pow_two]
  rw [add_right_comm]
  rw [mul_add, add_mul, add_mul]
  rw [two_mul, add_mul]
  rw [mul_comm m n]
  rw [← add_assoc, ← add_assoc]

/-
## Bonus (Master): Prove Fermat's Last Theorem

Fermat's Last Theorem states that if `x, y, z > 0` and
`m ≥ 3` then `x^m + y^m ≠ z^m`. Since we have not yet
introduced inequalities, you will need to restate this
using disequalities (`≠`).

The shortest solution known to humans would translate into
many millions of lines of Lean code. Kevin Buzzard is working
on translating the proof by Taylor and Wiles into Lean, although
this task will take many years.
-/

theorem fermats_last_theorem (x y z m : MyNat)
    (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hm2 : m ≠ 2)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x^m + y^m ≠ z^m := by
  sorry

/-
# Tactic Addendum: `simp`
=====================

Many of the proofs above were tedious — long `rw` chains rearranging terms
via associativity and commutativity, with no deep mathematical insight.
The following rearrangement of 8 variables illustrates the problem. `#golf`
your solution and try to make the *tactic proof* as compact as possible.
-/

example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry

--  310 chars using `add_comm`, `add_assoc`, and `add_left_comm`
#golf theorem leonie (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  rw[add_comm (g + e)]
  rw[add_comm g]
  rw[add_comm h]
  rw[add_comm (d + f)]
  nth_rewrite 2 [add_assoc]
  rw[add_comm h]
  nth_rewrite 2 [add_assoc]
  rw[add_assoc]
  nth_rewrite 2 [add_comm]
  rw[add_assoc]
  rw[add_comm (e + g)]
  nth_rewrite 2 [add_assoc]
  rw [add_assoc]
  rw[add_assoc]
  rw[add_comm (f + h)]
  rw[add_assoc]
  nth_rewrite 6 [add_left_comm]
  repeat rw [← add_assoc]

-- 324 characters using `add_comm` and `add_assoc`
#golf theorem theottm (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  rw [add_comm _ b, add_comm _ e, add_comm h _, ←add_assoc, ←add_assoc (d+f) _,
      add_comm (d+f) _, add_assoc _ b, add_assoc _ _ (b + (e + g)), add_comm h _,
      add_assoc, add_assoc a c _ , add_assoc]
  repeat rw [← add_assoc f _ _]
  rw [add_comm f b, add_assoc _ f, ← add_assoc f _ _, add_comm f e]
  repeat rw [← add_assoc d _ _]
  rw [add_comm d _]
  repeat rw [← add_assoc c _ _]
  rw [add_comm c _]
  repeat rw [←add_assoc]

-- 648 chars using `add_comm`, `add_assoc`, and `add_right_comm`
#golf theorem speacky081 (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  calc (d + f) + (h + (a + c)) + (g + e + b)
    _ = (d + f) + (h + a + c) + (g + e + b) := by rw [(add_assoc h a c).symm]
    _ = d + f + (h + a) + c + (g + e + b) := by rw [(add_assoc (d + f) (h + a) c).symm]
    _ = d + f + h + a + c + (g + e + b) := by rw [(add_assoc (d + f) h a).symm]
    _ = d + f + h + a + c + (g + e) + b := by rw [(add_assoc (d + f + h + a + c) (g + e) b).symm]
    _ = d + f + h + a + c + g + e + b := by rw [(add_assoc (d + f + h + a + c) g e).symm]
    _ = d + f + a + h + c + g + e + b := by rw [add_right_comm (d + f) h a]
    _ = d + a + f + h + c + g + e + b := by rw [add_right_comm d f a]
    _ = a + d + f + h + c + g + e + b := by rw [add_comm d a]
    _ = a + d + f + h + c + g + b + e := by rw [add_right_comm _ _ _]
    _ = a + b + d + f + h + c + g + e := by repeat rw [add_right_comm _ _ b]
    _ = a + b + c + d + f + h + g + e := by repeat rw [add_right_comm _ _ c]
    _ = a + b + c + d + e + f + h + g := by repeat rw [add_right_comm _ _ e]
    _ = a + b + c + d + e + f + g + h := by rw [add_right_comm _ _ _]

-- 324 characters using `add_comm`, `add_assoc`, and `add_right_comm`
#golf theorem artulean  (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  rw [add_assoc, add_assoc h (a + c) (g + e + b), ← add_assoc,
  add_assoc a c (g + e + b), ← add_assoc, ← add_assoc, add_assoc g e b,
  ← add_assoc, ← add_assoc, add_right_comm (d + f), add_right_comm (d + f + a),
  add_right_comm (d + f + a + c), add_right_comm (d + f + a + c + g),
  add_right_comm (d + f + a + c + g + e), add_right_comm (d + f + a + c),
  add_right_comm (d + f + a + c + e), add_right_comm d, add_right_comm (d + a),
  add_right_comm (d + a + c), add_right_comm (d + a + c + e),
  add_right_comm (d + a + c), add_comm d a, add_right_comm a,
  add_right_comm (a + c), add_right_comm (a)]

-- 244 chars using  `add_comm` and `add_assoc`
#golf theorem towalt (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  rw[add_assoc a b, add_comm b, ← add_assoc a c, add_comm _ d, add_assoc d _ e, add_assoc _ b e,
  add_comm b e, add_assoc d _ f, add_comm (a + c + (e + b)), ← add_assoc d f (a + c + (e + b)),
  add_assoc _ _ g, add_assoc _ _ g, add_comm _ g, add_assoc g e b, add_assoc _ _ h, add_comm _ h,
  ← add_assoc h (a+c), add_assoc]

-- 230 characters using `add_comm`, `add_assoc`, and `add_right_comm`
#golf theorem anliki (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  rw[add_comm h]
  rw[add_assoc g e b , add_comm g, add_comm e]
  rw[add_assoc, add_comm]
  rw[← add_assoc, ← add_assoc, ← add_assoc]
  rw[add_right_comm _ h b,add_right_comm _ c b]
  rw[add_right_comm _ g d, add_right_comm _ g f, add_right_comm _ e d]
  repeat rw[add_right_comm _ h _]

-- 316 characters using `add_comm` and `add_assoc`
#golf example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  repeat rw [← add_assoc]
  nth_rw 6 [add_comm]; repeat rw [← add_assoc]
  nth_rw 3 [add_comm]; repeat rw [← add_assoc]
  nth_rw 5 [add_comm]; repeat rw [← add_assoc]
  nth_rw 2 [add_comm]; repeat rw [← add_assoc]
  nth_rw 4 [add_comm]; repeat rw [← add_assoc]
  nth_rw 2 [add_comm]; repeat rw [← add_assoc]
  nth_rw 1 [add_comm]; repeat rw [← add_assoc]
  nth_rw 1 [add_comm]; repeat rw [← add_assoc]

-- 259 characters using `add_comm` and `add_assoc`
-- Already lays out a clear principle along which a term should be canonized
#golf example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  repeat rw [add_assoc]
  repeat (rw [add_comm d]; repeat rw [add_assoc])
  repeat (rw [add_comm f]; repeat rw [add_assoc])
  repeat (rw [add_comm h]; repeat rw [add_assoc])
  repeat (rw [add_comm c]; repeat rw [add_assoc])
  repeat (rw [add_comm g]; repeat rw [add_assoc])
  repeat (rw [add_comm e]; repeat rw [add_assoc])

-- 172 chars using `add_comm`, `add_assoc`, and `add_left_comm`
#golf example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  repeat rw [add_assoc]
  repeat rw [add_left_comm _ g]
  repeat rw [add_left_comm _ f]
  repeat rw [add_left_comm _ d]
  repeat rw [add_left_comm _ e]
  rw [add_comm _ h]
  repeat rw [add_left_comm _ h]
  rw [add_comm _ c]


/-
## The `simp` tactic

`simp` repeatedly applies lemmas left-to-right at every subterm until nothing
changes — think of it as "`rw` in a loop." It will rewrite every lemma
tagged with `@[simp]` and every lemma you supply in brackets.

`simp only [...]` restricts `simp` to only the lemmas you supply.
-/


-- simp will use tagged lemmas and anything supplied in the brackets
#golf theorem example_simp_comm_left_comm (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp [add_comm, add_left_comm]

#print example_simp_comm_left_comm

-- you can limit simp to only lemmas that you are supplying
example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_comm, add_left_comm]

-- notably this fails!
-- example (a b c d e f g h : MyNat) :
--     (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
--   simp [add_comm, add_assoc]

/-
## Tagging lemmas with `@[simp]`

Lemmas can be tagged with `@[simp]` (at definition) or `attribute [simp]`
(after the fact) so that bare `simp` uses them automatically. Which lemmas
to tag is a design choice — following mathlib conventions:

**Identity and normalization lemmas** are always safe to apply:
-/

attribute [simp] add_zero zero_add mul_zero zero_mul
attribute [simp] mul_one one_mul
attribute [simp] pow_zero pow_one one_pow

/-
**Structural lemmas** like `pow_succ`, `mul_add`, `add_mul`, `pow_add`,
`two_mul` are intentionally NOT tagged: expanding or distributing is not
always desired, so you supply them explicitly when needed.
-/

/-
**AC triples**: for any associative, commutative operation, the triple
`{op_assoc, op_comm, op_left_comm}` lets `simp` rearrange any expression
into a canonical form. `op_left_comm` is the key: it lets `simp` swap past
a specific variable rather than blindly flipping two.

In mathlib, the AC triples are NOT globally tagged. A commutativity lemma
like `add_comm` interacts with every other simp lemma in the default set
(40,000+): `simp` might reorder the arguments of `f(a + b)` to `f(b + a)`,
triggering another simp lemma about `f`, which produces new sums that get
reordered again. The Batteries `simpComm` linter enforces this policy.
Instead, mathlib uses `simp only [add_comm, add_assoc, add_left_comm]`
explicitly, or dedicated tactics like `ring` and `ac_rfl`.

For our small `MyNat` development, this is not a concern — we tag them:
-/

attribute [simp] add_assoc add_comm add_left_comm
attribute [simp] mul_assoc mul_comm mul_left_comm

-- Now bare `simp` suffices:
example (a b c d e f g h : MyNat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp

/-
Note that a theorem can also be directly tagged when stating!

```
@[simp] theorem succ_eq_add_one (n : Nat) : succ n = n + 1 :=
  rfl
```
-/

/-
## Exercise Block B02
-/

-- Exercise 2.1 
-- Prove once using only `rw` and `exact` and then once using `simp`
example (a b c : MyNat) : (a + b) + (b + c) = (b + b) + (a + c) := by
  rw [add_assoc, ← add_assoc b, add_comm, add_comm a, ← add_assoc]

-- We can pass the relevant theorems explicitly to `simp` ...
example (a b c : MyNat) : (a + b) + (b + c) = (b + b) + (a + c) := by
  simp only [add_comm, add_left_comm]

-- ... but note that we already `@[simp]` tagged these before
example (a b c : MyNat) : (a + b) + (b + c) = (b + b) + (a + c) := by
  simp

-- Exercise 2.2
-- Prove however you like and `#golf`, shortest tactic mode proof wins

-- 19 characters
#golf example (a b : MyNat) : a * (1 + b) = a + a * b := by
  rw [mul_add, mul_one]

-- 13 characters
#golf example (a b : MyNat) : a * (1 + b) = a + a * b := by
  simp [mul_add]


-- Or we cheat for 4 characters by tagging `mul_add` with `simp` ...
attribute [simp] mul_add
example (a b : MyNat) : a * (1 + b) = a + a * b := by
  simp

-- ... or we cheat even more by aliasing `s` for `simp` for 1 character
syntax "s" : tactic
macro_rules
  | `(tactic| s) => `(tactic| simp)
example (a b : MyNat) : a * (1 + b) = a + a * b := by
  s


end MyNat
