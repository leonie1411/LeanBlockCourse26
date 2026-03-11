/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Tauto
import LeanBlockCourse26.P05_NaturalNumbers.S06_Inequalities

/-
# Advanced Multiplication
=====================
-/

namespace MyNat

/-
## Exercise Block B01
-/

-- Exercise 1.1
theorem mul_le_mul_right {n m : MyNat} (k : MyNat) (h : n ≤ m) : n * k ≤ m * k := by
  sorry

-- Exercise 1.2
theorem one_le_of_ne_zero {n : MyNat} (hn : n ≠ 0) : 1 ≤ n := by
  sorry

-- Exercise 1.3
theorem mul_left_ne_zero {n m : MyNat} (h : n * m ≠ 0) : m ≠ 0 := by
  sorry

-- Exercise 1.4
theorem le_mul_right {n m : MyNat} (h : n * m ≠ 0) : n ≤ n * m := by
  sorry

-- Exercise 1.5 (Master)
theorem mul_right_eq_one {n m : MyNat} (h : n * m = 1) : n = 1 := by
  sorry

-- Exercise 1.6 (Master)
theorem mul_ne_zero {n m : MyNat} (hn : n ≠ 0) (hm : m ≠ 0) : n * m ≠ 0 := by
  sorry

-- Exercise 1.7 (Master)
theorem mul_eq_zero {n m : MyNat} (h : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry

/-
## A challenging induction: `induction` while `generalizing`
-/

-- Exercise 2.1 (Master)
theorem mul_left_cancel {n m k : MyNat}
    (hn : n ≠ 0) (h : n * m = n * k) : m = k := by
  sorry

end MyNat
