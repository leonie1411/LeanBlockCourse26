/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra

/-
# Defining the Natural Numbers
=====================

## The inductive definition of `MyNat`
-/

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

#check MyNat.noConfusion


namespace MyNat

instance myNatInhabited : Inhabited MyNat where
  default := MyNat.zero -- Would also be valid to use `MyNat.zero.succ.succ`

#eval myNatInhabited.default -- tells use our default instance of `MyNat` is `MyNat.zero`

#check 0 -- Note that this is still `Nat` and `(0 : MyNat)` coercion fails

-- Establish a coercion method from `Nat` to `MyNat` so we can use numerals
def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero => MyNat.zero
  | Nat.succ b => MyNat.succ (ofNat b)

#eval ofNat 0
#eval ofNat 1

instance instOfNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n

#check (0 : MyNat) -- manually coerces `0` into MyNat.zero

def foo (n : MyNat) : MyNat := n

#check foo 1 -- coercion turns `1` into `1 : MyNat`

-- Some basic theorems about successors in MyNat
theorem one_eq_succ_zero : 1 = succ 0 := rfl
theorem two_eq_succ_one : 2 = succ 1 := rfl
theorem three_eq_succ_two : 3 = succ 2 := rfl
theorem four_eq_succ_three : 4 = succ 3 := rfl
theorem five_eq_succ_four : 5 = succ 4 := rfl
theorem zero_eq_zero : 0 = zero := rfl

/-
## Exercise Block B01
-/

-- Exercise 1.1
example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero]

example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]

example : 2 = succ (succ 0) := rfl

-- Exercise 1.2
theorem eq_succ_of_ne_zero {n : MyNat} (h : n ≠ 0) :
    ∃ m : MyNat, n = succ m := by
  -- Hint: try `induction n` or just `cases n`
  cases' n with k
  · contradiction
  · use k

-- Exercise 1.3 (Master)
-- Turn Exercise 1.2 into a verified algorithm
def eq_succ_of_ne_zero_algorithm {n : MyNat} (h : n ≠ 0) :
    { m : MyNat // n = succ m } := by
  cases n with
  | zero => contradiction
  | succ k => use k 

end MyNat
