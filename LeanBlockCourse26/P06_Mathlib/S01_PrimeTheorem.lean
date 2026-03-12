import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.TFAE

/-
## Euclid's theorem: there are infinitely many prime

How exactly is this result stated?

### [Wikipedia](https://en.wikipedia.org/wiki/Euclid%27s_theorem)

"Euclid's theorem (...) asserts that there are infinitely many prime numbers."

### Aigner and Ziegler: Proofs from THE BOOK

* "It shows that the sequence of primes does not end."
* "a finite set {p1,...,pr} cannot be the collection of all prime numbers"
* "We will show that any two Fermat numbers are relatively prime; hence there must be infinitely
   many primes.
* "The set of primes cannot be finite"
* "The function counting the number of primes that are less than or equal to a real number x is
   unboundend, and so there are infinitely many primes"
* "Our final proof goes a considerable step further and demonstrates not only that there are
   infinitely many primes, but also that the series ∑p 1/p diverges.""
-/


/-
You will now have to work with mathlib, i.e., understand its definitions and finds its results.

To do this, you should:

(I)   Look up the correct section of the area / type / structure that you are interested in
      and read the comments and basic definitions of at least the main files (`Defs.lean` and
      `Basic.lean`). Either understand the definitions or, if they are too opaque and disappear
      in formal abstraction, find the relevant equivalent definition statements to `rw` with.

(II)  Hover or cmd-click anything that is unclear or unexpected and click through in VS Code.

(III) Use `exact?` or `simp?` whenever you think you have a nuclear expression that *should*
      be in mathlib to try and find it. Often it is advisable to extract the statement into
      separate `example` for this. You can also manually search the files, guess the
      expected theorem name based on the [mathlib naming convention](https://leanprover-community.github.io/contribute/naming.html),
      use [leansearch.net](https://leansearch.net) or [Loogle](https://loogle.lean-lang.org),
      talk to people on [Is there code for X? on zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Complexity.20theory/with/578655619)
      or ask ChatGPT, Claude, ... with online research tools and maybe even a lean environment.
-/


#check Fintype

theorem infinitude_of_primes_tfae : [

    -- 1) The set of primes is infinite
    { p : ℕ | p.Prime }.Infinite,

    -- 2) The subtype of primes is infinite
    Infinite { p : ℕ // p.Prime },

    -- 3) For any finite set we can find a prime number outside of it
    ∀ (S : Finset ℕ), (∃ p ∉ S, p.Prime),

    -- 4) For any finite set *of prime numbers* we can find a prime number outside of it
    (∀ (S : Finset ℕ) (_ : ∀ s ∈ S, Nat.Prime s), (∃ p ∉ S, p.Prime)),

    -- 5) For any natural number there exists a prime strictly greater than it
    (∀ n : ℕ, (∃ p > n, p.Prime)),

    -- 6) There exists an injection from the Natural numbers into the primes
    ∃ (P : ℕ → ℕ) (h : P.Injective), (∀ k, (P k).Prime) ].TFAE := by

  tfae_have 5 → 6 := by sorry -- Theo

  tfae_have 2 → 3 := by sorry -- Arthur

  tfae_have 1 → 2 := by sorry -- Onat

  tfae_have 1 → 6 := by sorry -- Bohdan

  tfae_have 3 → 2 := by sorry -- Leonie

  tfae_have 3 → 4 := by sorry -- Alexandra

  tfae_have 5 → 4 := by sorry -- Sammy

  tfae_have 6 → 3 := by sorry -- Anna

  tfae_have 6 → 1 := by sorry -- Alexander

  tfae_have 4 → 1 := by -- Cara
   /-
   We are proving that :
      Given:
         (4) For any finite set *of prime numbers* we can find a prime number outside of it, i.e.
         `(∀ (S : Finset ℕ) (_ : ∀ s ∈ S, Nat.Prime s), (∃ p ∉ S, p.Prime))`.
      Then:
         (1) The set of primes is infinite, i.e. `{ p : ℕ | p.Prime }.Infinite`.
   -/

   -- First, we clear the unused variables to make the InfoView more readable.
   clear tfae_5_to_6 tfae_2_to_3 tfae_1_to_2 tfae_1_to_6 tfae_3_to_2
      tfae_3_to_4 tfae_5_to_4 tfae_6_to_3 tfae_6_to_1

   -- Introduce our assumption (4)
   intro h

   --- Assume by way of contradiction that the set of primes is finite.
   by_contra P_finite
   push_neg at P_finite

   -- We also define P, the set of primes, to use later in the proof.
   let P := {p | Nat.Prime p}

   -- Now, we show that all numbers in our set are prime, using the theorem `Set.mem_toFinset`
   -- See: (https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Set.mem_toFinset#doc)
   -- This is necessary, since our hypothesis is only for sets of prime numbers.
   obtain (n_in_P_n_prime : (∀ n ∈ P_finite.toFinset, Nat.Prime n)) :=
      fun _ => (@Set.Finite.mem_toFinset ℕ P _ P_finite).mp

   -- We apply our hypothesis, so we get that there exists a
   -- prime not in our finite set of primes
   have _ := h P_finite.toFinset n_in_P_n_prime

   -- Finally, we show that the opposite statement is also true, and we get a contradiction.
   -- See: https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Set.notMem_setOf_iff#doc
   -- For the description of `notMem_setOf_iff`
   obtain (_ : ¬(∃ p ∉ P_finite.toFinset, Nat.Prime p)) := by
      push_neg
      intro p p_not_in_P_finset
      have p_not_in_S := (@Set.Finite.mem_toFinset ℕ P p P_finite).mpr.mt p_not_in_P_finset
      exact Set.notMem_setOf_iff.mp p_not_in_S
   contradiction

  tfae_have 1 → 5 := by sorry -- Tonio

  tfae_have 1 → 3 := by sorry -- Nina

  tfae_have 3 → 5 := by sorry -- Daniel

  tfae_finish
