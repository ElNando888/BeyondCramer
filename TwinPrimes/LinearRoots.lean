/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import TwinPrimes.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Properties of Roots of x(x + 2) ≡ 0 (mod p)

This file establishes the number-theoretic properties of the equation
`x(x + 2) ≡ 0 (mod p)` that drive the sieve for twin primes.

The roots are `x ≡ 0` and `x ≡ -2 (mod p)`. For `p ≥ 3` these are distinct, giving
exactly 2 roots. For `p = 2`, they coincide (`0 ≡ -2 mod 2`), giving 1 root.

## Main Results

* `TwinPrimes.twinRoots_eq_pair`: For `p ≥ 3` prime, the roots are `{0, -2}`.
* `TwinPrimes.twinRootCount_eq_two`: For `p ≥ 3` prime, there are exactly 2 roots.
* `TwinPrimes.twinRootCount_two`: For `p = 2`, there is exactly 1 root.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators

namespace TwinPrimes

variable {p : ℕ} [hp : Fact p.Prime]

private instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- In `ZMod p` for prime `p`, the equation `x * (x + 2) = 0` implies `x = 0` or `x = -2`. -/
theorem twinRoot_cases {x : ZMod p} (hx : x * (x + 2) = 0) :
    x = 0 ∨ x = -2 := by
  rcases mul_eq_zero.mp hx with h | h
  · exact Or.inl h
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The roots of `x(x + 2) = 0` in `ZMod p` are contained in `{0, -2}`. -/
theorem twinRoots_subset :
    twinRoots p ⊆ {0, -2} := by
  intro x hx
  simp only [twinRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rcases twinRoot_cases hx with rfl | rfl <;> simp

/-- `0` is always a root of `x(x + 2) = 0`. -/
theorem zero_mem_twinRoots : (0 : ZMod p) ∈ twinRoots p := by
  simp [twinRoots]

/-- `-2` is always a root of `x(x + 2) = 0`. -/
theorem neg_two_mem_twinRoots : (-2 : ZMod p) ∈ twinRoots p := by
  simp [twinRoots]

/-
For `p ≠ 2`, `0 ≠ -2` in `ZMod p`.
-/
theorem zero_ne_neg_two (hp2 : p ≠ 2) : (0 : ZMod p) ≠ -2 := by
  simp +zetaDelta at *;
  erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( lt_of_le_of_ne hp.1.two_le ( Ne.symm hp2 ) )

/-- The roots of `x(x+2) = 0` in `ZMod p` are exactly `{0, -2}`. When `p = 2`, these
coincide, so the set is `{0}`. -/
theorem twinRoots_eq_pair :
    twinRoots p = {0, -2} := by
  ext x
  simp only [twinRoots, Finset.mem_filter, Finset.mem_univ, true_and,
             Finset.mem_insert, Finset.mem_singleton]
  exact ⟨twinRoot_cases, fun h => by rcases h with rfl | rfl <;> ring⟩

/-- For an odd prime `p ≥ 3`, there are exactly 2 roots. -/
theorem twinRootCount_eq_two (hp2 : p ≠ 2) :
    twinRootCount p = 2 := by
  unfold twinRootCount
  rw [twinRoots_eq_pair, Finset.card_pair (zero_ne_neg_two hp2)]

/-- For `p = 2`, there is exactly 1 root. -/
theorem twinRootCount_two : twinRootCount 2 = 1 := by native_decide

end TwinPrimes
