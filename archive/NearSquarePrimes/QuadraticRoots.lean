/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import NearSquarePrimes.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Properties of Quadratic Roots of x² ≡ -1 (mod p)

This file establishes the fundamental number-theoretic properties of the equation
`x² ≡ -1 (mod p)` that drive the sieve for primes of the form `n² + 1`.

## Main Results

* `NearSquarePrimes.sqrtNegOneCount_eq_two`: For `p ≡ 1 (mod 4)`, `x² + 1 ≡ 0` has
  exactly 2 solutions in `ZMod p`.
* `NearSquarePrimes.sqrtNegOneCount_eq_zero`: For odd `p ≡ 3 (mod 4)`, `x² + 1 ≡ 0` has
  no solutions in `ZMod p`.
* `NearSquarePrimes.sqrtNegOneRoots_eq_pair`: If `ν` is a root, the roots are `{ν, -ν}`.

## References

* Portela, F. (2026). *A Poisson Limit Model for Landau's First Problem via
  Bounded-Variance Multi-Residue Sieves*, §1.1.
-/

open Finset BigOperators

namespace NearSquarePrimes

variable {p : ℕ} [hp : Fact p.Prime]

private instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- If `ν² + 1 = 0` in `ZMod p`, then `(-ν)² + 1 = 0` as well. -/
theorem sqrtNegOne_neg_root {ν : ZMod p} (hν : ν ^ 2 + 1 = 0) :
    (-ν) ^ 2 + 1 = 0 := by
  rw [neg_pow_two]; exact hν

/-
When `p` is an odd prime and `ν` is a root of `x² + 1 = 0` in `ZMod p`,
`ν ≠ -ν`.
-/
theorem sqrtNegOne_ne_neg {ν : ZMod p} (hp2 : p ≠ 2) (hν : ν ^ 2 + 1 = 0) :
    ν ≠ -ν := by
  -- Since $2 \neq 0$ in $\mathbb{Z}/p\mathbb{Z}$ and $\nu \neq 0$, we have $2\nu \neq 0$.
  have h_two_ne_zero : (2 : ZMod p) ≠ 0 := by
    exact by erw [ Ne, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( lt_of_le_of_ne hp.1.two_le ( Ne.symm hp2 ) ) ;
  grind +splitImp

/-
The number of roots of `x² + 1 = 0` in `ZMod p` is at most 2.
-/
theorem sqrtNegOneCount_le_two : sqrtNegOneCount p ≤ 2 := by
  -- For $p \equiv 1 \pmod{4}$, we have $\sqrt{-1} \in \mathbb{Z}/p\mathbb{Z}$, so there are exactly two roots.
  have h_sqrt_neg_one : ∀ (ν : ZMod p), ν ^ 2 + 1 = 0 → sqrtNegOneRoots p = {ν, -ν} := by
    unfold sqrtNegOneRoots;
    grind;
  by_cases h : ∃ ν : ZMod p, ν ^ 2 + 1 = 0 <;> simp_all +decide [ sqrtNegOneCount ];
  · exact h_sqrt_neg_one _ h.choose_spec ▸ Finset.card_insert_le _ _;
  · unfold sqrtNegOneRoots; aesop;

/-
If `ν` is a root of `x² + 1 = 0` in `ZMod p` with `p > 2`, then the roots
are exactly `{ν, -ν}` and these are distinct.
-/
theorem sqrtNegOneRoots_eq_pair {ν : ZMod p} (_hp2 : p ≠ 2)
    (hν : ν ^ 2 + 1 = 0) :
    sqrtNegOneRoots p = {ν, -ν} := by
  ext x;
  simp +decide [ sqrtNegOneRoots ];
  exact ⟨ fun hx => eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination hx - hν, by rintro ( rfl | rfl ) <;> linear_combination hν ⟩

/-
For a prime `p ≡ 1 (mod 4)`, `x² + 1 ≡ 0` has exactly 2 solutions in `ZMod p`.
-/
theorem sqrtNegOneCount_eq_two (hp1 : p % 4 = 1) :
    sqrtNegOneCount p = 2 := by
  obtain ⟨ν, hν⟩ : ∃ ν : ZMod p, ν ^ 2 + 1 = 0 := by
    obtain ⟨ x, hx ⟩ := ZMod.exists_sq_eq_neg_one_iff ( p := p );
    exact Exists.elim ( hx ( by rw [ hp1 ] ; decide ) ) fun x hx => ⟨ x, by rw [ sq, ← hx ] ; ring ⟩;
  convert sqrtNegOneRoots_eq_pair ( show p ≠ 2 by rintro rfl; contradiction ) hν |> congr_arg Finset.card using 1;
  rw [ Finset.card_pair ] ; norm_num [ sqrtNegOne_ne_neg ( show p ≠ 2 by rintro rfl; contradiction ) hν ]

/-
For an odd prime `p ≡ 3 (mod 4)`, `x² + 1 ≡ 0` has no solutions in `ZMod p`.
-/
theorem sqrtNegOneCount_eq_zero (hp3 : p % 4 = 3) :
    sqrtNegOneCount p = 0 := by
  rw [ sqrtNegOneCount ];
  simp +decide [ sqrtNegOneRoots ];
  intro x hx; have := ZMod.exists_sq_eq_neg_one_iff ( p := p ) ; simp_all +decide [ ← eq_sub_iff_add_eq ] ;
  exact this ⟨ x, by rw [ sq ] at hx; exact hx.symm ⟩

/-
For `p = 2`, `x² + 1 ≡ 0` has exactly 1 solution (namely `x = 1`).
-/
theorem sqrtNegOneCount_two : sqrtNegOneCount 2 = 1 := by
  native_decide

end NearSquarePrimes
