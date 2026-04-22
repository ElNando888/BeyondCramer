/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import BeyondCramer.GrandConvergence

/-!
# Near-Square Prime Sieve as a Poisson-Admissible Sieve

This file proves that the `n² + 1` (near-square prime) sieve satisfies the
`PoissonAdmissibleSieve` axioms, making all results from the unified framework
available for primes of the form `n² + 1` as corollaries.

The key feature of the quadratic sieve is the **fluctuating density**:
`κ(p) = 1 + (−1/p)`, which equals `2` when `p ≡ 1 (mod 4)` (two roots of
`x² + 1 ≡ 0`) and `0` when `p ≡ 3 (mod 4)` (no roots). For `p = 2`, there
is one root (`x = 1`), but this is handled by the `1/2` parity factor.

## Main Results

* The `PoissonAdmissibleSieve` instance for the `n² + 1` sieve.
* The density map `κ(p) = sqrtNegOneCount' p` satisfies the geometric convergence
  property.

## References

* Portela, F. (2026). *A Poisson Limit Model for Landau's First Problem via
  Bounded-Variance Multi-Residue Sieves*.
-/

open Finset BigOperators Filter

/-- Tag type for the near-square prime sieve instance. -/
structure NearSquarePrimeSieveTag : Type where

/-! ### Density map -/

/-- The density map for the `n² + 1` sieve: `κ(p) = 2` for `p ≡ 1 (mod 4)`,
`κ(p) = 0` for odd `p ≡ 3 (mod 4)`, `κ(2) = 1`. -/
def nearSquareKappa (p : ℕ) : ℕ :=
  if p = 2 then 1
  else if p % 4 = 1 then 2
  else 0

theorem nearSquareKappa_le_two (p : ℕ) : nearSquareKappa p ≤ 2 := by
  simp only [nearSquareKappa]; split_ifs <;> omega

theorem nearSquareKappa_lt_prime (p : ℕ) (hp : Nat.Prime p) :
    nearSquareKappa p < p := by
  simp only [nearSquareKappa]
  rcases eq_or_lt_of_le hp.two_le with rfl | hgt
  · simp
  · split_ifs <;> omega

theorem nearSquareKappa_eq_two {p : ℕ} (hp1 : p % 4 = 1) (hp2 : p ≠ 2) :
    nearSquareKappa p = 2 := by
  simp [nearSquareKappa, hp2, hp1]

theorem nearSquareKappa_eq_zero {p : ℕ} (hp3 : p % 4 = 3) :
    nearSquareKappa p = 0 := by
  simp [nearSquareKappa, hp3]; omega

/-- The collision threshold `P(h)`: the maximum of `(hᵢ - hⱼ)² + 4` over all pairs,
including `i = j`. For primes `p > P(h)` with `p ≡ 1 (mod 4)`, the excluded classes of
distinct shifts do not overlap, giving `|S_p(h)| = 2k`.

Note: when `i = j`, the summand is `4`, so `P(h) ≥ 4` for any tuple of length ≥ 1.
The relevant bound is that for `i ≠ j` and prime `p > (hᵢ - hⱼ)² + 4`, neither
`p ∣ (hᵢ - hⱼ)` nor `p ∣ ((hᵢ - hⱼ)² + 4)` can hold. -/
noncomputable def nearSquarePrime_collisionThreshold {k : ℕ} (h : Fin k → ℤ) : ℕ :=
  Finset.sup (Finset.univ ×ˢ Finset.univ) fun ij : Fin k × Fin k =>
    ((h ij.1 - h ij.2) ^ 2 + 4).natAbs

/-
For `p > 2k`, the local factor `(1 - 2k/p) / (1 - 2/p)^k` deviates from 1 by
at most `C/p²`.
-/
theorem nearSquarePrime_correlation_factor_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, Nat.Prime p → p % 4 = 1 → 2 * k < p →
      |((1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k) - 1| ≤ C / (p : ℝ) ^ 2 := by
  -- Use the exponential approximation for large `p`, bounding離散誤差.
  have h_approx : ∃ C, 0 < C ∧ ∀ (p : ℕ), Nat.Prime p → p % 4 = 1 → 2 * k < p → |(1 - (2 * k : ℝ) / p) - (1 - 2 / p) ^ k| ≤ C / p ^ 2 := by
    -- Expand $(1 - 2/p)^k$ using the binomial theorem.
    have h_binom : ∀ (p : ℕ), Nat.Prime p → p % 4 = 1 → 2 * k < p → |(1 - (2 * k : ℝ) / p) - (1 - 2 / p) ^ k| ≤ ∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (2 / p : ℝ) ^ i := by
      intros p hp hp_mod hp_gt
      have h_binom : (1 - 2 / p : ℝ) ^ k = ∑ i ∈ Finset.range (k + 1), Nat.choose k i * (-2 / p : ℝ) ^ i := by
        rw [ sub_eq_add_neg, add_comm, add_pow ] ; congr ; ext ; ring;
      have h_binom_simplified : (1 - 2 / p : ℝ) ^ k = 1 - 2 * k / p + ∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (-2 / p : ℝ) ^ i := by
        erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ', h_binom ] ; ring;
        linarith;
      rw [ h_binom_simplified, abs_le ];
      norm_num [ neg_div, Finset.sum_neg_distrib ];
      exact ⟨ Finset.sum_le_sum fun i hi => by exact le_of_abs_le <| by simp [ abs_mul, abs_div ], by rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_le_sum fun i hi => by exact le_of_abs_le <| by simp [ abs_mul, abs_div ] ⟩;
    -- Since $(2/p)^i \leq (2/p)^2$ for $i \geq 2$, we can bound the sum.
    have h_bound : ∀ (p : ℕ), Nat.Prime p → p % 4 = 1 → 2 * k < p → ∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (2 / p : ℝ) ^ i ≤ (∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (2 : ℝ) ^ i) / p ^ 2 := by
      intros p hp hp4 hp2k
      have h_bound : ∀ i ∈ Finset.Icc 2 k, (2 / p : ℝ) ^ i ≤ (2 : ℝ) ^ i / p ^ 2 := by
        intro i hi; rw [ div_pow ] ; gcongr ; norm_cast ; nlinarith [ Finset.mem_Icc.mp hi ] ;
        · exact_mod_cast hp.pos;
        · linarith [ Finset.mem_Icc.mp hi ];
      simpa only [ Finset.sum_div _ _ _ ] using Finset.sum_le_sum fun i hi => by simpa only [ mul_div_assoc ] using mul_le_mul_of_nonneg_left ( h_bound i hi ) ( Nat.cast_nonneg _ ) ;
    exact ⟨ ∑ i ∈ Icc 2 k, ( k.choose i : ℝ ) * 2 ^ i + 1, by exact add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => by positivity ) zero_lt_one, fun p hp hp' hp'' => le_trans ( h_binom p hp hp' hp'' ) ( le_trans ( h_bound p hp hp' hp'' ) ( by gcongr ; norm_num ) ) ⟩;
  -- Use the fact that $(1 - 2/p)^k \geq (2k-1)/(2k+1)^k$ for $p > 2k$ to bound the denominator.
  have h_denom_bound : ∃ C, 0 < C ∧ ∀ (p : ℕ), Nat.Prime p → p % 4 = 1 → 2 * k < p → (1 - 2 / (p : ℝ)) ^ k ≥ C := by
    refine' ⟨ ( 1 - 2 / ( 2 * k + 1 ) ) ^ k, pow_pos ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) _, fun p hp hp' hp'' => pow_le_pow_left₀ ( sub_nonneg.mpr <| div_le_one_of_le₀ ( by norm_cast ; linarith ) <| by positivity ) ( sub_le_sub_left ( by rw [ div_le_div_iff₀ ] <;> norm_cast <;> linarith ) _ ) _ ⟩;
  obtain ⟨ C₁, hC₁_pos, hC₁ ⟩ := h_approx; obtain ⟨ C₂, hC₂_pos, hC₂ ⟩ := h_denom_bound; use C₁ / C₂; refine' ⟨ div_pos hC₁_pos hC₂_pos, fun p hp hp' hp'' => _ ⟩ ; rw [ div_sub_one, abs_div ];
  · rw [ div_right_comm ];
    gcongr ; aesop;
    exact le_trans ( hC₂ p hp hp' hp'' ) ( le_abs_self _ );
  · exact ne_of_gt ( lt_of_lt_of_le hC₂_pos ( hC₂ p hp hp' hp'' ) )

/-
The deviation of the local factor from 1 is summable.
-/
theorem nearSquarePrime_correlation_deviation_summable (k : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ =>
      if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n
      then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1
      else 0) := by
  -- By correlation_factor_bound, |deviation| ≤ C/p² for qualifying primes.
  have h_bound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, Nat.Prime p → p % 4 = 1 → 2 * k < p → |((1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k) - 1| ≤ C / (p : ℝ) ^ 2 := by
    exact nearSquarePrime_correlation_factor_bound k hk
  generalize_proofs at *; (
  obtain ⟨ C, hC₀, hC ⟩ := h_bound; refine Summable.of_norm ?_; simp_all +decide [ div_eq_mul_inv ] ;
  refine' Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => _ ) ( Summable.mul_left C <| Real.summable_nat_pow_inv.2 one_lt_two ) ; aesop;)


/-
The near-square prime sieve is a Poisson-admissible sieve.
-/
noncomputable instance nearSquarePrimeSieve :
    PoissonAdmissibleSieve NearSquarePrimeSieveTag where
  κ := nearSquareKappa
  T := nearSquarePrime_collisionThreshold
  κ_le := ⟨2, nearSquareKappa_le_two⟩
  κ_lt_prime := nearSquareKappa_lt_prime
  correlation_bound := fun k hk => by
    obtain ⟨C, hC_pos, hC⟩ := nearSquarePrime_correlation_factor_bound k hk
    refine ⟨C, hC_pos, fun p hp hpk => ?_⟩
    -- When κ(p) = 0, the factor is 1 and |1 - 1| = 0 ≤ C/p².
    -- When κ(p) = 2, this is exactly the existing bound.
    -- When p = 2 and κ = 1: 1*k < 2 means k = 1, and factor = 0.
    simp only [nearSquareKappa] at hpk ⊢
    split_ifs at hpk ⊢ with h_eq h_mod
    · -- p = 2, κ = 1: k < 2 so k = 1, factor = (1-1/2)/(1-1/2) - 1 = 0
      subst h_eq; have : k = 1 := by omega
      subst this; norm_num; exact div_nonneg hC_pos.le (by positivity)
    · -- p % 4 = 1, κ = 2: use existing bound
      exact hC p hp h_mod hpk
    · -- p % 4 ≠ 1, κ = 0: factor = 1, |1-1| = 0
      norm_num; exact div_nonneg hC_pos.le (by positivity)
  correlation_summable := fun k hk => by
    convert nearSquarePrime_correlation_deviation_summable k hk using 1;
    ext n; by_cases hn : Nat.Prime n <;> simp +decide [ hn, nearSquareKappa ] ;
    split_ifs <;> simp_all +decide;
    interval_cases k ; norm_num

/-! ### Corollaries -/

/-- The near-square prime geometric correlation product is multipliable. -/
theorem nearSquare_geometric_multipliable (k : ℕ) (hk : 0 < k) :
    Multipliable (fun n =>
      PoissonAdmissibleSieve.localFactor (σ := NearSquarePrimeSieveTag) k n) :=
  PoissonAdmissibleSieve.localFactor_multipliable k hk

/-- The near-square prime geometric correlation product is positive. -/
theorem nearSquare_geometric_pos (k : ℕ) (hk : 0 < k) :
    0 < ∏' n,
      PoissonAdmissibleSieve.localFactor (σ := NearSquarePrimeSieveTag) k n :=
  PoissonAdmissibleSieve.localFactor_tprod_pos k hk
