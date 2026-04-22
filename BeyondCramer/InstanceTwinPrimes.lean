/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import BeyondCramer.GrandConvergence

/-!
# Twin Prime Sieve as a Poisson-Admissible Sieve

This file proves that the twin prime sieve satisfies the `PoissonAdmissibleSieve`
axioms, making all results from the unified framework (Grand Convergence Theorem,
multipliability, positivity) available for twin primes as corollaries.

## Main Results

* The `PoissonAdmissibleSieve` instance for the twin prime sieve.
* The Krafft residues `{0, -2}` satisfy `κ(p) = 2` for odd primes.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators Filter

/-- Tag type for the twin prime sieve instance. -/
structure TwinPrimeSieveTag : Type where

/-! ### Density map -/

/-- The density map for the twin prime sieve.
`κ(p) = 2` for odd primes (two roots `0` and `-2` of `x(x+2)`),
`κ(2) = 1` (roots coincide mod 2). For non-primes the value is irrelevant. -/
def twinPrimeKappa (p : ℕ) : ℕ := if p = 2 then 1 else 2

theorem twinPrimeKappa_le_two (p : ℕ) : twinPrimeKappa p ≤ 2 := by
  simp only [twinPrimeKappa]; split_ifs <;> omega

theorem twinPrimeKappa_lt_prime (p : ℕ) (hp : Nat.Prime p) :
    twinPrimeKappa p < p := by
  simp only [twinPrimeKappa]
  rcases eq_or_lt_of_le hp.two_le with rfl | hgt
  · simp
  · simp [show p ≠ 2 by omega]; omega

theorem twinPrimeKappa_odd {p : ℕ} (hp2 : p ≠ 2) :
    twinPrimeKappa p = 2 := by
  simp [twinPrimeKappa, hp2]

/-! ### Instance construction -/

/-- The collision threshold for the twin prime sieve: the maximum of
`|hᵢ - hⱼ|`, `|hᵢ - hⱼ + 2|`, and `|hᵢ - hⱼ - 2|` over all pairs `(i, j)`.
For primes `p` exceeding this threshold, the excluded classes of distinct shifts
do not overlap, giving `|S_p(h)| = 2k`. -/
noncomputable def twinPrime_collisionThreshold {k : ℕ} (h : Fin k → ℤ) : ℕ :=
  Finset.sup (Finset.univ ×ˢ Finset.univ) fun ij : Fin k × Fin k =>
    max ((h ij.1 - h ij.2).natAbs)
      (max ((h ij.1 - h ij.2 + 2).natAbs) ((h ij.1 - h ij.2 - 2).natAbs))

/-
For `p > 2k`, the local factor `(1 - 2k/p) / (1 - 2/p)^k` deviates from 1 by
at most `C/p²`.
-/
theorem twinPrime_correlation_factor_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, Nat.Prime p → 2 * k < p →
      |((1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k) - 1| ≤ C / (p : ℝ) ^ 2 := by
  -- Set $C$ to be $(sum_{i in Icc 2 k} C(k,i) * 2^i + 1) / ((1 - 2/(2k+1))^k)$.
  obtain ⟨C, hC_pos, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, Nat.Prime p → 2 * k < p → |(1 - 2 * k / (p : ℝ)) - (1 - 2 / (p : ℝ)) ^ k| ≤ C / (p : ℝ) ^ 2 := by
    -- By the binomial theorem, we have $(1 - 2/p)^k = 1 - 2k/p + \sum_{i=2}^k \binom{k}{i} (-2/p)^i$.
    have h_binom : ∀ p : ℕ, Nat.Prime p → 2 * k < p → (1 - 2 / (p : ℝ)) ^ k = 1 - 2 * k / (p : ℝ) + ∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (-2 / (p : ℝ)) ^ i := by
      intro p hp hp'; rw [ sub_eq_neg_add, add_pow ] ; norm_num [ Finset.sum_range_succ', mul_assoc, div_eq_mul_inv ] ;
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ', mul_comm ] ; ring;
      linarith;
    -- The sum $\sum_{i=2}^k \binom{k}{i} (-2/p)^i$ is bounded by $\sum_{i=2}^k \binom{k}{i} (2/p)^i$.
    have h_sum_bound : ∀ p : ℕ, Nat.Prime p → 2 * k < p → |∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (-2 / (p : ℝ)) ^ i| ≤ ∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (2 / (p : ℝ)) ^ i := by
      exact fun p hp hp' => le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => by rw [ abs_mul, abs_pow, abs_div, abs_neg, abs_two, abs_of_nonneg ( Nat.cast_nonneg _ : ( 0 : ℝ ) ≤ k.choose i ) ] ; norm_num ) ;
    -- The sum $\sum_{i=2}^k \binom{k}{i} (2/p)^i$ is bounded by $\sum_{i=2}^k \binom{k}{i} (2/p)^2$.
    have h_sum_bound_final : ∀ p : ℕ, Nat.Prime p → 2 * k < p → ∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (2 / (p : ℝ)) ^ i ≤ (∑ i ∈ Finset.Icc 2 k, Nat.choose k i * (2 : ℝ) ^ i) / (p : ℝ) ^ 2 := by
      intros p hp hp_gt
      have h_term_bound : ∀ i ∈ Finset.Icc 2 k, (Nat.choose k i : ℝ) * (2 / (p : ℝ)) ^ i ≤ (Nat.choose k i : ℝ) * (2 : ℝ) ^ i / (p : ℝ) ^ 2 := by
        intro i hi; rw [ mul_div_assoc ] ; gcongr ; ring_nf ;
        exact mul_le_mul_of_nonneg_right ( pow_le_pow_of_le_one ( by positivity ) ( inv_le_one_of_one_le₀ ( mod_cast hp.one_lt.le ) ) ( by linarith [ Finset.mem_Icc.mp hi ] ) ) ( by positivity );
      simpa only [ Finset.sum_div _ _ _ ] using Finset.sum_le_sum h_term_bound;
    refine' ⟨ ∑ i ∈ Finset.Icc 2 k, Nat.choose k i * 2 ^ i + 1, _, _ ⟩;
    · positivity;
    · intro p hp hp'; rw [ h_binom p hp hp' ] ; norm_num [ abs_le ] at *;
      constructor <;> nlinarith [ h_sum_bound p hp hp', h_sum_bound_final p hp hp', show ( p : ℝ ) ^ 2 > 0 by exact sq_pos_of_pos ( Nat.cast_pos.mpr hp.pos ), div_mul_cancel₀ ( ∑ i ∈ Icc 2 k, ( k.choose i : ℝ ) * 2 ^ i + 1 ) ( show ( p : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 ( Nat.cast_ne_zero.mpr hp.ne_zero ) ), div_mul_cancel₀ ( ∑ i ∈ Icc 2 k, ( k.choose i : ℝ ) * 2 ^ i ) ( show ( p : ℝ ) ^ 2 ≠ 0 by exact pow_ne_zero 2 ( Nat.cast_ne_zero.mpr hp.ne_zero ) ) ];
  -- Since $(1 - 2/p)^k$ is bounded below, we can find a constant $M$ such that $|(1 - 2/p)^k| \geq M$ for all $p > 2k$.
  obtain ⟨M, hM_pos, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ p : ℕ, Nat.Prime p → 2 * k < p → |(1 - 2 / (p : ℝ)) ^ k| ≥ M := by
    refine' ⟨ ( 1 - 2 / ( 2 * k + 1 : ℝ ) ) ^ k, pow_pos ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) _, fun p hp hp' => _ ⟩;
    rw [ abs_of_nonneg ( pow_nonneg ( sub_nonneg.mpr <| by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ) _ ) ] ; gcongr ; norm_cast;
    · exact sub_nonneg_of_le ( div_le_one_of_le₀ ( by norm_cast; linarith ) ( by positivity ) );
    · norm_cast;
  refine' ⟨ C / M, div_pos hC_pos hM_pos, fun p hp hp' => _ ⟩;
  rw [ div_sub_one, abs_div ];
  · rw [ div_right_comm ];
    gcongr <;> aesop;
  · exact pow_ne_zero _ ( sub_ne_zero_of_ne <| by rw [ Ne.eq_def, eq_div_iff ] <;> norm_cast <;> linarith [ hp.two_le ] )

/-
The deviation of the local factor from 1 is summable.
-/
theorem twinPrime_correlation_deviation_summable (k : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ =>
      if Nat.Prime n ∧ 2 * k < n
      then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1
      else 0) := by
  have h_summable : Summable (fun n : ℕ => if Nat.Prime n ∧ 2 * k < n then |((1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k) - 1| else 0) := by
    obtain ⟨ C, hC₀, hC ⟩ := twinPrime_correlation_factor_bound k hk;
    exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by aesop ) ( Summable.mul_left C <| Real.summable_nat_pow_inv.2 one_lt_two );
  -- Apply the fact that if the absolute value of a series is summable, then the series itself is summable.
  apply Summable.of_abs; exact h_summable.congr (by aesop)


/-
The twin prime sieve is a Poisson-admissible sieve.
-/
noncomputable instance twinPrimeSieve : PoissonAdmissibleSieve TwinPrimeSieveTag where
  κ := twinPrimeKappa
  T := twinPrime_collisionThreshold
  κ_le := ⟨2, twinPrimeKappa_le_two⟩
  κ_lt_prime := twinPrimeKappa_lt_prime
  correlation_bound := fun k hk => by
    obtain ⟨C, hC_pos, hC⟩ := twinPrime_correlation_factor_bound k hk
    refine ⟨C, hC_pos, fun p hp hpk => ?_⟩
    rcases eq_or_lt_of_le hp.two_le with rfl | hgt
    · simp [twinPrimeKappa] at hpk
      -- hpk : k < 2, so k = 1, and the factor is (1-1/2)/(1-1/2) - 1 = 0
      have hk1 : k = 1 := by omega
      subst hk1; simp [twinPrimeKappa]; norm_num
      exact div_nonneg hC_pos.le (by positivity)
    · rw [twinPrimeKappa_odd (by omega)] at hpk ⊢; exact hC p hp hpk
  correlation_summable := fun k hk => by
    convert twinPrime_correlation_deviation_summable k hk using 1;
    ext n; by_cases hn : n = 2 <;> simp +decide [ hn, twinPrimeKappa ] ;
    rcases k with ( _ | _ | k ) <;> norm_num at *

/-! ### Corollaries -/

/-- The twin prime geometric correlation product is multipliable. -/
theorem twinPrime_geometric_multipliable (k : ℕ) (hk : 0 < k) :
    Multipliable (fun n =>
      PoissonAdmissibleSieve.localFactor (σ := TwinPrimeSieveTag) k n) :=
  PoissonAdmissibleSieve.localFactor_multipliable k hk

/-- The twin prime geometric correlation product is positive. -/
theorem twinPrime_geometric_pos (k : ℕ) (hk : 0 < k) :
    0 < ∏' n,
      PoissonAdmissibleSieve.localFactor (σ := TwinPrimeSieveTag) k n :=
  PoissonAdmissibleSieve.localFactor_tprod_pos k hk
