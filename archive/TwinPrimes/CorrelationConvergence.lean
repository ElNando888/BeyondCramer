/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import TwinPrimes.CollisionFiniteness
import PoissonViaCRT
import Mathlib.Analysis.PSeries
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Convergence of the Geometric Correlation for the Twin Prime Sieve

This file formalizes the absolute convergence of the infinite product defining the
geometric correlation constant for the twin prime sieve.

For the twin prime sieve with `k`-tuples, the local factor at an odd prime `p ≥ 3` is
`(1 - 2k/p) / (1 - 2/p)^k`, which deviates from 1 by `O(1/p²)`. The infinite product
over all primes therefore converges absolutely.

## Main Results

* `TwinPrimes.correlation_factor_bound`: The local factor is `1 + O(1/p²)`.
* `TwinPrimes.correlation_factor_pos`: The local factor is positive.
* `TwinPrimes.geometric_correlation_multipliable`: The product is multipliable.
* `TwinPrimes.geometric_correlation_pos`: The limit is positive.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators

namespace TwinPrimes

/-! ### Local factor analysis -/

/-
For `p > 2k`, the local factor `(1 - 2k/p) / (1 - 2/p)^k` deviates from 1 by
at most `C/p²`.
-/
theorem correlation_factor_bound (k : ℕ) (hk : 0 < k) :
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
The local factor is positive for `p > 2k`.
-/
theorem correlation_factor_pos (k : ℕ) {p : ℕ} (_hp : Nat.Prime p) (hp_large : 2 * k < p) :
    0 < (1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k := by
  rcases k with ( _ | k ) <;> norm_num;
  exact div_pos ( sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) ) ( pow_pos ( sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) ) _ )

/-
The sum `∑ 1/p²` over primes converges.
-/
theorem sum_inv_sq_primes_summable :
    Summable (fun n : ℕ => if Nat.Prime n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) := by
  exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )

/-! ### Infinite product convergence -/

/-
The deviation of the local factor from 1 is summable.
-/
theorem correlation_deviation_summable (k : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ =>
      if Nat.Prime n ∧ 2 * k < n
      then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1
      else 0) := by
  have h_summable : Summable (fun n : ℕ => if Nat.Prime n ∧ 2 * k < n then |((1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k) - 1| else 0) := by
    obtain ⟨ C, hC₀, hC ⟩ := correlation_factor_bound k hk;
    exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by aesop ) ( Summable.mul_left C <| Real.summable_nat_pow_inv.2 one_lt_two );
  -- Apply the fact that if the absolute value of a series is summable, then the series itself is summable.
  apply Summable.of_abs; exact h_summable.congr (by aesop)

/-
**Multipliability of the geometric correlation factors.**
The function `n ↦ f(n)` (where `f(n)` is the local factor for qualifying primes
and 1 otherwise) is multipliable.
-/
theorem geometric_correlation_multipliable (k : ℕ) (hk : 0 < k) :
    Multipliable (fun n : ℕ =>
      if Nat.Prime n ∧ 2 * k < n
      then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k
      else 1) := by
  have h_summable : Summable (fun n : ℕ => if Nat.Prime n ∧ 2 * k < n then (1 - 2 * (k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1 else 0) := by
    exact correlation_deviation_summable k hk;
  have h_prod : Multipliable (fun n : ℕ => 1 + (if Nat.Prime n ∧ 2 * k < n then (1 - 2 * (k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1 else 0)) := by
    refine' multipliable_one_add_of_summable _;
    convert h_summable.norm using 1;
  grind

/-
The infinite product of the geometric correlation factors is positive.
-/
theorem geometric_correlation_pos (k : ℕ) (hk : 0 < k) :
    0 < ∏' (n : ℕ),
      (if Nat.Prime n ∧ 2 * k < n
       then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k
       else 1) := by
  have := correlation_deviation_summable k hk;
  have := this.abs;
  have h_prod_pos : Summable (fun n : ℕ => |Real.log (if Nat.Prime n ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k else 1)|) := by
    have h_log_bound : ∀ᶠ n in Filter.atTop, |Real.log (1 + (if Nat.Prime n ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1 else 0))| ≤ 2 * |(if Nat.Prime n ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1 else 0)| := by
      have h_log_conv : ∀ᶠ n in Filter.atTop, |(if Nat.Prime n ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1 else 0)| ≤ 1 / 2 := by
        have := this.tendsto_atTop_zero; exact this.eventually ( ge_mem_nhds <| by norm_num ) ;
      filter_upwards [ h_log_conv ] with n hn;
      rw [ abs_le ] at *;
      constructor <;> cases abs_cases ( if Nat.Prime n ∧ 2 * k < n then ( 1 - 2 * ( k : ℝ ) / n ) / ( 1 - 2 / n ) ^ k - 1 else 0 ) <;> nlinarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 + ( if Nat.Prime n ∧ 2 * k < n then ( 1 - 2 * ( k : ℝ ) / n ) / ( 1 - 2 / n ) ^ k - 1 else 0 ) ), Real.log_inv ( 1 + ( if Nat.Prime n ∧ 2 * k < n then ( 1 - 2 * ( k : ℝ ) / n ) / ( 1 - 2 / n ) ^ k - 1 else 0 ) ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 + ( if Nat.Prime n ∧ 2 * k < n then ( 1 - 2 * ( k : ℝ ) / n ) / ( 1 - 2 / n ) ^ k - 1 else 0 ) ) ), mul_inv_cancel₀ ( by linarith : ( 1 + ( if Nat.Prime n ∧ 2 * k < n then ( 1 - 2 * ( k : ℝ ) / n ) / ( 1 - 2 / n ) ^ k - 1 else 0 ) ) ≠ 0 ) ];
    rw [ ← summable_nat_add_iff ( Classical.choose ( Filter.eventually_atTop.mp h_log_bound ) ) ] at *;
    refine' .of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => _ ) ( this.mul_left 2 );
    grind +revert;
  have h_prod_pos : ∏' n : ℕ, (if Nat.Prime n ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k else 1) = Real.exp (∑' n : ℕ, Real.log (if Nat.Prime n ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k else 1)) := by
    have h_prod_pos : ∀ {f : ℕ → ℝ}, (∀ n, 0 < f n) → Summable (fun n => |Real.log (f n)|) → ∏' n, f n = Real.exp (∑' n, Real.log (f n)) := by
      intros f hf_pos hf_summable;
      have h_prod_pos : ∀ {f : ℕ → ℝ}, (∀ n, 0 < f n) → Summable (fun n => Real.log (f n)) → ∏' n, f n = Real.exp (∑' n, Real.log (f n)) := by
        exact fun {f} a a_1 => Eq.symm (Real.rexp_tsum_eq_tprod a a_1);
      exact h_prod_pos hf_pos <| hf_summable.of_abs;
    apply h_prod_pos;
    · intro n; split_ifs <;> norm_num;
      exact div_pos ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) ( pow_pos ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) _ );
    · assumption;
  exact h_prod_pos.symm ▸ Real.exp_pos _

/-
**Convergence of the geometric correlation.**
For any fixed `k`, the partial products over qualifying primes converge
to a nonzero limit.
-/
theorem geometric_correlation_converges {k : ℕ} (hk : 0 < k)
    (h : Fin k → ℤ) (_hinj : Function.Injective h) :
    ∃ G : ℝ, G ≠ 0 ∧
      Filter.Tendsto
        (fun N => ∏ p ∈ (Finset.Icc 3 N).filter Nat.Prime,
          ((1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k))
        Filter.atTop (nhds G) := by
  -- By definition of $G_k$, we know that it converges to a nonzero limit.
  obtain ⟨G, hG⟩ : ∃ G : ℝ, 0 < G ∧ Filter.Tendsto (fun N : ℕ =>
      ∏ p ∈ (Finset.Icc 3 N).filter Nat.Prime,
        (if 2 * k < p then (1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k else 1)) Filter.atTop (nhds G) := by
          have := TwinPrimes.geometric_correlation_multipliable k hk;
          obtain ⟨G, hG⟩ : ∃ G : ℝ, 0 < G ∧ Filter.Tendsto (fun N : ℕ =>
              ∏ p ∈ Finset.range (N + 1),
                (if Nat.Prime p ∧ 2 * k < p then (1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k else 1)) Filter.atTop (nhds G) := by
                  refine' ⟨ _, _, this.hasProd.tendsto_prod_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) ⟩;
                  convert TwinPrimes.geometric_correlation_pos k hk using 1;
          refine' ⟨ G, hG.1, hG.2.congr' _ ⟩;
          filter_upwards [ Filter.eventually_gt_atTop 2 ] with N hN;
          rw [ ← Finset.prod_subset ( show Finset.filter Nat.Prime ( Finset.Icc 3 N ) ⊆ Finset.range ( N + 1 ) from fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ) ) ];
          · exact Finset.prod_congr rfl fun x hx => by aesop;
          · grind;
  refine' ⟨ G * ( ∏ p ∈ Finset.filter Nat.Prime ( Finset.Icc 3 ( 2 * k ) ), ( 1 - 2 * ( k : ℝ ) / p ) / ( 1 - 2 / ( p : ℝ ) ) ^ k ), _, _ ⟩;
  · refine' mul_ne_zero hG.1.ne' ( Finset.prod_ne_zero_iff.mpr _ );
    norm_num [ sub_eq_iff_eq_add ];
    field_simp;
    exact fun a ha₁ ha₂ ha₃ => ⟨ by norm_cast; linarith [ show a < 2 * k from lt_of_le_of_ne ha₂ ( by rintro rfl; exact absurd ha₃ ( Nat.not_prime_mul ( by linarith ) ( by linarith ) ) ) ], by norm_cast; intros; linarith ⟩;
  · refine' Filter.Tendsto.congr' _ ( hG.2.mul_const _ );
    filter_upwards [ Filter.eventually_gt_atTop ( 2 * k ) ] with N hN;
    rw [ ← Finset.prod_filter_mul_prod_filter_not ( Finset.filter Nat.Prime ( Finset.Icc 3 N ) ) fun p => 2 * k < p ];
    rw [ mul_assoc, ← Finset.prod_filter_mul_prod_filter_not ( Finset.filter Nat.Prime ( Finset.Icc 3 N ) ) fun p => p ≤ 2 * k ];
    simp_all +decide [ Finset.prod_ite, not_lt ];
    simp_all +decide [ Finset.filter_filter, mul_comm ];
    rw [ show ( Finset.filter ( fun x => Nat.Prime x ∧ x ≤ k * 2 ) ( Finset.Icc 3 N ) ) = Finset.filter ( fun x => Nat.Prime x ) ( Finset.Icc 3 ( k * 2 ) ) from ?_, show ( Finset.filter ( fun x => ( Nat.Prime x ∧ x ≤ k * 2 ) ∧ k * 2 < x ) ( Finset.Icc 3 N ) ) = ∅ from ?_ ] <;> norm_num;
    · ring;
    · grind

end TwinPrimes
