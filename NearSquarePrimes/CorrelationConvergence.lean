/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import NearSquarePrimes.CollisionFiniteness
import PoissonViaCRT
import Mathlib.Analysis.PSeries
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Log.Summable


/-!
# Convergence of the Geometric Correlation (Lemma 2)

This file formalizes Lemma 2 of the manuscript: the absolute convergence of the
infinite product defining the geometric correlation constant `𝔊(h)`.

## Main Results

* `NearSquarePrimes.correlation_factor_bound`: The local factor is `1 + O(1/p²)`.
* `NearSquarePrimes.correlation_factor_pos`: The local factor is positive.
* `NearSquarePrimes.geometric_correlation_multipliable`: The product is multipliable.
* `NearSquarePrimes.geometric_correlation_pos`: The limit is positive.

## References

* Portela, F. (2026). *A Poisson Limit Model for Landau's First Problem via
  Bounded-Variance Multi-Residue Sieves*, Lemma 2.
-/

open Finset BigOperators

namespace NearSquarePrimes

/-! ### Local factor analysis -/

/-
For `p > 2k`, the local factor `(1 - 2k/p) / (1 - 2/p)^k` deviates from 1 by
at most `C/p²`.
-/
theorem correlation_factor_bound (k : ℕ) (hk : 0 < k) :
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
The local factor is positive for `p > 2k`.
-/
theorem correlation_factor_pos (k : ℕ) {p : ℕ} (hp : Nat.Prime p) (hp_large : 2 * k < p) :
    0 < (1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k := by
  refine' div_pos _ _;
  · rw [ sub_pos, div_lt_iff₀ ] <;> norm_cast <;> linarith [ hp.two_le ];
  · rcases p with ( _ | _ | _ | p ) <;> norm_num at *;
    · aesop;
    · exact pow_pos ( sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> linarith ) ) _

/-
The sum `∑ 1/p²` over primes `p ≡ 1 (mod 4)` converges.
-/
theorem sum_inv_sq_primes_one_mod_four_summable :
    Summable (fun n : ℕ => if Nat.Prime n ∧ n % 4 = 1 then (1 : ℝ) / (n : ℝ) ^ 2 else 0) := by
  exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two )

/-! ### Infinite product convergence -/

/-
The deviation of the local factor from 1 is summable.
-/
theorem correlation_deviation_summable (k : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ =>
      if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n
      then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k - 1
      else 0) := by
  -- By correlation_factor_bound, |deviation| ≤ C/p² for qualifying primes.
  have h_bound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, Nat.Prime p → p % 4 = 1 → 2 * k < p → |((1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k) - 1| ≤ C / (p : ℝ) ^ 2 := by
    exact correlation_factor_bound k hk
  generalize_proofs at *; (
  obtain ⟨ C, hC₀, hC ⟩ := h_bound; refine Summable.of_norm ?_; simp_all +decide [ div_eq_mul_inv ] ;
  refine' Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => _ ) ( Summable.mul_left C <| Real.summable_nat_pow_inv.2 one_lt_two ) ; aesop;)

/-
**Multipliability of the geometric correlation factors (Lemma 2).**
The function `n ↦ f(n)` (where `f(n)` is the local factor for qualifying primes
and 1 otherwise) is multipliable. This is the key infinite-product convergence result.
-/
theorem geometric_correlation_multipliable (k : ℕ) (hk : 0 < k) :
    Multipliable (fun n : ℕ =>
      if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n
      then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k
      else 1) := by
  convert multipliable_one_add_of_summable _ using 1;
  rotate_left;
  exact NormMulClass.toNormOneClass;
  exact fun n => if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n then ( 1 - 2 * k / n ) / ( 1 - 2 / n ) ^ k - 1 else 0;
  · infer_instance;
  · convert correlation_deviation_summable k hk |> Summable.norm using 1;
  · ext; split_ifs <;> ring

/-
The infinite product (tprod) of the geometric correlation factors is positive.
-/
theorem geometric_correlation_pos (k : ℕ) (hk : 0 < k) :
    0 < ∏' (n : ℕ),
      (if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n
       then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k
       else 1) := by
  by_contra h_neg;
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |(if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k else 1) - 1| ≤ C / (n : ℝ) ^ 2 := by
    have h_bound : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, Nat.Prime n → n % 4 = 1 → 2 * k < n → |((1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k) - 1| ≤ C / (n : ℝ) ^ 2 := by
      grind +suggestions;
    obtain ⟨ C, hC₀, hC ⟩ := h_bound;
    refine' ⟨ C, hC₀, fun n => _ ⟩ ; split_ifs <;> simp_all +decide;
    positivity;
  have h_prod_pos : Summable (fun n : ℕ => |(if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k else 1) - 1|) := by
    exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => hC.2 n ) ( Summable.mul_left _ <| Real.summable_nat_pow_inv.2 one_lt_two );
  have h_prod_pos : ∏' n : ℕ, (if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k else 1) ≠ 0 := by
    have h_prod_pos : ∀ {a : ℕ → ℝ}, (∀ n, 0 < a n) → Summable (fun n => |a n - 1|) → ∏' n, a n ≠ 0 := by
      intros a ha hsum
      have h_prod_pos : Summable (fun n => Real.log (a n)) := by
        have h_log_bound : ∀ᶠ n in Filter.atTop, |Real.log (a n)| ≤ 2 * |a n - 1| := by
          have h_log_bound : ∀ᶠ n in Filter.atTop, |a n - 1| < 1 / 2 := by
            exact hsum.tendsto_atTop_zero.eventually ( gt_mem_nhds <| by norm_num );
          filter_upwards [ h_log_bound ] with n hn;
          rw [ abs_le ];
          constructor <;> cases abs_cases ( a n - 1 ) <;> nlinarith [ ha n, Real.log_le_sub_one_of_pos ( ha n ), Real.log_inv ( a n ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( ha n ) ), mul_inv_cancel₀ ( ne_of_gt ( ha n ) ) ];
        simp +zetaDelta at *;
        rw [ ← summable_nat_add_iff h_log_bound.choose ];
        -- Since the series ∑ |a n - 1| is summable, multiplying by 2 (a constant) should still keep it summable. Therefore, the series ∑ |Real.log (a (n + h_log_bound.choose))| is summable.
        have h_log_summable : Summable (fun n => |Real.log (a (n + h_log_bound.choose))|) := by
          exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_log_bound.choose_spec _ ( Nat.le_add_left _ _ ) ) ( Summable.mul_left _ ( hsum.comp_injective ( add_left_injective _ ) ) );
        exact h_log_summable.of_abs;
      have h_prod_pos : ∏' n, a n = Real.exp (∑' n, Real.log (a n)) := by
        exact Eq.symm (Real.rexp_tsum_eq_tprod ha h_prod_pos);
      exact h_prod_pos.symm ▸ Real.exp_ne_zero _;
    apply h_prod_pos;
    · intro n; split_ifs <;> norm_num;
      exact correlation_factor_pos k ( by tauto ) ( by tauto );
    · assumption;
  refine' h_neg ( lt_of_le_of_ne _ ( Ne.symm h_prod_pos ) );
  have h_prod_pos : ∀ n : ℕ, 0 ≤ (if Nat.Prime n ∧ n % 4 = 1 ∧ 2 * k < n then (1 - (2 * k : ℝ) / n) / (1 - 2 / (n : ℝ)) ^ k else 1) := by
    intro n; split_ifs <;> norm_num;
    exact div_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ ( by norm_cast; linarith ) <| by positivity ) <| pow_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ ( by norm_cast; linarith ) <| by positivity ) _;
  rw [ tprod_def ];
  split_ifs <;> norm_num;
  · exact finprod_nonneg h_prod_pos;
  · have := Exists.choose_spec ‹_›;
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds this fun n => Finset.prod_nonneg fun _ _ => h_prod_pos _

/-
**Convergence of the geometric correlation (Lemma 2 of the manuscript).**
For any fixed `k`, the partial products over qualifying primes converge.

The limit `G` is nonzero but not necessarily positive, because the local factor
`(1 - 2k/p)/(1 - 2/p)^k` can be negative for small primes `p < 2k`.
However, the tail product (over `p > 2k`) converges to a positive limit by the
bounded-variance argument.
-/
theorem geometric_correlation_converges {k : ℕ} (hk : 0 < k)
    (h : Fin k → ℤ) (_hinj : Function.Injective h) :
    ∃ G : ℝ, G ≠ 0 ∧
      Filter.Tendsto
        (fun N => ∏ p ∈ (Finset.Icc 5 N).filter (fun p => Nat.Prime p ∧ p % 4 = 1),
          ((1 - (2 * k : ℝ) / p) / (1 - 2 / (p : ℝ)) ^ k))
        Filter.atTop (nhds G) := by
  -- By definition of $f$, we know that its product converges to a positive number.
  obtain ⟨G, hG⟩ : ∃ G : ℝ, 0 < G ∧ Filter.Tendsto (fun N : ℕ =>
      ∏ p ∈ (Finset.Icc 5 N).filter fun p => (Nat.Prime p ∧ p % 4 = 1 ∧ 2 * k < p),
        (1 - (2 * (k : ℝ) / p)) / (1 - 2 / (p : ℝ)) ^ k) Filter.atTop (nhds G) := by
          obtain ⟨G, hG⟩ : ∃ G : ℝ, 0 < G ∧ Filter.Tendsto (fun N => ∏ p ∈ Finset.filter (fun p => Nat.Prime p ∧ p % 4 = 1 ∧ 2 * k < p) (Finset.range (N + 1)), (1 - 2 * k / (p : ℝ)) / (1 - 2 / (p : ℝ)) ^ k) Filter.atTop (nhds G) := by
            have := geometric_correlation_pos k hk;
            obtain ⟨G, hG⟩ : ∃ G : ℝ, 0 < G ∧ Filter.Tendsto (fun N => ∏ p ∈ Finset.range (N + 1), (if Nat.Prime p ∧ p % 4 = 1 ∧ 2 * k < p then (1 - 2 * k / (p : ℝ)) / (1 - 2 / (p : ℝ)) ^ k else 1)) Filter.atTop (nhds G) := by
              have := geometric_correlation_multipliable k hk;
              exact ⟨ _, by assumption, this.hasProd.tendsto_prod_nat.comp <| Filter.tendsto_add_atTop_nat _ ⟩;
            exact ⟨ G, hG.1, hG.2.congr fun N => by rw [ Finset.prod_filter ] ⟩;
          refine' ⟨ G, hG.1, hG.2.congr' _ ⟩;
          filter_upwards [ Filter.eventually_gt_atTop 4 ] with N hN;
          refine' Finset.prod_subset _ _ <;> simp +contextual [ Finset.subset_iff ];
          exact fun p hp₁ hp₂ hp₃ hp₄ => le_of_not_gt fun hp₅ => by interval_cases p <;> trivial;
  refine' ⟨ G * ∏ p ∈ ( Finset.Icc 5 ( 2 * k ) ).filter fun p => Nat.Prime p ∧ p % 4 = 1, ( 1 - 2 * ( k : ℝ ) / p ) / ( 1 - 2 / ( p : ℝ ) ) ^ k, _, _ ⟩;
  · refine' mul_ne_zero hG.1.ne' ( Finset.prod_ne_zero_iff.mpr _ );
    intro p hp; norm_num [ sub_eq_iff_eq_add ] ;
    rw [ eq_div_iff ] <;> norm_cast <;> norm_num at *;
    · exact ⟨ by omega, fun h => absurd h ( by rw [ eq_div_iff ] <;> norm_cast <;> linarith ) ⟩;
    · linarith;
  · refine' Filter.Tendsto.congr' _ ( hG.2.mul_const _ );
    filter_upwards [ Filter.eventually_ge_atTop ( 2 * k ) ] with N hN;
    rw [ ← Finset.prod_union ];
    · refine' Finset.prod_subset _ _ <;> simp +contextual [ Finset.subset_iff ];
      lia;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ), Finset.mem_filter.mp hx₁ |>.2.2.2 ] ;

end NearSquarePrimes
