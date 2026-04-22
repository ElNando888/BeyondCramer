/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import BeyondCramer.Utils
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The Poisson-Admissible Sieve Framework

This file defines the `PoissonAdmissibleSieve` class, which abstracts the shared
analytic structure of linear and quadratic multi-residue sieves into a single
framework. Both the twin prime sieve and the `n² + 1` sieve are instances.

## Main Definitions

* `PoissonAdmissibleSieve`: A typeclass packaging:
  - A **density map** `κ(p)`: the number of residue classes excluded per shift
    at prime `p`.
  - A **collision threshold** `T(h)`: beyond this bound, the excluded classes of
    distinct shifts do not overlap.
  - A **geometric convergence property**: the local correlation factor
    `L_p = (1 - |S_p(h)|/p) / (1 - κ(p)/p)^k` deviates from `1` by at most
    `O(1/p²)` for sufficiently large `p`, ensuring the infinite product converges.

## Design Notes

The class is parameterized by a `Type` index `σ` (the "sieve tag") so that
multiple sieve instances can coexist without overlap. The fields are chosen to
be the minimal analytic spine needed for the Grand Convergence Theorem in
`BeyondCramer.GrandConvergence`.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators Filter

/-! ### The core abstraction -/

/-- A **Poisson-admissible sieve** packages the analytic data shared by linear and
quadratic multi-residue sieves.

* `κ p` is the number of residue classes excluded by a single event at prime `p`.
* `T h` is the collision threshold for a `k`-tuple of shifts `h`: for primes
  `p > T(h)`, distinct shifts produce disjoint excluded-class sets, giving
  `|S_p(h)| = κ(p) · k`.
* `correlation_bound` asserts that the local ratio
  `(1 - κ(p)·k/p) / (1 - κ(p)/p)^k` deviates from `1` by at most `C / p²`
  for all primes `p` with `κ(p) · k < p`.
* `correlation_summable` asserts that the deviation series is summable over
  ℕ (with non-qualifying terms set to zero), which is the key input for the
  `Multipliable` / `Filter.Tendsto` convergence proof. -/
class PoissonAdmissibleSieve (σ : Type) where
  /-- The density map: number of excluded residue classes per shift at prime `p`. -/
  κ : ℕ → ℕ
  /-- The collision threshold for a `k`-tuple of integer shifts. -/
  T : {k : ℕ} → (Fin k → ℤ) → ℕ
  /-- Uniform bound: `κ(p)` is bounded by some constant. -/
  κ_le : ∃ B : ℕ, ∀ p, κ p ≤ B
  /-- The density map is strictly less than `p` for every prime `p`. This ensures
  that the sieve density factors `1 - κ(p)/p` are nonzero. -/
  κ_lt_prime : ∀ p, Nat.Prime p → κ p < p
  /-- Geometric convergence: `|(1 - κk/p) / (1 - κ/p)^k - 1| ≤ C / p²`
  for all primes `p` with `κ(p) · k < p`. -/
  correlation_bound :
    ∀ k : ℕ, 0 < k →
      ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, Nat.Prime p → κ p * k < p →
        |((1 - (κ p * k : ℝ) / p) / (1 - (κ p : ℝ) / p) ^ k) - 1| ≤ C / (p : ℝ) ^ 2
  /-- The deviation of the local correlation factor from `1` is summable.
  Terms for primes where `κ(p) · k ≥ p` are set to zero. -/
  correlation_summable :
    ∀ k : ℕ, 0 < k →
      Summable (fun n : ℕ =>
        if Nat.Prime n ∧ κ n * k < n
        then (1 - (κ n * k : ℝ) / n) / (1 - (κ n : ℝ) / n) ^ k - 1
        else 0)

namespace PoissonAdmissibleSieve

variable {σ : Type} [S : PoissonAdmissibleSieve σ]

/-- The local correlation factor at prime `p` for a `k`-tuple. For qualifying
primes this is `(1 - κk/p) / (1 - κ/p)^k`; for others it is `1`. -/
noncomputable def localFactor (k p : ℕ) : ℝ :=
  if Nat.Prime p ∧ S.κ p * k < p
  then (1 - (S.κ p * k : ℝ) / p) / (1 - (S.κ p : ℝ) / p) ^ k
  else 1

/-- The local factor is positive. -/
theorem localFactor_pos (k p : ℕ) : 0 < localFactor (σ := σ) k p := by
  simp only [localFactor]
  split_ifs with h
  · rcases k with _ | k
    · simp
    · have hpp : (0 : ℝ) < p := by exact_mod_cast h.1.pos
      have hκk : (S.κ p * (k + 1) : ℝ) < p := by exact_mod_cast h.2
      have hκ : (S.κ p : ℝ) < p := by
        have : S.κ p ≤ S.κ p * (k + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
        exact_mod_cast Nat.lt_of_le_of_lt this h.2
      refine div_pos (sub_pos.mpr ((div_lt_one hpp).mpr ?_))
        (pow_pos (sub_pos.mpr ((div_lt_one hpp).mpr hκ)) _)
      exact_mod_cast h.2
  · exact one_pos

/-- The deviation `localFactor k p - 1` is summable over `ℕ`. -/
theorem localFactor_deviation_summable (k : ℕ) (hk : 0 < k) :
    Summable (fun n => localFactor (σ := σ) k n - 1) := by
  have h := S.correlation_summable k hk
  exact h.congr fun n => by simp only [localFactor]; split_ifs <;> ring

/-- The infinite product of local factors is `Multipliable`. -/
theorem localFactor_multipliable (k : ℕ) (hk : 0 < k) :
    Multipliable (fun n => localFactor (σ := σ) k n) := by
  have hsumm := localFactor_deviation_summable (σ := σ) k hk
  have hmult : Multipliable (fun n => 1 + (localFactor (σ := σ) k n - 1)) :=
    multipliable_one_add_of_summable hsumm.norm
  exact hmult.congr fun n => by ring

/-
The infinite product of local factors is positive.
-/
theorem localFactor_tprod_pos (k : ℕ) (hk : 0 < k) :
    0 < ∏' n, localFactor (σ := σ) k n := by
  have := S.localFactor_multipliable k hk;
  rw [ this.hasProd.tprod_eq ];
  have h_log_summable : Summable (fun n => Real.log (S.localFactor k n)) := by
    have h_log_summable : ∀ᶠ n in Filter.atTop, |Real.log (S.localFactor k n)| ≤ 2 * |S.localFactor k n - 1| := by
      have h_log_summable : ∀ᶠ n in Filter.atTop, |S.localFactor k n - 1| < 1 / 2 := by
        have := S.localFactor_deviation_summable k hk;
        exact this.tendsto_atTop_zero.eventually ( Metric.ball_mem_nhds _ one_half_pos ) |> fun h => h.mono fun n hn => by simpa using hn;
      filter_upwards [ h_log_summable ] with n hn;
      have h_log_bound : ∀ x : ℝ, 0 < x ∧ |x - 1| < 1 / 2 → |Real.log x| ≤ 2 * |x - 1| := by
        intros x hx;
        cases abs_cases ( Real.log x ) <;> cases abs_cases ( x - 1 ) <;> nlinarith [ Real.log_le_sub_one_of_pos hx.1, Real.log_inv x ▸ Real.log_le_sub_one_of_pos ( inv_pos.mpr hx.1 ), mul_inv_cancel₀ hx.1.ne', abs_lt.mp hx.2 ];
      exact h_log_bound _ ⟨ S.localFactor_pos k n, hn ⟩;
    simp +zetaDelta at *;
    obtain ⟨ N, hN ⟩ := h_log_summable;
    rw [ ← summable_nat_add_iff N ];
    exact Summable.of_norm <| Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => hN _ <| Nat.le_add_left _ _ ) <| Summable.mul_left _ <| by simpa using S.localFactor_deviation_summable k hk |> Summable.abs |> Summable.comp_injective <| add_left_injective N;
  have h_exp_pos : ∏' n, S.localFactor k n = Real.exp (∑' n, Real.log (S.localFactor k n)) := by
    have := @Real.rexp_tsum_eq_tprod;
    rw [ this ( fun n => S.localFactor_pos k n ) h_log_summable ];
  exact h_exp_pos.symm ▸ Real.exp_pos _

/-- The infinite product of local factors is nonzero. -/
theorem localFactor_tprod_ne_zero (k : ℕ) (hk : 0 < k) :
    ∏' n, localFactor (σ := σ) k n ≠ 0 :=
  ne_of_gt (localFactor_tprod_pos k hk)

end PoissonAdmissibleSieve
