/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import Mathlib.Analysis.PSeries

/-!
# Shared Utilities for the Poisson-Admissible Sieve Framework

This file consolidates lemmas that appear identically in both `TwinPrimes` and
`NearSquarePrimes`, eliminating code duplication.

## Main Definitions

* `PoissonSieve.primorial`: The primorial `q_y = ∏_{p ≤ y, p prime} p`.

## Main Results

* `PoissonSieve.sum_inv_sq_primes_summable`: `∑ 1/p²` over primes converges.
* `PoissonSieve.poisson_gap_probability`: Gap probability converges to `e^{-λ}`.
* `PoissonSieve.correlation_factor_pos'`: Local correlation factor is positive.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators Filter

namespace PoissonSieve

/-! ### Primorial -/

/-- The primorial `q_y = ∏_{p ≤ y, p prime} p`. -/
noncomputable def primorial (y : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime, p

/-! ### Summability of `∑ 1/p²` -/

/-- The series `∑ 1/p²` restricted to primes is summable. -/
theorem sum_inv_sq_primes_summable :
    Summable (fun n : ℕ =>
      if Nat.Prime n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => by split_ifs <;> simp_all)
    (Real.summable_one_div_nat_pow.2 one_lt_two)

/-! ### Correlation factor positivity -/

/-- The local correlation factor `(1 - c·k/p) / (1 - c/p)^k` is positive for
`p > c · k`, where `c > 0`. -/
theorem correlation_factor_pos' (c : ℝ) (_hc : 0 < c) (k : ℕ) {p : ℕ}
    (hp : Nat.Prime p) (hp_large : c * k < (p : ℝ)) :
    0 < (1 - c * k / (p : ℝ)) / (1 - c / (p : ℝ)) ^ k := by
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rcases k with _ | k
  · simp
  · have hcp : c < p := by
      calc c = c * 1 := (mul_one c).symm
        _ ≤ c * (k + 1 : ℕ) := by gcongr; exact_mod_cast Nat.succ_pos k
        _ < p := hp_large
    exact div_pos (sub_pos.mpr ((div_lt_one hpp).mpr hp_large))
      (pow_pos (sub_pos.mpr ((div_lt_one hpp).mpr hcp)) _)

/-! ### Poisson gap probability -/

/-- **Poisson Gap Probability.** If the ratio of interval length to mean spacing
converges to `λ`, then `e^{-ratio}` converges to `e^{-λ}`. -/
theorem poisson_gap_probability (lam : ℝ) (_hlam : 0 < lam)
    (intervalLength meanSpacing : ℕ → ℝ)
    (_hinterval : ∀ n, 0 < intervalLength n)
    (_hspacing : ∀ n, 0 < meanSpacing n)
    (hratio : Filter.Tendsto (fun n => intervalLength n / meanSpacing n)
      Filter.atTop (nhds lam)) :
    Filter.Tendsto (fun n => Real.exp (-(intervalLength n / meanSpacing n)))
      Filter.atTop (nhds (Real.exp (-lam))) :=
  Real.continuous_exp.continuousAt.tendsto.comp (Filter.Tendsto.neg hratio)

end PoissonSieve
