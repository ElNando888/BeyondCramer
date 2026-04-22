/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import TwinPrimes.CorrelationConvergence

/-!
# Poisson Limit for the Twin Prime Sieve

This file formalizes the main theorems of the Poisson limit model for twin primes:
the expectation factorization and the Poisson gap probability.

## Main Results

* `TwinPrimes.sieveDensity`: The baseline sieve density `ρ(y)`.
* `TwinPrimes.tupleExpectation`: The expected count of surviving `k`-tuples.
* `TwinPrimes.expectation_factorization`: The factorization into `ρ(y)^k · 𝔊(h)`.
* `TwinPrimes.poisson_gap_probability`: The gap probability converges to `e^{-λ}`.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators

namespace TwinPrimes

/-! ### Auxiliary: root count as a plain function of ℕ -/

/-- The number of roots of `x(x+2) = 0` in `ZMod p`, defined for all `p`
by treating `p = 0` as giving 0. -/
noncomputable def twinRootCount' (p : ℕ) : ℕ :=
  if h : p = 0 then 0 else @twinRootCount p ⟨h⟩

/-- The cardinality of excluded classes as a plain function of `p` and `h`. -/
noncomputable def excludedClassesCard {k : ℕ} (p : ℕ) (h : Fin k → ℤ) : ℕ :=
  if hp : p = 0 then 0
  else @Finset.card (ZMod p) (@excludedClasses p ⟨hp⟩ k (fun i => (h i : ZMod p)))

/-! ### Sieve density -/

/-- The baseline sieve density `ρ(y)`: the fraction of elements surviving the twin prime
sieve up to parameter `y`. For `p = 2`, one class is excluded (parity sieve).
For odd primes `p ≥ 3`, the number of excluded classes is 2 (namely `0` and `-2`).

$$\rho(y) = \frac{1}{2} \prod_{2 < p \le y,\, p \text{ prime}}
  \left(1 - \frac{2}{p}\right)$$ -/
noncomputable def sieveDensity (y : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
    (1 - (twinRootCount' p : ℝ) / p)

/-! ### Expected count of surviving configurations -/

/-- The expected number of surviving `k`-tuples modulo `q_y`:

$$E[N_k(\mathbf{h})] = q_y \cdot \frac{1}{2^k} \cdot \prod_{2 < p \le y,\, p \text{ prime}}
  \left(1 - \frac{|S_p(\mathbf{h})|}{p}\right)$$ -/
noncomputable def tupleExpectation {k : ℕ} (h : Fin k → ℤ) (y : ℕ) : ℝ :=
  (primorial y : ℝ) *
    ((1 / 2 : ℝ) ^ k *
      ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
        (1 - (excludedClassesCard p h : ℝ) / p))

/-
**Theorem 1 (Expectation Factorization).** The `k`-tuple expectation factorizes as
the product of the primorial, the `k`-th power of the single-event density, and the
geometric correlation constant.

For the twin prime sieve, every odd prime contributes 2 excluded classes for a single
event (same as for `p ≡ 1 mod 4` in the quadratic case). The factorization is:
`E[N_k(h)] = q_y · ρ(y)^k · ∏_{3 ≤ p ≤ y} (1 - |S_p(h)|/p) / (1 - 2/p)^k`.
-/
theorem expectation_factorization {k : ℕ} (_hk : 0 < k)
    (h : Fin k → ℤ) (_hinj : Function.Injective h) (y : ℕ) :
    tupleExpectation h y =
      (primorial y : ℝ) * sieveDensity y ^ k *
        (∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
          ((1 - (excludedClassesCard p h : ℝ) / p) /
           (1 - (twinRootCount' p : ℝ) / p) ^ k)) := by
  unfold tupleExpectation sieveDensity;
  norm_num [ mul_pow, Finset.prod_mul_distrib, mul_assoc ];
  rw [ ← Finset.prod_pow ];
  refine' Or.inl ( Eq.symm ( mul_div_cancel₀ _ _ ) );
  refine' Finset.prod_ne_zero_iff.mpr _;
  intro p hp
  have h_twinRootCount : twinRootCount' p ≤ 2 := by
    unfold twinRootCount';
    split_ifs <;> simp_all +decide [ twinRootCount ];
    haveI := Fact.mk hp.2; exact le_trans ( Finset.card_le_card ( TwinPrimes.twinRoots_subset ) ) ( Finset.card_insert_le _ _ ) ;
  exact pow_ne_zero _ ( sub_ne_zero_of_ne <| ne_of_gt <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_Icc.mp <| Finset.mem_filter.mp hp |>.1 ] )

/-! ### Poisson gap probability -/

/-- **Theorem 2 (Poisson Gap Probability).**
Under the Poisson limit model, if the ratio of interval length to mean spacing
converges to `λ`, then the gap exceedance probability `e^{-ratio}` converges
to `e^{-λ}`. -/
theorem poisson_gap_probability (lam : ℝ) (_hlam : 0 < lam)
    (intervalLength meanSpacing : ℕ → ℝ)
    (_hinterval : ∀ n, 0 < intervalLength n)
    (_hspacing : ∀ n, 0 < meanSpacing n)
    (hratio : Filter.Tendsto (fun n => intervalLength n / meanSpacing n)
      Filter.atTop (nhds lam)) :
    Filter.Tendsto (fun n => Real.exp (-(intervalLength n / meanSpacing n)))
      Filter.atTop (nhds (Real.exp (-lam))) :=
  Real.continuous_exp.continuousAt.tendsto.comp (Filter.Tendsto.neg hratio)

end TwinPrimes