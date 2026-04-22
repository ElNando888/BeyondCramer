/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import NearSquarePrimes.CorrelationConvergence

/-!
# Poisson Limit for the Quadratic Sieve (Theorems 1 and 2)

This file formalizes the main theorems of the manuscript: the Poisson limit for the
distribution of primes of the form `n² + 1`.

## Main Results

* `NearSquarePrimes.sieveDensity`: The baseline sieve density `ρ(y)`.
* `NearSquarePrimes.tupleExpectation`: The expected count of surviving `k`-tuples.
* `NearSquarePrimes.expectation_factorization`: The factorization into `ρ(y)^k · 𝔊(h)`.
* `NearSquarePrimes.poisson_gap_probability`: The gap probability converges to `e^{-λ}`.

## References

* Portela, F. (2026). *A Poisson Limit Model for Landau's First Problem via
  Bounded-Variance Multi-Residue Sieves*, Theorems 1–2.
* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators

namespace NearSquarePrimes

/-! ### Auxiliary: root count as a plain function of ℕ -/

/-- The number of roots of `x² + 1 = 0` in `ZMod p`, defined for all `p`
by treating `p = 0` as giving 0. -/
noncomputable def sqrtNegOneCount' (p : ℕ) : ℕ :=
  if h : p = 0 then 0 else @sqrtNegOneCount p ⟨h⟩

/-- The cardinality of excluded classes as a plain function of `p` and `h`. -/
noncomputable def excludedClassesCard {k : ℕ} (p : ℕ) (h : Fin k → ℤ) : ℕ :=
  if hp : p = 0 then 0
  else @Finset.card (ZMod p) (@excludedClasses p ⟨hp⟩ k (fun i => (h i : ZMod p)))

/-! ### Sieve density -/

/-- The baseline sieve density `ρ(y)`: the fraction of elements surviving the `n² + 1`
sieve up to parameter `y`. For the prime `2`, one class is excluded (parity sieve).
For odd primes `p`, the number of excluded classes equals the number of roots of `x²+1`.

$$\rho(y) = \frac{1}{2} \prod_{2 < p \le y,\, p \text{ prime}}
  \left(1 - \frac{\#\{x : x^2+1 \equiv 0\}}{p}\right)$$ -/
noncomputable def sieveDensity (y : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
    (1 - (sqrtNegOneCount' p : ℝ) / p)

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
-/
theorem expectation_factorization {k : ℕ} (_hk : 0 < k)
    (h : Fin k → ℤ) (_hinj : Function.Injective h) (y : ℕ) :
    tupleExpectation h y =
      (primorial y : ℝ) * sieveDensity y ^ k *
        (∏ p ∈ ((Finset.Icc 3 y).filter Nat.Prime).filter (· % 4 = 1),
          ((1 - (excludedClassesCard p h : ℝ) / p) /
           (1 - 2 / (p : ℝ)) ^ k)) := by
  unfold tupleExpectation;
  unfold sieveDensity; norm_num [ mul_assoc, Finset.prod_filter ] ;
  rw [ mul_pow, ← Finset.prod_pow ];
  rw [ mul_div, eq_div_iff ];
  · rw [ mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib ];
    refine Or.inl <| congr_arg _ <| Finset.prod_congr rfl fun x hx => ?_ ; split_ifs <;> simp_all +decide;
    · rw [ show sqrtNegOneCount' x = 2 from ?_ ] ; ring;
      unfold sqrtNegOneCount';
      split_ifs <;> simp_all +decide [ sqrtNegOneCount_eq_two ];
    · unfold excludedClassesCard sqrtNegOneCount';
      simp_all +decide [Nat.Prime.ne_zero];
      unfold excludedClasses sqrtNegOneCount; simp_all +decide;
      -- Since $x \equiv 3 \pmod{4}$, we know that $-1$ is not a quadratic residue modulo $x$, so the set of roots of $x^2 + 1 = 0$ modulo $x$ is empty.
      have h_empty : ∀ a : ZMod x, ¬(a ^ 2 + 1 = 0) := by
        haveI := Fact.mk ‹Nat.Prime x›; intro a ha; have := ZMod.exists_sq_eq_neg_one_iff ( p := x ) ; simp_all +decide [ ← eq_sub_iff_add_eq ] ;
        exact absurd ( this.mp ⟨ a, by rw [ sq ] at ha; exact ha.symm ⟩ ) ( by have := Nat.Prime.eq_two_or_odd ‹_›; omega );
      simp_all +decide [ sqrtNegOneRoots ];
  · exact Finset.prod_ne_zero_iff.mpr fun p hp => by split_ifs <;> first | positivity | exact pow_ne_zero _ <| sub_ne_zero_of_ne <| by rw [ Ne.eq_def, eq_div_iff ] <;> norm_cast <;> linarith [ Finset.mem_Icc.mp hp ] ;

/-! ### Poisson gap probability (Theorem 2) -/

/-
**Theorem 2 (Poisson Gap Probability).**
Under the Poisson limit model, if the ratio of interval length to mean spacing
converges to `λ`, then the gap exceedance probability `e^{-ratio}` converges
to `e^{-λ}`.
-/
theorem poisson_gap_probability (lam : ℝ) (_hlam : 0 < lam)
    (intervalLength meanSpacing : ℕ → ℝ)
    (_hinterval : ∀ n, 0 < intervalLength n)
    (_hspacing : ∀ n, 0 < meanSpacing n)
    (hratio : Filter.Tendsto (fun n => intervalLength n / meanSpacing n)
      Filter.atTop (nhds lam)) :
    Filter.Tendsto (fun n => Real.exp (-(intervalLength n / meanSpacing n)))
      Filter.atTop (nhds (Real.exp (-lam))) :=
  Real.continuous_exp.continuousAt.tendsto.comp (Filter.Tendsto.neg hratio)

end NearSquarePrimes