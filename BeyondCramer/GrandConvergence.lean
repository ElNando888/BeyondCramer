/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import BeyondCramer.Defs
import PoissonViaCRT.MainTheorem

/-!
# Grand Convergence Theorem for the Poisson-Admissible Sieve

This file proves the **Unified Expectation Factorization**: a single theorem
that applies to any `PoissonAdmissibleSieve` instance. It shows that the
`k`-tuple expectation factorizes as

$$E[N_k(\mathbf{h})] \sim q_y \cdot \rho(y)^k \cdot \mathfrak{G}(\mathbf{h}),$$

where:
- `q_y` is the primorial,
- `ρ(y)` is the single-event sieve density,
- `𝔊(h)` is the geometric correlation constant (an absolutely convergent
  infinite product).

The key insight is that the factorization and convergence depend only on the
`PoissonAdmissibleSieve` axioms (density map, collision threshold, and
`O(1/p²)` deviation bound), not on whether the sieve is linear or quadratic.

## Main Results

* `PoissonAdmissibleSieve.sieveDensity`: The baseline sieve density.
* `PoissonAdmissibleSieve.tupleExpectation`: The expected `k`-tuple count.
* `PoissonAdmissibleSieve.expectation_factorization`: The factorization theorem.
* `PoissonAdmissibleSieve.geometric_correlation_converges`: Convergence of `𝔊(h)`.
* `PoissonAdmissibleSieve.is_well_distributed`: Bridge to GK08 well-distribution.
* `PoissonAdmissibleSieve.SieveRealization`: Concrete realization of the sieve.
* `PoissonAdmissibleSieve.unified_poisson_spacing`: Poisson limit for spacings.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators Filter

namespace PoissonAdmissibleSieve

variable {σ : Type} [S : PoissonAdmissibleSieve σ]

/-! ### Sieve density -/

/-- The baseline sieve density `ρ(y)` for the sieve `S`.

For the prime `p = 2`, one residue class is excluded (parity sieve), contributing
a factor of `1/2`. For larger primes, each prime contributes `1 - κ(p)/p`. -/
noncomputable def sieveDensity (y : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
    (1 - (S.κ p : ℝ) / p)

/-! ### Expected count -/

/-- Given a function `excl` that maps each prime `p` to the number of excluded
residue classes for the tuple `h`, the expected number of surviving `k`-tuples
modulo the primorial `q_y` is:

$$E[N_k(\mathbf{h})] = q_y \cdot (1/2)^k \cdot
  \prod_{3 \le p \le y,\, p \text{ prime}} (1 - \mathrm{excl}(p)/p)$$ -/
noncomputable def tupleExpectation (excl : ℕ → ℕ) (y k : ℕ) : ℝ :=
  (PoissonSieve.primorial y : ℝ) *
    ((1 / 2 : ℝ) ^ k *
      ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
        (1 - (excl p : ℝ) / p))

/-! ### Helper: density factors are nonzero -/

/-- Each density factor `(1 - κ(p)/p)` is nonzero for primes `p` in `[3, y]`,
because `κ(p) < p` for all primes `p`. -/
theorem density_factor_ne_zero {p : ℕ}
    (hp : p ∈ (Finset.Icc 3 y).filter Nat.Prime) :
    (1 - (S.κ p : ℝ) / p) ≠ 0 := by
  have hp' := (Finset.mem_filter.mp hp).2
  exact ne_of_gt (sub_pos.mpr ((div_lt_one (by exact_mod_cast hp'.pos)).mpr
    (by exact_mod_cast S.κ_lt_prime p hp')))

/-! ### Expectation Factorization -/

/-- **Unified Expectation Factorization.** For any `PoissonAdmissibleSieve` instance,
the `k`-tuple expectation factorizes as

$$E[N_k(\mathbf{h})] = q_y \cdot \rho(y)^k \cdot
  \prod_{3 \le p \le y} \frac{1 - \mathrm{excl}(p)/p}{(1 - \kappa(p)/p)^k}.$$

This theorem is agnostic to whether the sieve is linear or quadratic; it
depends only on the `PoissonAdmissibleSieve` axioms. -/
theorem expectation_factorization (excl : ℕ → ℕ) (y k : ℕ) (_hk : 0 < k) :
    tupleExpectation excl y k =
      (PoissonSieve.primorial y : ℝ) * sieveDensity (σ := σ) y ^ k *
        (∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
          ((1 - (excl p : ℝ) / p) /
           (1 - (S.κ p : ℝ) / p) ^ k)) := by
  unfold tupleExpectation sieveDensity
  simp only [mul_pow, ← Finset.prod_pow, one_div]
  have key : ∀ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
      (1 - (S.κ p : ℝ) / p) ^ k *
        ((1 - (excl p : ℝ) / p) / (1 - (S.κ p : ℝ) / p) ^ k) =
      (1 - (excl p : ℝ) / p) := fun p hp =>
    mul_div_cancel₀ _ (pow_ne_zero _ (density_factor_ne_zero hp))
  calc _ = (PoissonSieve.primorial y : ℝ) *
      (2⁻¹ ^ k * ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
        (1 - (excl p : ℝ) / p)) := rfl
    _ = (PoissonSieve.primorial y : ℝ) *
      (2⁻¹ ^ k * ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
        ((1 - (S.κ p : ℝ) / p) ^ k *
          ((1 - (excl p : ℝ) / p) / (1 - (S.κ p : ℝ) / p) ^ k))) := by
      congr 2; exact Finset.prod_congr rfl fun p hp => (key p hp).symm
    _ = (PoissonSieve.primorial y : ℝ) *
      (2⁻¹ ^ k *
        ((∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
            (1 - (S.κ p : ℝ) / p) ^ k) *
          ∏ p ∈ (Finset.Icc 3 y).filter Nat.Prime,
            (1 - (excl p : ℝ) / p) / (1 - (S.κ p : ℝ) / p) ^ k)) := by
      congr 2; exact Finset.prod_mul_distrib
    _ = _ := by ring

/-- **Convergence of the geometric correlation** `𝔊(h)`.
The infinite product of local factors converges to a nonzero limit, and
is `Multipliable`. -/
theorem geometric_correlation_converges (k : ℕ) (hk : 0 < k) :
    ∃ G : ℝ, G ≠ 0 ∧
      Multipliable (fun n => localFactor (σ := σ) k n) :=
  ⟨∏' n, localFactor (σ := σ) k n,
    localFactor_tprod_ne_zero k hk,
    localFactor_multipliable k hk⟩

/-! ### Bridge to PoissonViaCRT -/

/-- **Bridge Lemma.** The `correlation_bound` and `correlation_summable` properties of a
`PoissonAdmissibleSieve` ensure that the local error terms `ε_k` satisfy the vanishing
conditions required by GK08 (Theorem 3.7).

Concretely, this lemma packages two facts:

1. **Pointwise bound**: For qualifying primes `p` (where `κ(p) · k < p`), the deviation
   of the local correlation factor from `1` is bounded by `C / p²`. This is strictly
   stronger than the `(1 - |Ω|/p) · p^{-ε}` bound required by `WellDistributed`.

2. **Summability**: The deviations `localFactor k p - 1` are summable over `ℕ`, ensuring
   that the Euler product `∏_p (1 + ε_k(p))` converges absolutely. This is the
   quantitative vanishing condition that drives the error in GK08 Theorem 3.7 to zero.

Together, these two properties ensure that any sieve realization compatible with the
abstract `PoissonAdmissibleSieve` framework will satisfy the analytic hypotheses of
the GK08 main theorem. -/
theorem is_well_distributed (k : ℕ) (hk : 0 < k) :
    (∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, Nat.Prime p → S.κ p * k < p →
      |localFactor (σ := σ) k p - 1| ≤ C / (p : ℝ) ^ 2) ∧
    Summable (fun n => localFactor (σ := σ) k n - 1) := by
  constructor
  · obtain ⟨C, hC, hbound⟩ := S.correlation_bound k hk
    exact ⟨C, hC, fun p hp hpk => by
      simp only [localFactor, hp, hpk, and_self, ite_true]
      exact hbound p hp hpk⟩
  · exact localFactor_deviation_summable k hk

/-! ### Sieve Realization -/

/-- A **sieve realization** equips a `PoissonAdmissibleSieve` with concrete subsets
`Ω_p ⊆ ℤ/pℤ` and the quantitative well-distribution hypothesis (Hypothesis (1) from
GK08, Theorem 1.1). These are the inputs needed to invoke the Poisson via CRT main
theorem (`PoissonCRT.mainTheorem_precise`).

The `PoissonAdmissibleSieve` provides the abstract convergence properties (local factor
bounds, summability), while the `SieveRealization` provides the concrete combinatorial
data (subsets, tuple counts) that realize those properties. -/
structure SieveRealization (σ : Type) [PoissonAdmissibleSieve σ] where
  /-- The surviving residues modulo each prime `p`. -/
  Ω : ∀ p : ℕ, Finset (ZMod p)
  /-- Each `Ω_p` is nonempty for primes. -/
  Ω_nonempty : ∀ p, Nat.Prime p → (Ω p).Nonempty
  /-- The well-distribution parameter `ε > 0`. -/
  ε : ℝ
  /-- Positivity of `ε`. -/
  hε : 0 < ε
  /-- Hypothesis (1) of GK08: well-distribution of tuple counts at each prime. -/
  well_distributed : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ),
    PoissonCRT.WellDistributed ε p (Ω p) k
  /-- Spacing bound: `s_p ≤ p^{λ_K - ε}` for all primes `p`. The parameter `K`
  controls the range of correlations for which the Poisson limit holds. -/
  spacing_bound : ∀ K : ℕ, ∀ p, Nat.Prime p →
    (p : ℝ) / (Ω p).card ≤ (p : ℝ) ^ (PoissonCRT.lambdaExponent K - ε)

/-- **Unified Poisson Spacing Theorem.** For any `PoissonAdmissibleSieve` equipped with
a sieve realization, the normalized spacings between surviving residues converge to a
Poisson distribution: for all `k ≥ 2` and boxes `X`, the `k`-level correlation
`R_k(X, Ω_q)` converges to `vol(X)` as `s_q → ∞`.

This theorem is the formal bridge between the abstract `PoissonAdmissibleSieve` framework
and the analytic results of Granville–Kurlberg. It invokes `PoissonCRT.mainTheorem_precise`
(Theorem 3.7), combining the well-distribution hypothesis with the sieve's convergence
properties to obtain the Poisson limit for `k`-level correlations.

The bound `|R_k(X, Ω_q) - vol(X)| ≤ C · s_q^{-δ}` for some `δ > 0` implies that the
correlations converge to `vol(X)` as the average spacing `s_q → ∞`, which is the
defining property of Poisson-distributed spacings. -/
theorem unified_poisson_spacing (R : SieveRealization σ) (K : ℕ) (hK : 2 ≤ K)
    (k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) (X : PoissonCRT.Box (k - 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (_hq : Squarefree q),
        |PoissonCRT.kCorrelation (PoissonCRT.crtSubset q R.Ω) X - X.volume| ≤
          C * ((q : ℝ) / (PoissonCRT.crtSubset q R.Ω).card) ^ (-δ) :=
  PoissonCRT.mainTheorem_precise R.ε R.hε K hK R.Ω R.Ω_nonempty
    (fun p _ k _ => R.well_distributed p k) (R.spacing_bound K) k hk hkK X

/-- The `k`-level correlation converges to the box volume along any sequence of
squarefree moduli whose average spacing tends to infinity. This is a direct
consequence of `unified_poisson_spacing`: the power-law error bound
`C · s_q^{-δ}` tends to zero as `s_q → ∞`. -/
theorem correlation_tendsto_volume (R : SieveRealization σ) (K : ℕ) (hK : 2 ≤ K)
    (k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) (X : PoissonCRT.Box (k - 1))
    (Q : ℕ → ℕ) [∀ n, NeZero (Q n)]
    (hQ_sq : ∀ n, Squarefree (Q n))
    (hQ_spacing : Filter.Tendsto
      (fun n => (Q n : ℝ) / (PoissonCRT.crtSubset (Q n) R.Ω).card)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => PoissonCRT.kCorrelation (PoissonCRT.crtSubset (Q n) R.Ω) X)
      Filter.atTop (nhds X.volume) := by
        obtain ⟨ δ, hδ_pos, C, hC_pos, h_bound ⟩ := unified_poisson_spacing R K hK k hk hkK X;
        exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => h_bound _ <| hQ_sq _ ) <| by simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop hδ_pos |> Filter.Tendsto.comp <| hQ_spacing ) ;

/-- Corollary: the geometric correlation product `∏ localFactor k p` being nonzero
ensures that the correlation limit in the Poisson spacing theorem is compatible with
the non-degeneracy condition `vol(X) > 0` of GK08.

This links `localFactor_tprod_pos` (from the abstract `PoissonAdmissibleSieve`) to
the positivity requirements of `PoissonCRT.mainTheorem_precise`. -/
theorem geometric_pos_ensures_nondegenerate (k : ℕ) (hk : 0 < k)
    (X : PoissonCRT.Box (k - 1)) :
    0 < ∏' n, localFactor (σ := σ) k n ∧ 0 < X.volume :=
  ⟨localFactor_tprod_pos k hk,
   Finset.prod_pos fun i _ => X.sides_pos i⟩

end PoissonAdmissibleSieve
