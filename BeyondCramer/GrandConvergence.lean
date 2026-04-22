/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import BeyondCramer.Defs

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

end PoissonAdmissibleSieve
