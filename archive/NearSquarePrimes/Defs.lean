/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Prime.Defs

/-!
# Definitions for Landau's First Problem (Primes of the form n² + 1)

Core definitions for the Poisson limit model for primes of the form `n² + 1`,
adapting the Granville–Kurlberg framework to the quadratic sieve setting.

## Main Definitions

* `NearSquarePrimes.sqrtNegOneRoots`: The roots of `x² ≡ -1 (mod p)`.
* `NearSquarePrimes.excludedClasses`: The excluded residue classes for a `k`-tuple.
* `NearSquarePrimes.collisionThreshold`: The bound `P(h)` beyond which no collisions occur.
* `NearSquarePrimes.primorial`: The primorial `∏_{p ≤ y} p`.

## References

* Portela, F. (2026). *A Poisson Limit Model for Landau's First Problem via
  Bounded-Variance Multi-Residue Sieves*.
* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators

namespace NearSquarePrimes

/-! ### Quadratic roots of x² ≡ -1 (mod p) -/

/-- The set of solutions to `x² + 1 ≡ 0` in `ZMod p`. Requires `p ≠ 0` so that
`ZMod p` is finite. -/
def sqrtNegOneRoots (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter fun x : ZMod p => x ^ 2 + 1 = 0

/-- The number of solutions to `x² + 1 ≡ 0` in `ZMod p`. -/
def sqrtNegOneCount (p : ℕ) [NeZero p] : ℕ :=
  (sqrtNegOneRoots p).card

/-! ### Excluded residue classes for the n² + 1 sieve -/

/-- For a `k`-tuple of shifts `h`, the excluded residue classes mod `p`
are those `a ∈ ZMod p` such that `(a + hᵢ)² + 1 ≡ 0 (mod p)` for some shift `hᵢ`.
These are the values of `n` modulo `p` for which `(n + hᵢ)² + 1` is divisible by `p`. -/
def excludedClasses (p : ℕ) [NeZero p] {k : ℕ} (h : Fin k → ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun a : ZMod p =>
    ∃ i : Fin k, (a + h i) ^ 2 + 1 = 0

/-! ### Collision threshold -/

/-- The collision threshold `P(h)`: the maximum of `(hᵢ - hⱼ)² + 4` over all pairs,
including `i = j`. For primes `p > P(h)` with `p ≡ 1 (mod 4)`, the excluded classes of
distinct shifts do not overlap, giving `|S_p(h)| = 2k`.

Note: when `i = j`, the summand is `4`, so `P(h) ≥ 4` for any tuple of length ≥ 1.
The relevant bound is that for `i ≠ j` and prime `p > (hᵢ - hⱼ)² + 4`, neither
`p ∣ (hᵢ - hⱼ)` nor `p ∣ ((hᵢ - hⱼ)² + 4)` can hold. -/
noncomputable def collisionThreshold {k : ℕ} (h : Fin k → ℤ) : ℕ :=
  Finset.sup (Finset.univ ×ˢ Finset.univ) fun ij : Fin k × Fin k =>
    ((h ij.1 - h ij.2) ^ 2 + 4).natAbs

/-! ### Primorial -/

/-- The primorial `q_y = ∏_{p ≤ y, p prime} p`. -/
noncomputable def primorial (y : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime, p

end NearSquarePrimes
