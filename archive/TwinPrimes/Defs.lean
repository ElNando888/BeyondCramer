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
# Definitions for the Twin Prime Conjecture Poisson Model

Core definitions for the Poisson limit model for twin primes (primes `p` with `p + 2` prime),
adapting the Granville–Kurlberg framework to the linear sieve setting.

The twin prime sieve sieves by the polynomial `n(n + 2)`: an integer `n` can give rise to a
twin prime pair `(n, n + 2)` only if `n(n + 2)` has no small prime factor. For each prime `p`,
the residue classes excluded are those `n` with `p ∣ n(n + 2)`, namely `n ≡ 0` and
`n ≡ -2 (mod p)`.

## Main Definitions

* `TwinPrimes.twinRoots`: The roots of `x(x + 2) ≡ 0 (mod p)`.
* `TwinPrimes.excludedClasses`: The excluded residue classes for a `k`-tuple.
* `TwinPrimes.collisionThreshold`: The bound beyond which no collisions occur.
* `TwinPrimes.primorial`: The primorial `∏_{p ≤ y} p`.

## References

* [A. Granville, P. Kurlberg, *Poisson statistics via the Chinese remainder theorem*]
  [arXiv:math/0412135v2]
-/

open Finset BigOperators

namespace TwinPrimes

/-! ### Roots of x(x + 2) ≡ 0 (mod p) -/

/-- The set of solutions to `x * (x + 2) ≡ 0` in `ZMod p`. These are the residue classes
`n mod p` for which `p ∣ n(n + 2)`. -/
def twinRoots (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter fun x : ZMod p => x * (x + 2) = 0

/-- The number of solutions to `x * (x + 2) ≡ 0` in `ZMod p`. -/
def twinRootCount (p : ℕ) [NeZero p] : ℕ :=
  (twinRoots p).card

/-! ### Excluded residue classes for the twin prime sieve -/

/-- For a `k`-tuple of shifts `h`, the excluded residue classes mod `p`
are those `a ∈ ZMod p` such that `(a + hᵢ) * (a + hᵢ + 2) ≡ 0 (mod p)` for some shift `hᵢ`.
These are the values of `n` modulo `p` for which `(n + hᵢ)(n + hᵢ + 2)` is divisible by `p`. -/
def excludedClasses (p : ℕ) [NeZero p] {k : ℕ} (h : Fin k → ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun a : ZMod p =>
    ∃ i : Fin k, (a + h i) * (a + h i + 2) = 0

/-! ### Collision threshold -/

/-- The collision threshold for the twin prime sieve: the maximum of
`|hᵢ - hⱼ|`, `|hᵢ - hⱼ + 2|`, and `|hᵢ - hⱼ - 2|` over all pairs `(i, j)`.
For primes `p` exceeding this threshold, the excluded classes of distinct shifts
do not overlap, giving `|S_p(h)| = 2k`. -/
noncomputable def collisionThreshold {k : ℕ} (h : Fin k → ℤ) : ℕ :=
  Finset.sup (Finset.univ ×ˢ Finset.univ) fun ij : Fin k × Fin k =>
    max ((h ij.1 - h ij.2).natAbs)
      (max ((h ij.1 - h ij.2 + 2).natAbs) ((h ij.1 - h ij.2 - 2).natAbs))

/-! ### Primorial -/

/-- The primorial `q_y = ∏_{p ≤ y, p prime} p`. -/
noncomputable def primorial (y : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime, p

end TwinPrimes
