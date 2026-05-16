# Beyond Cramér: A unified Poisson limit framework

This repository contains the Lean 4 formalization for the mathematical paper **"Beyond Cramér: A unified Poisson limit framework for prime-representing sieve spacings"** by Fernando Portela (Ronin Institute for Independent Scholarship 2.0).

## Overview

The formalization establishes a unified geometric framework that reduces the probabilistic distribution of prime-representing sieves to deterministic modular intersections. By formalizing a class of bounded-variance, multi-residue sieves, it proves that Poisson-distributed spacings are a necessary consequence of local geometric correlation.

This unified theory resolves the transition from sieves with constant dimensions, such as the twin prime sieve ($x(x+2)$), to sieves with fluctuating dimensions governed by the Legendre symbol, such as Landau's First Problem ($n^2+1$). 

At the core of the repository is a machine-verified **Grand Convergence Theorem**, proving that any multi-residue sieve satisfying the collision threshold axioms admits a factorization of the $k$-tuple expectation into a single-event density and an absolutely convergent geometric correlation constant.

## Repository Structure

- `BeyondCramer/`: The Lean 4 formalization source code.
  - `Defs.lean`: Core abstractions, defining the `PoissonAdmissibleSieve` class and geometric convergence properties.
  - `GrandConvergence.lean`: The Grand Convergence Theorem establishing the unified expectation factorization and bridging to the Poisson limits.
  - `InstanceTwinPrimes.lean`: The Poisson-admissible sieve instance for the Twin Prime Conjecture.
  - `InstanceNearSquarePrimes.lean`: The Poisson-admissible sieve instance for Landau's First Problem (primes of the form $n^2+1$).
- `manuscript/`: Contains the LaTeX source code for the associated manuscript (`beyondcramer.tex`).

## Dependencies

This project is built using Lean 4 and depends on:
* **[mathlib4](https://github.com/leanprover-community/mathlib4)** (v4.28.0)
* **[PoissonViaCRT](https://github.com/ElNando888/PoissonViaCRT)**: Provides the underlying Poisson statistics via the Chinese Remainder Theorem, based on the Granville-Kurlberg 2008 paper. 
  > *Note:* Due to current limitations in the `RiemannHypothesisCurves` library (a slightly edited fork of a formalization by Math-Inc) regarding the general Hasse-Weil bound, `PoissonViaCRT` is restricted to bounding polynomials of degree $\le 2$. This perfectly accommodates our applications to twin primes and near-square primes, which exclude at most 2 residue classes per prime.

## Building

To build the Lean project, ensure you have Lean 4 and `lake` installed (we recommend using [`elan`](https://github.com/leanprover/elan)), and run:

```bash
lake build
```
