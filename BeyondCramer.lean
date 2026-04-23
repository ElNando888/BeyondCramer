/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

/-
PROVIDED SOLUTION

### Aristotle Prompt: Closing the Loop (BeyondCramer ↔ PoissonViaCRT)

The `BeyondCramer` refactor successfully established the algebraic expectation factorization, but
it is currently disconnected from the core analytic results of the Granville-Kurlberg (GK08)
formalization. To finalize the 'Beyond Cramér' unified theory, you must formally link the
`PoissonAdmissibleSieve` class to the `PoissonViaCRT` theorems.

#### 1. Import and Dependency
In `BeyondCramer/GrandConvergence.lean`, add the following import:
* `import PoissonViaCRT.MainTheorem` 

#### 2. The Bridge Lemma: `is_well_distributed`
Implement a lemma in `BeyondCramer/GrandConvergence.lean` that bridges the two frameworks:
* **The Goal:** Prove that any instance of `PoissonAdmissibleSieve` satisfies the `WellDistributed`
  hypothesis used in the `PoissonViaCRT` root.
* **Logic:** Use the `correlation_bound` and `correlation_summable` properties of the class to show
  that the local error terms $\epsilon_k$ satisfy the vanishing conditions required by GK08.

#### 3. Formalizing the Poisson Limit
Prove the **Unified Poisson Spacing Theorem** in `BeyondCramer/GrandConvergence.lean`:
* **The Theorem:** For any `PoissonAdmissibleSieve`, the normalized spacings between surviving
  residues converge to a Poisson distribution as the spacing parameter $s_q \to \infty$.
* **Implementation:** Invoke `PoissonCRT.mainTheorem_precise` (Theorem 3.7) to show that the
  $k$-level correlation $R_k(X, \Omega_q)$ converges to the volume of the box $X$.

#### 4. Finalizing Instances
Update the corollaries in the `TwinPrimes` and `NearSquarePrimes` instance files:
* Ensure that `twinPrime_geometric_pos` and `nearSquare_geometric_pos` are used to satisfy the
  non-zero limit requirements of the GK08 main theorem.

#### Requirements
* **Standard Verification:** The newly generated code must be entirely free of `sorry` blocks.
* **Namespace Consistency:** Maintain all unified results under the `PoissonAdmissibleSieve`
  namespace to ensure they are available as corollaries for any future sieve implementations.

-/

import BeyondCramer.Defs
import BeyondCramer.Utils
import BeyondCramer.GrandConvergence
import BeyondCramer.InstanceTwinPrimes
import BeyondCramer.InstanceNearSquarePrimes
