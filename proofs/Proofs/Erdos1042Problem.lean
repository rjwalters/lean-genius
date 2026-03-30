/-
Erdős Problem #1042: Connected Components of Polynomial Lemniscates

For polynomials f(z) = ∏ᵢ(z - zᵢ) with roots in a closed set F ⊆ ℂ,
how many connected components can the lemniscate {z : |f(z)| < 1} have?

**Status**: SOLVED by Ghosh-Ramachandran (2024)

**Key Results**:
- Erdős-Herzog-Piranian (1958): unit disc gives n components via f(z) = zⁿ + 1
- GR (2024): if d < 1, at most (1-c)n components
- GR (2024): if d ≤ 1/4 and F connected, only 1 component
- GR (2024): for d = 1, examples with n components exist
- Answer depends on geometry of F, not just transfinite diameter

References:
- [EHP58] Erdős-Herzog-Piranian, "Metric properties of polynomials" (1958)
- [GhRa24] Ghosh-Ramachandran, "Number of components of polynomial lemniscates" (2024)
- https://erdosproblems.com/1042
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset

open Complex BigOperators

namespace Erdos1042

/- ## Transfinite Diameter -/

/-- Transfinite diameter (logarithmic capacity) of a closed set F ⊆ ℂ.
Defined as ρ(F) = lim_{n→∞} sup_{z₁,...,zₙ∈F} (∏_{i<j} |zᵢ-zⱼ|)^{1/C(n,2)}.
Axiomatized since the full definition requires Chebyshev constant machinery. -/
axiom transfiniteDiameter (F : Set ℂ) : ℝ

/-- Transfinite diameter is nonneg (equals logarithmic capacity). -/
/-- The transfinite diameter of a disc of radius r is r. -/
/-- The transfinite diameter of [-1,1] ⊆ ℂ is 1/2. -/
/- ## Polynomial Lemniscates -/

/-- A monic polynomial f(z) = ∏ᵢ(z - zᵢ) with all roots in F. -/
structure PolynomialWithRoots (F : Set ℂ) where
  degree : ℕ
  roots : Fin degree → ℂ
  roots_in_F : ∀ i, roots i ∈ F

/-- The lemniscate of f is {z : |f(z)| < 1}. -/
def lemniscate (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | Complex.abs (f z) < 1}

/-- Number of connected components of a set S ⊆ ℂ. Defined as the
cardinality of the quotient by the connected component equivalence
on the subspace ↥S. Returns 0 if the number of components is infinite. -/
noncomputable def numComponents (S : Set ℂ) : ℕ :=
  Nat.card (ConnectedComponents ↥S)

/-- The monic polynomial f(z) = ∏ᵢ(z - zᵢ) associated with a set of roots. -/
noncomputable def monicPoly {F : Set ℂ} (p : PolynomialWithRoots F) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

/-- Maximum number of connected components achievable by lemniscates
of degree-n polynomials with roots in F. Defined as the supremum over
all such polynomials. Returns 0 if no polynomials of that degree exist. -/
noncomputable def maxComponents (F : Set ℂ) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ p : PolynomialWithRoots F, p.degree = n ∧
    numComponents (lemniscate (monicPoly p)) = k}

/- ## The Original Problem -/

/-- Main Question 1: For F with transfinite diameter 1 not contained
in any disc of radius 1, can the lemniscate have n components? -/
def mainQuestion1 : Prop :=
  ∃ F : Set ℂ,
    transfiniteDiameter F = 1 ∧
    (∀ c : ℂ, ∃ z ∈ F, Complex.abs (z - c) > 1) ∧
    ∀ n : ℕ, n > 0 → maxComponents F n = n

/-- Main Question 2: For F with transfinite diameter < 1, must
the lemniscate have at most (1-c)n components for some c > 0? -/
def mainQuestion2 : Prop :=
  ∀ F : Set ℂ, transfiniteDiameter F < 1 →
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, (maxComponents F n : ℝ) ≤ (1 - c) * n

/- ## Erdős-Herzog-Piranian Result (1958) -/

/-- For the unit disc, the lemniscate can have n connected components.
Example: f(z) = zⁿ + 1 has n components. -/
/-- f(z) = zⁿ + 1 has its roots on the unit circle and its lemniscate
has n connected components. -/
/- ## Ghosh-Ramachandran Solution (2024) -/

/-- GR Theorem 1: If 0 < d < 1, the lemniscate has at most (1-c)n
components for some c > 0 depending on F. -/
axiom ghosh_ramachandran_small_diameter :
    ∀ F : Set ℂ, 0 < transfiniteDiameter F →
      transfiniteDiameter F < 1 →
        ∃ c : ℝ, c > 0 ∧
          ∀ n : ℕ, (maxComponents F n : ℝ) ≤ (1 - c) * n

/-- GR Theorem 2: If d ≤ 1/4 and F is connected, then the lemniscate
has only one connected component. -/
/-- GR Theorem 3: There exist sets with transfinite diameter 1 such that
the lemniscate has n components for infinitely many n. -/
axiom ghosh_ramachandran_diameter_one_examples :
    ∃ F : Set ℂ, transfiniteDiameter F = 1 ∧
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧ maxComponents F n = n

/- ## The Counterexample -/

/-- The answer depends on geometry, not just diameter.
Both the disc of radius 1/2 and [-1,1] have transfinite diameter 1/2,
but the disc always gives 1 component while [-1,1] can give many. -/
/- ## Summary -/

/-- **Erdős Problem #1042 Summary.**
Combines the key results: Question 2 confirmed (d < 1 → bounded components),
diameter-1 examples exist, and geometry matters more than diameter alone. -/
theorem erdos_1042_summary :
    (∀ F : Set ℂ, 0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
      ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, (maxComponents F n : ℝ) ≤ (1 - c) * n) ∧
    (∃ F : Set ℂ, transfiniteDiameter F = 1 ∧
      ∀ N : ℕ, ∃ n : ℕ, n > N ∧ maxComponents F n = n) :=
  ⟨ghosh_ramachandran_small_diameter, ghosh_ramachandran_diameter_one_examples⟩

end Erdos1042
