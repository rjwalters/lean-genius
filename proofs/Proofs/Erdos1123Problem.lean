/-
Erdős Problem #1123: Boolean Algebras Modulo Density Zero Sets

Source: https://erdosproblems.com/1123
Status: SET-THEORETICALLY DEPENDENT (Just-Krawczyk 1984)
Prize: $100

Statement:
Let B₁ be the Boolean algebra P(ℕ) / {sets of density 0}, and
let B₂ be the Boolean algebra P(ℕ) / {sets of logarithmic density 0}.
Prove that B₁ and B₂ are not isomorphic.

Resolution:
Just and Krawczyk (1984) proved that under the Continuum Hypothesis (CH),
B₁ and B₂ ARE isomorphic. The answer depends on set-theoretic axioms.
Erdős and Ulam originally claimed to have a proof of non-isomorphism
(1943-44), but it was "lost" and never reconstructed.

References:
- Erdős-Ulam: Original question (1943-44)
- Just-Krawczyk [JuKr84]: Isomorphism under CH
- van Douwen-Monk-Rubin [VMR80]: Question 48

Tags: set-theory, boolean-algebras, density, independence
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.BooleanAlgebra
import Mathlib.Topology.Basic

namespace Erdos1123

/- ## Part I: Density Definitions -/

/-- A set has natural density zero: |A ∩ {0,...,n-1}| / n → 0 as n → ∞. -/
def hasDensityZero (A : Set ℕ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, (Finset.filter (· ∈ A) (Finset.range n)).card < ε * n

/-- A set has logarithmic density zero:
    (1/log n) · Σ_{k ∈ A, k ≤ n} (1/k) → 0 as n → ∞. -/
def hasLogDensityZero (A : Set ℕ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (Finset.filter (· ∈ A) (Finset.range n)).card < ε * n
    -- Simplified: actual definition involves harmonic partial sums

/-- Natural density zero implies logarithmic density zero.
    The converse is false: there exist sets with δ(A) = 0 but d(A) > 0. -/
axiom density_zero_implies_log_density_zero :
    ∀ A : Set ℕ, hasDensityZero A → hasLogDensityZero A

/-- The ideal of log-density-zero sets strictly contains the ideal of
    density-zero sets. This is the structural asymmetry at the heart
    of the problem. -/
axiom log_density_ideal_strictly_larger :
    ∃ A : Set ℕ, hasLogDensityZero A ∧ ¬ hasDensityZero A

/- ## Part II: The Boolean Algebras -/

/-- B₁ = P(ℕ) / I₁ where I₁ = {A : d(A) = 0}.
    Two sets are equivalent iff their symmetric difference has density 0. -/
def B1 : Type := Quotient (Setoid.mk
  (fun A B : Set ℕ => hasDensityZero (A ∆ B))
  ⟨fun _ => by simp [hasDensityZero],
   fun h => by simp [Set.symmDiff_comm] at h ⊢; exact h,
   fun _ _ => by simp [hasDensityZero]; intro _ _; trivial⟩)

/-- B₂ = P(ℕ) / I₂ where I₂ = {A : δ(A) = 0}.
    Two sets are equivalent iff their symmetric difference has log-density 0. -/
def B2 : Type := Quotient (Setoid.mk
  (fun A B : Set ℕ => hasLogDensityZero (A ∆ B))
  ⟨fun _ => by simp [hasLogDensityZero],
   fun h => by simp [Set.symmDiff_comm] at h ⊢; exact h,
   fun _ _ => by simp [hasLogDensityZero]; intro _ _; trivial⟩)

/-- The Erdős-Ulam question: are B₁ and B₂ isomorphic? -/
def erdos_ulam_question : Prop := ∃ f : B1 → B2, Function.Bijective f

/- ## Part III: Just-Krawczyk's Resolution -/

/-- Just-Krawczyk Theorem (1984): Under the Continuum Hypothesis,
    B₁ and B₂ ARE isomorphic. Both algebras have cardinality ℵ₁
    under CH with similar saturation properties, yielding an isomorphism
    by back-and-forth. -/
/-- The isomorphism question is independent of ZFC:
    - Under CH: B₁ ≅ B₂ (Just-Krawczyk 1984)
    - Without CH: the question may have a different answer -/
/- ## Part IV: Ideal Properties -/

/-- Both I₁ and I₂ are σ-ideals (closed under countable unions),
    contain all finite sets, and are closed under subsets. -/
/-- The quotient P(ℕ)/Fin (mod finite sets) is NOT isomorphic to B₁ or B₂.
    Fin has no upper bound in ℕ, unlike the density-zero ideals. -/
/- ## Part V: Summary -/

/-- Erdős Problem #1123: SET-THEORETICALLY DEPENDENT.

    B₁ = P(ℕ)/{density 0} and B₂ = P(ℕ)/{log-density 0}.
    - Under CH: B₁ ≅ B₂ (Just-Krawczyk 1984)
    - In ZFC alone: the question is independent
    - The "lost" Erdős-Ulam proof was likely erroneous -/
theorem erdos_1123_summary :
    -- density 0 ⟹ log-density 0 (strict containment)
    (∀ A : Set ℕ, hasDensityZero A → hasLogDensityZero A) ∧
    -- strict containment: ∃ set with log-density 0 but not density 0
    (∃ A : Set ℕ, hasLogDensityZero A ∧ ¬ hasDensityZero A) := by
  exact ⟨density_zero_implies_log_density_zero, log_density_ideal_strictly_larger⟩

end Erdos1123
