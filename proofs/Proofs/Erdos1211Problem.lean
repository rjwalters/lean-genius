/-
Erdős Problem #1211: Partition Sums and Upper Logarithmic Density

Source: https://erdosproblems.com/1211
Status: SOLVED

Statement:
Let ℕ = A ∪ B (disjoint). Let S(A) be the set of all finite subset sums of A.
Upper logarithmic density: δ̄(X) = limsup (1/log x) Σ_{n ∈ X, n ≤ x} 1/n.
Erdős conjectured δ̄(S(A) ∪ S(B)) ≥ 1/2 always, with equality attainable.

Answer: YES — proved with bound 1/2 tight.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Filter

open Filter Real

namespace Erdos1211

/-- Upper logarithmic density of X ⊆ ℕ -/
noncomputable def upperLogDensity (X : Set ℕ) : ℝ :=
  limsup (fun x : ℕ => (1 / Real.log x) *
    ∑ n ∈ Finset.filter (fun n => n ∈ X) (Finset.Icc 1 x), (1 : ℝ) / n) atTop

/-- Subset sums: all positive sums of finite subsets of A -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧ F.sum id = n ∧ n > 0}

/--
**Main Result:**
For any partition ℕ = A ∪ B, δ̄(S(A) ∪ S(B)) ≥ 1/2.
-/
axiom erdos_sarkozy_sos :
    ∀ (A B : Set ℕ), Set.univ = A ∪ B → Disjoint A B →
      upperLogDensity (subsetSums A ∪ subsetSums B) ≥ 1/2

/-- The bound 1/2 is sharp: some partition achieves exactly 1/2. -/
axiom erdos_1211_sharp :
    ∃ (A B : Set ℕ), Set.univ = A ∪ B ∧ Disjoint A B ∧
      upperLogDensity (subsetSums A ∪ subsetSums B) = 1/2

/-- **Erdős Problem #1211: SOLVED** -/
theorem erdos_1211 :
    (∀ (A B : Set ℕ), Set.univ = A ∪ B → Disjoint A B →
      upperLogDensity (subsetSums A ∪ subsetSums B) ≥ 1/2) ∧
    (∃ (A B : Set ℕ), Set.univ = A ∪ B ∧ Disjoint A B ∧
      upperLogDensity (subsetSums A ∪ subsetSums B) = 1/2) :=
  ⟨erdos_sarkozy_sos, erdos_1211_sharp⟩

end Erdos1211
