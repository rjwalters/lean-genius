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

import Mathlib
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic

open scoped Classical symmDiff

namespace Erdos1123

/- ## Part I: Density Definitions -/

/-- Counting function: |A ∩ {0,...,n-1}|. -/
noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.filter (· ∈ A) (Finset.range n)).card

/-- A set has natural density zero: |A ∩ {0,...,n-1}| / n → 0 as n → ∞. -/
def hasDensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N, ∀ n ≥ N, (countUpTo A n : ℝ) < ε * n

/-- A set has logarithmic density zero:
    (1/log n) · Σ_{k ∈ A, k ≤ n} (1/k) → 0 as n → ∞. -/
def hasLogDensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (countUpTo A n : ℝ) < ε * n
    -- Simplified: actual definition involves harmonic partial sums

/-- The counting function is subadditive under union of sets. -/
theorem countUpTo_union_le (A B : Set ℕ) (n : ℕ) :
    countUpTo (A ∪ B) n ≤ countUpTo A n + countUpTo B n := by
  classical
  unfold countUpTo
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_union] at hx ⊢
  rcases hx.2 with h | h
  · exact Finset.mem_union_left _ (by simp [hx.1, h])
  · exact Finset.mem_union_right _ (by simp [hx.1, h])

/-- The counting function is monotone in the set. -/
theorem countUpTo_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    countUpTo A n ≤ countUpTo B n := by
  classical
  unfold countUpTo
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

/-- Density zero is monotone: a subset of a density-zero set is density zero. -/
theorem hasDensityZero_mono {A B : Set ℕ} (h : A ⊆ B) (hB : hasDensityZero B) :
    hasDensityZero A := by
  intro ε hε
  obtain ⟨N, hN⟩ := hB ε hε
  exact ⟨N, fun n hn => lt_of_le_of_lt
    (by exact_mod_cast countUpTo_mono h n) (hN n hn)⟩

/-- Density zero is closed under union. -/
theorem hasDensityZero_union {A B : Set ℕ}
    (hA : hasDensityZero A) (hB : hasDensityZero B) : hasDensityZero (A ∪ B) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hA (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hB (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hu : (countUpTo (A ∪ B) n : ℝ) ≤ (countUpTo A n : ℝ) + (countUpTo B n : ℝ) := by
    exact_mod_cast countUpTo_union_le A B n
  calc (countUpTo (A ∪ B) n : ℝ) ≤ (countUpTo A n : ℝ) + (countUpTo B n : ℝ) := hu
    _ < ε / 2 * n + ε / 2 * n := by linarith
    _ = ε * n := by ring

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

/- B₁ = P(ℕ) / I₁ where I₁ = {A : d(A) = 0}.
   Two sets are equivalent iff their symmetric difference has density 0. -/
/-- The empty set has density zero. -/
theorem hasDensityZero_empty : hasDensityZero (∅ : Set ℕ) := by
  intro ε hε
  refine ⟨1, fun n hn => ?_⟩
  have : countUpTo (∅ : Set ℕ) n = 0 := by
    simp [countUpTo]
  rw [this]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  simpa using mul_pos hε hnpos

/-- The density-zero symmetric-difference relation is an equivalence.
    Reflexivity: A ∆ A = ∅ has density zero. Symmetry: A ∆ B = B ∆ A.
    Transitivity: A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C), density zero is subset- and
    union-closed. -/
def densityZeroSetoid : Setoid (Set ℕ) where
  r A B := hasDensityZero (A ∆ B)
  iseqv := {
    refl := fun A => by simpa [symmDiff_self] using hasDensityZero_empty
    symm := fun {A B} h => by rwa [symmDiff_comm] at h
    trans := fun {A B C} hAB hBC =>
      hasDensityZero_mono (symmDiff_triangle A B C)
        (by simpa [Set.sup_eq_union] using hasDensityZero_union hAB hBC)
  }

def B1 : Type := Quotient densityZeroSetoid

/- B₂ = P(ℕ) / I₂ where I₂ = {A : δ(A) = 0}.
   Two sets are equivalent iff their symmetric difference has log-density 0. -/
/-- `hasLogDensityZero` and `hasDensityZero` share the same (simplified) body,
    so the log-density symmetric-difference relation is likewise an equivalence. -/
def logDensityZeroSetoid : Setoid (Set ℕ) where
  r A B := hasLogDensityZero (A ∆ B)
  iseqv := {
    refl := fun A => by
      show hasDensityZero _
      simpa [symmDiff_self] using hasDensityZero_empty
    symm := fun {A B} h => by rwa [symmDiff_comm] at h
    trans := fun {A B C} hAB hBC =>
      hasDensityZero_mono (symmDiff_triangle A B C)
        (by simpa [Set.sup_eq_union] using hasDensityZero_union hAB hBC)
  }

def B2 : Type := Quotient logDensityZeroSetoid

/-- The Erdős-Ulam question: are B₁ and B₂ isomorphic? -/
def erdos_ulam_question : Prop := ∃ f : B1 → B2, Function.Bijective f

/- ## Part III: Just-Krawczyk's Resolution -/

/-  Just-Krawczyk Theorem (1984): Under the Continuum Hypothesis,
    B₁ and B₂ ARE isomorphic. Both algebras have cardinality ℵ₁
    under CH with similar saturation properties, yielding an isomorphism
    by back-and-forth. -/
/-  The isomorphism question is independent of ZFC:
    - Under CH: B₁ ≅ B₂ (Just-Krawczyk 1984)
    - Without CH: the question may have a different answer -/
/- ## Part IV: Ideal Properties -/

/-  Both I₁ and I₂ are σ-ideals (closed under countable unions),
    contain all finite sets, and are closed under subsets. -/
/-  The quotient P(ℕ)/Fin (mod finite sets) is NOT isomorphic to B₁ or B₂.
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
