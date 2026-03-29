/-
  Aristotle targets for Erdős Problem #956
  Routine supporting lemmas for automated proof search.
  See Erdos956Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (h(n) > n^(1+c))
  - Known results from Mathlib: set distance properties, convexity/compactness
    preservation under translation, basic analysis inequalities
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos956Aristotle

open Set Metric Finset

/-- The distance between two sets in a metric space. -/
noncomputable def setDistance {X : Type*} [PseudoMetricSpace X] (C D : Set X) : ℝ :=
  sInf { dist c d | (c : X) (d : X) (_ : c ∈ C) (_ : d ∈ D) }

/-- A translate C + x of a set. -/
def translate (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  { c + x | c ∈ C }

-- Routine: Symmetry of set distance (follows from dist_comm)
theorem setDistance_symm {X : Type*} [PseudoMetricSpace X] (C D : Set X) :
    setDistance C D = setDistance D C := by
  unfold setDistance
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, d, hc, hd, rfl⟩
    exact ⟨d, c, hd, hc, (dist_comm c d).symm⟩
  · rintro ⟨d, c, hd, hc, rfl⟩
    exact ⟨c, d, hc, hd, (dist_comm c d)⟩

-- Routine: Non-negativity of set distance (dist is non-negative, so is its infimum)
theorem setDistance_nonneg {X : Type*} [PseudoMetricSpace X] (C D : Set X) :
    setDistance C D ≥ 0 := by
  unfold setDistance
  rcases Set.eq_empty_or_nonempty { x | ∃ c ∈ C, ∃ d ∈ D, x = dist c d } with h | h
  · rw [h]; simp [Real.sInf_empty]
  · exact le_csInf h (by rintro _ ⟨c, _, d, _, rfl⟩; exact dist_nonneg)

-- Routine: Translates preserve convexity
theorem translate_convex (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2))
    (hC : Convex ℝ C) : Convex ℝ (translate C x) := by
  intro a ha b hb t₁ t₂ ht₁ ht₂ ht
  obtain ⟨ca, hca, rfl⟩ := ha
  obtain ⟨cb, hcb, rfl⟩ := hb
  refine ⟨t₁ • ca + t₂ • cb, hC hca hcb ht₁ ht₂ ht, ?_⟩
  simp only [smul_add]
  have : t₁ • ca + t₁ • x + (t₂ • cb + t₂ • x) =
      (t₁ • ca + t₂ • cb) + (t₁ • x + t₂ • x) := by abel
  rw [this, ← add_smul, ht, one_smul]

-- Routine: Translates preserve compactness
theorem translate_compact (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) : IsCompact (translate C x) := by
  -- translate C x is the image of C under the continuous map (· + x)
  have : translate C x = (· + x) '' C := by
    ext y; simp [translate, Set.mem_image]
  rw [this]
  exact hC.image (continuous_id.add continuous_const)

-- Routine: Translation preserves nonemptiness
theorem translate_nonempty (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2))
    (hC : C.Nonempty) : (translate C x).Nonempty := by
  obtain ⟨c, hc⟩ := hC
  exact ⟨c + x, ⟨c, hc, rfl⟩⟩

-- Routine: Distance between singletons equals point distance
theorem setDistance_singletons {X : Type*} [PseudoMetricSpace X] (a b : X) :
    setDistance {a} {b} = dist a b := by
  simp [setDistance]
  rw [show { x | ∃ c ∈ ({a} : Set X), ∃ d ∈ ({b} : Set X), x = dist c d } = {dist a b}
    from by ext; simp]
  exact csInf_singleton _

-- Routine: The general convex set exponent 7/5 exceeds the translate exponent 4/3
theorem general_exponent_larger : (7 : ℝ) / 5 > 4 / 3 := by norm_num

-- Routine: For large n, n^(4/3) > n * log n / log log n
theorem power_dominates_log_ratio (n : ℕ) (hn : n ≥ 100) :
    (n : ℝ) ^ ((4 : ℝ) / 3) > n * Real.log n / Real.log (Real.log n) := by
  sorry

end Erdos956Aristotle
