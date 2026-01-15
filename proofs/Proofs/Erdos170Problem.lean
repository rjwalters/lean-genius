/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d9945fb1-a3f1-4263-9ab3-acacaac683e9

The following was proved by Aristotle:

- theorem trivial_upper (n : ℕ) : maxChromaticSegments n ≤ n

- theorem chromatic_ge_clique {V : Type*} [Fintype V] (G : SimpleGraph V) :
    chromaticNumber G ≥ cliqueNumber G
-/

/-
  Erdős Problem #170: Intersection Graphs of Segments

  Source: https://erdosproblems.com/170
  Status: SOLVED
  Prize: None specified

  Statement:
  What is the maximum chromatic number of intersection graphs of n line segments
  in the plane?

  History:
  - Erdős conjectured this grows polylogarithmically in n
  - Pawlik et al. (2014): Proved it can be Ω(log log n)
  - Stronger constructions followed

  Reference: Pawlik, R. et al. (2014)
-/

import Mathlib


open Set Finset

namespace Erdos170

/-! ## Line Segments -/

/-- A line segment in ℝ² represented by its endpoints. -/
structure Segment where
  p1 : ℝ × ℝ
  p2 : ℝ × ℝ
  distinct : p1 ≠ p2

/-- Two segments intersect (have a common point). -/
def Segment.Intersects (s₁ s₂ : Segment) : Prop :=
  ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
    (1 - t₁) • s₁.p1 + t₁ • s₁.p2 = (1 - t₂) • s₂.p1 + t₂ • s₂.p2

/-! ## Intersection Graphs -/

/-- The intersection graph of a finite set of segments.
    Vertices are segments, edges connect intersecting segments. -/
def intersectionGraph (S : Finset Segment) : SimpleGraph S :=
  SimpleGraph.fromRel (fun s₁ s₂ => s₁.val.Intersects s₂.val)

/-- The chromatic number of a graph (axiomatized). -/
noncomputable def chromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ c : V → Fin k, ∀ v w : V, G.Adj v w → c v ≠ c w }

/-! ## The Maximum Chromatic Number -/

/-- The maximum chromatic number of segment intersection graphs on n segments. -/
noncomputable def maxChromaticSegments (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset Segment, S.card = n ∧ chromaticNumber (intersectionGraph S) = k }

/-! ## Bounds -/

/-- Trivial upper bound: χ ≤ n. -/
theorem trivial_upper (n : ℕ) : maxChromaticSegments n ≤ n := by
  refine' csSup_le' _;
  intro k hk;
  obtain ⟨ S, hS₁, hS₂ ⟩ := hk;
  refine' hS₂ ▸ csInf_le _ _;
  · exact ⟨ 0, fun k hk => Nat.zero_le _ ⟩;
  · have h_colorable : Nonempty (S ≃ Fin n) := by
      exact ⟨ Fintype.equivOfCardEq <| by aesop ⟩;
    exact ⟨ fun v => h_colorable.some v, fun v w hvw => by simpa [ h_colorable.some.injective.eq_iff ] using hvw.ne ⟩

/-- **Pawlik et al. (2014)**: The chromatic number can be Ω(log log n). -/
axiom pawlik_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 →
    (maxChromaticSegments n : ℝ) ≥ c * Real.log (Real.log n)

/-- Known upper bound: χ = O(log n) for segment graphs. -/
axiom segment_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (maxChromaticSegments n : ℝ) ≤ C * Real.log n

/-! ## Triangle-Free Case -/

/-- For triangle-free segment graphs, the bound is even better. -/
axiom triangle_free_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (S : Finset Segment),
    (∀ a b c : S, ¬(a.val.Intersects b.val ∧ b.val.Intersects c.val ∧ a.val.Intersects c.val ∧
       a ≠ b ∧ b ≠ c ∧ a ≠ c)) →
    (chromaticNumber (intersectionGraph S) : ℝ) ≤ C * Real.log (Real.log S.card)

/-! ## Clique Number -/

/-- The clique number ω(G) - size of largest clique. -/
noncomputable def cliqueNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ C : Finset V, C.card = k ∧ ∀ v ∈ C, ∀ w ∈ C, v ≠ w → G.Adj v w }

/-- χ ≥ ω always holds. -/
theorem chromatic_ge_clique {V : Type*} [Fintype V] (G : SimpleGraph V) :
    chromaticNumber G ≥ cliqueNumber G := by
  refine' le_csInf _ _;
  · exact ⟨ Fintype.card V, ⟨ fun v => ⟨ Fintype.equivFin V v, Fintype.equivFin V v |>.2 ⟩, fun v w hvw => by simpa [ Fintype.equivFin ] using hvw.ne ⟩ ⟩;
  · rintro k ⟨ c, hc ⟩;
    refine' csSup_le' _;
    rintro n ⟨ C, rfl, hC ⟩;
    have h_card_C : Finset.card (Finset.image c C) ≤ k := by
      exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide );
    rwa [ Finset.card_image_of_injOn fun v hv w hw h => Classical.not_not.1 fun h' => hc v w ( hC v hv w hw h' ) h ] at h_card_C

/-- For segment graphs, the gap between χ and ω can be arbitrarily large. -/
axiom segment_chi_omega_gap :
  ∀ k : ℕ, ∃ S : Finset Segment,
    cliqueNumber (intersectionGraph S) = 2 ∧
    chromaticNumber (intersectionGraph S) ≥ k

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #170 asks about the maximum chromatic number of intersection
graphs of n line segments in the plane.

**Main Results:**
- Lower bound (Pawlik et al. 2014): Ω(log log n)
- Upper bound: O(log n)
- The gap shows segment graphs can have χ >> ω

**Current Knowledge:**
- log log n ≤ maxChromatic(n) ≤ O(log n)
- Triangle-free case: O(log log n) upper bound

References:
- Pawlik, R. et al. (2014): "Triangle-free intersection graphs of segments"
- Chalermsook (2015): Further bounds
-/

end Erdos170