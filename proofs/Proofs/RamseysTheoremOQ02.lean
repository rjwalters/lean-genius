/-
# R(3,3) = 6 Exactly

## Problem: ramseys-theorem-oq-02

Proves the exact Ramsey number R(3,3) = 6:
- Upper bound: every 2-coloring of K₆ has a monochromatic triangle
- Lower bound: K₅ admits a triangle-free 2-coloring (pentagon, from RamseysTheorem.lean)

### Strategy (Upper Bound)
Classical pigeonhole argument:
1. Pick any vertex v in K₆. It has 5 neighbors.
2. By pigeonhole: ≥ 3 edges from v are red, or ≥ 3 are blue.
3. WLOG 3 neighbors u₀, u₁, u₂ are all red-connected to v.
4. Among edges {u₀u₁, u₀u₂, u₁u₂}:
   - Any red edge → red triangle with v.
   - All blue → blue triangle {u₀, u₁, u₂}.

### Status
- HasRamseyProperty_Fin6_3_3: proved (0 sorries)
- ramsey_3_3_exact: proved (0 sorries, uses pentagon lower bound)
-/

import Proofs.RamseysTheorem

namespace RamseyNumber33

open RamseysTheorem SimpleGraph Finset

/-!
## Part I: Pigeonhole on 5 Neighbors
-/

/-- If a + b ≥ 5, then a ≥ 3 or b ≥ 3. -/
lemma pigeonhole_5 (a b : ℕ) (h : a + b ≥ 5) : a ≥ 3 ∨ b ≥ 3 := by omega

/-!
## Part II: Extract Three Distinct Elements
-/

/-- From a finset with ≥ 3 elements, extract three distinct elements. -/
lemma extract_three {α : Type*} [DecidableEq α] {s : Finset α} (h : 3 ≤ s.card) :
    ∃ a b c : α, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq h
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht_card
  refine ⟨a, b, c, ht_sub ?_, ht_sub ?_, ht_sub ?_, hab, hac, hbc⟩ <;> simp [hab, hac, hbc]

/-!
## Part III: Monochromatic Triangle Helpers
-/

/-- Helper: prove IsRedClique on {v, x, y} given all three pairwise edges are red. -/
lemma isRedClique_triple (c : EdgeColoring (Fin 6)) (v x y : Fin 6)
    (hvx : c.color v x = true) (hvy : c.color v y = true) (hxy : c.color x y = true)
    (hne_vx : v ≠ x) (hne_vy : v ≠ y) (hne_xy : x ≠ y) :
    IsRedClique c {v, x, y} := by
  intro a ha b hb hab
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  simp only [EdgeColoring.redGraph]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [c.symm]

/-- Helper: prove IsBlueClique on {v, x, y} given all three pairwise edges are blue. -/
lemma isBlueClique_triple (c : EdgeColoring (Fin 6)) (v x y : Fin 6)
    (hvx : c.color v x = false) (hvy : c.color v y = false) (hxy : c.color x y = false)
    (hne_vx : v ≠ x) (hne_vy : v ≠ y) (hne_xy : x ≠ y) :
    IsBlueClique c {v, x, y} := by
  intro a ha b hb hab
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  simp only [EdgeColoring.blueGraph]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [c.symm]

/-- Helper: the card of a 3-element set of distinct elements is 3. -/
lemma card_triple {α : Type*} [DecidableEq α] (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset α).card = 3 := by
  rw [card_insert_of_notMem (by simp [hab, hac]),
      card_insert_of_notMem (by simp [hbc]),
      card_singleton]

/-- If v has ≥ 3 vertices in its red neighborhood, then there is a monochromatic triangle. -/
theorem triangle_from_red_nbrs (c : EdgeColoring (Fin 6))
    (v : Fin 6)
    (s : Finset (Fin 6))
    (hs_sub : s ⊆ redNeighborhood c v)
    (hs_card : 3 ≤ s.card) :
    (∃ red : Finset (Fin 6), red.card = 3 ∧ IsRedClique c red) ∨
    (∃ blue : Finset (Fin 6), blue.card = 3 ∧ IsBlueClique c blue) := by
  obtain ⟨u₀, u₁, u₂, hu₀, hu₁, hu₂, h01, h02, h12⟩ := extract_three hs_card
  have hvu₀ : c.color v u₀ = true ∧ v ≠ u₀ := by
    have := hs_sub hu₀; simp [redNeighborhood] at this; exact this
  have hvu₁ : c.color v u₁ = true ∧ v ≠ u₁ := by
    have := hs_sub hu₁; simp [redNeighborhood] at this; exact this
  have hvu₂ : c.color v u₂ = true ∧ v ≠ u₂ := by
    have := hs_sub hu₂; simp [redNeighborhood] at this; exact this
  cases h₀₁ : c.color u₀ u₁
  · -- u₀u₁ blue
    cases h₀₂ : c.color u₀ u₂
    · -- u₀u₂ blue
      cases h₁₂ : c.color u₁ u₂
      · -- all blue → blue triangle {u₀, u₁, u₂}
        exact Or.inr ⟨{u₀, u₁, u₂}, card_triple u₀ u₁ u₂ h01 h02 h12,
          isBlueClique_triple c u₀ u₁ u₂ h₀₁ h₀₂ h₁₂ h01 h02 h12⟩
      · -- u₁u₂ red → red triangle {v, u₁, u₂}
        exact Or.inl ⟨{v, u₁, u₂}, card_triple v u₁ u₂ hvu₁.2 hvu₂.2 h12,
          isRedClique_triple c v u₁ u₂ hvu₁.1 hvu₂.1 h₁₂ hvu₁.2 hvu₂.2 h12⟩
    · -- u₀u₂ red → red triangle {v, u₀, u₂}
      exact Or.inl ⟨{v, u₀, u₂}, card_triple v u₀ u₂ hvu₀.2 hvu₂.2 h02,
        isRedClique_triple c v u₀ u₂ hvu₀.1 hvu₂.1 h₀₂ hvu₀.2 hvu₂.2 h02⟩
  · -- u₀u₁ red → red triangle {v, u₀, u₁}
    exact Or.inl ⟨{v, u₀, u₁}, card_triple v u₀ u₁ hvu₀.2 hvu₁.2 h01,
      isRedClique_triple c v u₀ u₁ hvu₀.1 hvu₁.1 h₀₁ hvu₀.2 hvu₁.2 h01⟩

/-- If v has ≥ 3 vertices in its blue neighborhood, then there is a monochromatic triangle. -/
theorem triangle_from_blue_nbrs (c : EdgeColoring (Fin 6))
    (v : Fin 6)
    (s : Finset (Fin 6))
    (hs_sub : s ⊆ blueNeighborhood c v)
    (hs_card : 3 ≤ s.card) :
    (∃ red : Finset (Fin 6), red.card = 3 ∧ IsRedClique c red) ∨
    (∃ blue : Finset (Fin 6), blue.card = 3 ∧ IsBlueClique c blue) := by
  obtain ⟨u₀, u₁, u₂, hu₀, hu₁, hu₂, h01, h02, h12⟩ := extract_three hs_card
  have hvu₀ : c.color v u₀ = false ∧ v ≠ u₀ := by
    have := hs_sub hu₀; simp [blueNeighborhood] at this; exact this
  have hvu₁ : c.color v u₁ = false ∧ v ≠ u₁ := by
    have := hs_sub hu₁; simp [blueNeighborhood] at this; exact this
  have hvu₂ : c.color v u₂ = false ∧ v ≠ u₂ := by
    have := hs_sub hu₂; simp [blueNeighborhood] at this; exact this
  cases h₀₁ : c.color u₀ u₁
  · -- u₀u₁ blue → blue triangle {v, u₀, u₁}
    exact Or.inr ⟨{v, u₀, u₁}, card_triple v u₀ u₁ hvu₀.2 hvu₁.2 h01,
      isBlueClique_triple c v u₀ u₁ hvu₀.1 hvu₁.1 h₀₁ hvu₀.2 hvu₁.2 h01⟩
  · -- u₀u₁ red; try u₀u₂
    cases h₀₂ : c.color u₀ u₂
    · -- u₀u₂ blue → blue triangle {v, u₀, u₂}
      exact Or.inr ⟨{v, u₀, u₂}, card_triple v u₀ u₂ hvu₀.2 hvu₂.2 h02,
        isBlueClique_triple c v u₀ u₂ hvu₀.1 hvu₂.1 h₀₂ hvu₀.2 hvu₂.2 h02⟩
    · -- u₀u₂ red; try u₁u₂
      cases h₁₂ : c.color u₁ u₂
      · -- u₁u₂ blue → blue triangle {v, u₁, u₂}
        exact Or.inr ⟨{v, u₁, u₂}, card_triple v u₁ u₂ hvu₁.2 hvu₂.2 h12,
          isBlueClique_triple c v u₁ u₂ hvu₁.1 hvu₂.1 h₁₂ hvu₁.2 hvu₂.2 h12⟩
      · -- all u-u red → red triangle {u₀, u₁, u₂}
        exact Or.inl ⟨{u₀, u₁, u₂}, card_triple u₀ u₁ u₂ h01 h02 h12,
          isRedClique_triple c u₀ u₁ u₂ h₀₁ h₀₂ h₁₂ h01 h02 h12⟩

/-!
## Part IV: Main Upper Bound Theorem
-/

/-- **Upper bound: HasRamseyProperty (Fin 6) 3 3**

Every 2-coloring of K₆ contains a monochromatic triangle.
Proof: pick vertex 0, pigeonhole on 5 neighbors, find 3 same-color neighbors,
then triangle within those 3 neighbors or back to vertex 0.
-/
theorem HasRamseyProperty_Fin6_3_3 : HasRamseyProperty (Fin 6) 3 3 := by
  intro c
  let v : Fin 6 := ⟨0, by norm_num⟩
  have hsum : (redNeighborhood c v).card + (blueNeighborhood c v).card = 5 := by
    have := neighborhood_card_sum c v
    simp [Fintype.card_fin] at this
    omega
  rcases pigeonhole_5 (redNeighborhood c v).card (blueNeighborhood c v).card (by omega)
    with hred | hblue
  · exact triangle_from_red_nbrs c v (redNeighborhood c v) (Finset.Subset.refl _) hred
  · exact triangle_from_blue_nbrs c v (blueNeighborhood c v) (Finset.Subset.refl _) hblue

/-!
## Part V: R(3,3) = 6 Exactly
-/

/-- **R(3,3) = 6**: The exact Ramsey number.

- Lower bound (R(3,3) > 5): pentagon coloring of K₅ has no monochromatic triangle
  (proved in RamseysTheorem.lean as `ramsey_3_3_lower_bound`).
- Upper bound (R(3,3) ≤ 6): every 2-coloring of K₆ has a monochromatic triangle.

Together: 6 is the minimum n for which K_n forces a monochromatic triangle.
-/
theorem ramsey_3_3_exact :
    HasRamseyProperty (Fin 6) 3 3 ∧ ¬HasRamseyProperty (Fin 5) 3 3 :=
  ⟨HasRamseyProperty_Fin6_3_3, ramsey_3_3_lower_bound⟩

end RamseyNumber33
