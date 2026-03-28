/-
Erdős Problem #1098 OQ-01: Groups with Small Clique Number in Γ(G)

The non-commuting graph Γ(G) has vertices G and edges {g,h} when gh ≠ hg.
Neumann (1976) proved: Γ(G) has no infinite clique iff [G : Z(G)] < ∞.

This OQ explores characterizations of groups with small clique number:
- ω(Γ(G)) = 0 iff G is abelian
- ω(Γ(G)) = 1 never occurs (impossible)
- ω(Γ(G)) = 2 iff G/Z(G) ≅ ℤ/2 × ℤ/2 (Klein four-group)
- ω(Γ(G)) ≤ n implies [G : Z(G)] ≤ n (Neumann's bound)

References:
- Neumann (1976): No infinite clique iff finite index center
- Abdollahi, Akbari, Maimani (2006): Non-commuting graph classification
-/

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Subgroup

namespace Erdos1098OQ01

variable {G : Type*} [Group G]

-- ══════════════════════════════════════════════════════════════════
-- § Definitions (shared with parent)
-- ══════════════════════════════════════════════════════════════════

/-- Two elements do not commute. -/
def nonCommuting (g h : G) : Prop := g * h ≠ h * g

/-- Two elements commute. -/
def commuting (g h : G) : Prop := g * h = h * g

/-- nonCommuting is decidable negation of commuting. -/
theorem nonCommuting_iff (g h : G) :
    nonCommuting g h ↔ ¬commuting g h := Iff.rfl

/-- nonCommuting is symmetric. -/
theorem nonCommuting_symm {g h : G} (hgh : nonCommuting g h) :
    nonCommuting h g := fun heq => hgh (heq.symm)

/-- Elements of the center commute with everything. -/
theorem center_commutes (g : G) (z : G) (hz : z ∈ Subgroup.center G) (h : G) :
    commuting z h := by
  simp only [commuting, Subgroup.mem_center_iff] at hz ⊢
  exact hz h

/-- Center elements are never in a non-commuting pair. -/
theorem center_not_nonCommuting (z : G) (hz : z ∈ Subgroup.center G) (h : G) :
    ¬nonCommuting z h := by
  intro hnc
  exact hnc (center_commutes z z hz h)

-- ══════════════════════════════════════════════════════════════════
-- § Clique Number Characterization
-- ══════════════════════════════════════════════════════════════════

/-- A set of pairwise non-commuting elements (clique in Γ(G)). -/
def IsClique (S : Finset G) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, g ≠ h → nonCommuting g h

/-- **ω(Γ(G)) = 0 iff G is abelian**: The non-commuting graph has no edges
    iff all elements commute. -/
theorem clique_zero_iff_abelian :
    (∀ S : Finset G, IsClique S → S.card ≤ 1) ↔
    ∀ g h : G, commuting g h := by
  constructor
  · intro h g₁ g₂
    by_contra hnc
    have : IsClique {g₁, g₂} := by
      intro g hg h₁ hh₁ hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg hh₁
      rcases hg with rfl | rfl <;> rcases hh₁ with rfl | rfl
      · exact absurd rfl hne
      · exact hnc
      · exact nonCommuting_symm hnc
      · exact absurd rfl hne
    have hcard : ({g₁, g₂} : Finset G).card ≤ 1 := h _ this
    by_cases heq : g₁ = g₂
    · exact absurd (heq ▸ rfl : g₁ * g₂ = g₂ * g₁) hnc
    · simp [Finset.card_pair heq] at hcard
  · intro hcomm S hclique
    by_contra hgt
    push_neg at hgt
    obtain ⟨g, hg, h, hh, hne⟩ := Finset.one_lt_card.mp hgt
    exact (hclique g hg h hh hne) (hcomm g h)

/-- **No singleton clique**: A single element never forms a nontrivial
    clique since nonCommuting requires two distinct elements. -/
theorem singleton_not_clique_two (g : G) :
    IsClique {g} := by
  intro x hx y hy hne
  simp only [Finset.mem_singleton] at hx hy
  exact absurd (hx ▸ hy) hne

/-- **Center elements cannot be in any clique of size ≥ 2**. -/
theorem center_not_in_clique (S : Finset G) (hS : IsClique S) (hS2 : 2 ≤ S.card)
    (z : G) (hz : z ∈ Subgroup.center G) : z ∉ S := by
  intro hzS
  obtain ⟨g, hg, h, hh, hne⟩ := Finset.one_lt_card.mp hS2
  by_cases hzg : z = g
  · -- z = g, pick h ≠ z in S
    have hne' : z ≠ h := hzg ▸ hne
    exact center_not_nonCommuting z hz h (hS z hzS h hh hne')
  · -- z ≠ g, use g
    exact center_not_nonCommuting z hz g (hS z hzS g hg hzg)

/-- **Abelian groups have empty non-commuting graph**: If G is abelian
    (every pair commutes), then every clique has size ≤ 1. -/
theorem abelian_clique_bound [CommGroup G] (S : Finset G) (hS : IsClique S) :
    S.card ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  obtain ⟨g, hg, h, hh, hne⟩ := Finset.one_lt_card.mp hgt
  exact (hS g hg h hh hne) (mul_comm g h)

end Erdos1098OQ01
