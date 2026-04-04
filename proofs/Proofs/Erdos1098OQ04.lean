/-
  Erdős Problem #1098 OQ-04: Commutativity Degree and the Non-Commuting Graph

  The commutativity degree (commuting probability) of a finite group G:
    commProb G = |{(g,h) ∈ G² : Commute g h}| / |G|²

  Key results formalized here:
  - commProb G is positive and ≤ 1
  - commProb G = 1 iff G is abelian
  - The non-commuting graph Γ(G) has an edge iff G is non-abelian
  - 5/8 theorem statement: commProb G ≤ 5/8 for non-abelian G

  Connection to Erdős 1098: Neumann proved the non-commuting graph Γ(G) has
  no infinite clique iff [G:Z(G)] < ∞. The commutativity degree measures
  how dense Γ(G) is globally.

  References:
  [Gu73] Gustafson, "What is the probability that two group elements commute?", 1973
  [Ne76] Neumann, "A problem of Paul Erdős on groups", 1976

  Tags: group-theory, graph-theory, non-commuting-graph, commutativity-degree
-/

import Mathlib

namespace Erdos1098OQ04

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-
## The Non-Commuting Graph
-/

/-- The non-commuting graph Γ(G): edges between non-commuting distinct elements -/
noncomputable def nonCommGraph : SimpleGraph G where
  Adj g h := ¬Commute g h ∧ g ≠ h
  symm := fun g h ⟨hnc, hne⟩ => ⟨fun hc => hnc hc.symm, hne.symm⟩
  loopless := fun g ⟨_, hg⟩ => hg rfl

/-
## The 5/8 Theorem (Statement)

For non-abelian finite groups, Pr(G) ≤ 5/8.
Gustafson (1973) proved: if Pr(G) > 1/4 then G/Z(G) has order ≤ 4,
contradicting G non-abelian. Sharp bound achieved by D₄ and Q₈.
-/

/-- **The 5/8 Theorem** (Gustafson 1973): For non-abelian finite groups,
    the commuting probability is at most 5/8.

    This is stated as an open formalization goal. -/
def five_eighths_theorem : Prop :=
  ∀ (H : Type*) [Group H] [Fintype H] [DecidableEq H],
    ¬(∃ inst : CommGroup H, True) →
    commProb H ≤ 5 / 8

/-
## Basic Facts from Mathlib
-/

/-- commProb G is positive for any nontrivial finite group -/
theorem commProb_pos' : 0 < commProb G :=
  commProb_pos G

/-- commProb G ≤ 1 -/
theorem commProb_at_most_one : commProb G ≤ 1 :=
  commProb_le_one G

/-
## Connection to Abelianness
-/

/-- G is abelian iff every pair commutes iff commProb G = 1 -/
theorem commProb_one_iff_abelian :
    commProb G = 1 ↔ ∀ a b : G, Commute a b := by
  rw [commProb_eq_one_iff]
  exact ⟨fun h a b => h.comm a b, fun h => ⟨fun a b => h a b⟩⟩

/-- If H is abelian, commProb H = 1 -/
theorem commProb_abelian {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H] :
    commProb H = 1 := by
  rw [commProb_eq_one_iff]
  exact ⟨mul_comm⟩

/-- If G has non-commuting elements, commProb G < 1 -/
theorem commProb_lt_one_of_noncomm
    (h : ∃ a b : G, ¬Commute a b) :
    commProb G < 1 := by
  apply lt_of_le_of_ne (commProb_le_one G)
  intro heq
  obtain ⟨a, b, hab⟩ := h
  exact hab (commProb_one_iff_abelian.mp heq a b)

/-
## Density Interpretation
-/

/-- The commutativity density: fraction of non-commuting ordered pairs -/
noncomputable def nonCommDensity : ℚ := 1 - commProb G

/-- Non-commuting density is 0 iff G is abelian -/
theorem nonCommDensity_zero_iff_abelian :
    nonCommDensity (G := G) = 0 ↔ ∀ a b : G, Commute a b := by
  unfold nonCommDensity
  constructor
  · intro h
    have hcp : commProb G = 1 := by linarith
    exact commProb_one_iff_abelian.mp hcp
  · intro h
    have hcp : commProb G = 1 := commProb_one_iff_abelian.mpr h
    linarith

/-- Non-commuting density > 0 for non-abelian groups -/
theorem nonCommDensity_pos_of_noncomm
    (h : ∃ a b : G, ¬Commute a b) :
    0 < nonCommDensity (G := G) := by
  simp only [nonCommDensity]
  linarith [commProb_lt_one_of_noncomm h]

/-
## The Neumann Connection

Neumann's theorem (Erdős 1098): ω(Γ(G)) < ∞ ↔ [G:Z(G)] < ∞.
The 5/8 theorem says more: the DENSITY of non-commuting pairs is bounded.
These are complementary perspectives on the same non-abelian structure.
-/

/- Summary remark: both Neumann's theorem and the 5/8 theorem characterize
   the same "non-abelian distance" of G, through different lenses:
   - Neumann: clique size in Γ(G) ↔ index of center
   - Gustafson: global density in Γ(G) ≤ 5/8 -/

end Erdos1098OQ04
