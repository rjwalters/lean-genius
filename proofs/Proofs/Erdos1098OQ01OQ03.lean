/-
# Erdős #1098 OQ-01 OQ-03: Neumann's Theorem — ω(Γ(G)) finite ⟺ [G:Z(G)] finite

## Context

In the non-commuting graph Γ(G), vertices are the elements of G and edges join
non-commuting pairs. A clique is a set of pairwise non-commuting elements, and the
clique number ω(Γ(G)) is the supremum of clique sizes. Erdős asked whether a group
in which every set of pairwise non-commuting elements is finite must have a centre
of finite index. B. H. Neumann (1976) answered this affirmatively, and the converse
is elementary. Together they give **Neumann's theorem**:

> ω(Γ(G)) is finite  ⟺  [G : Z(G)] is finite.

We formalise the predicate `BoundedCliques G` ("there is a uniform finite bound on
the size of every clique", i.e. ω(Γ(G)) finite) and prove the full equivalence with
`(Subgroup.center G).index ≠ 0` (i.e. [G:Z(G)] finite, in Mathlib's convention where
`index = 0` encodes infinite index).

## Main Results

* `commuting_of_invMul_mem_center` — if `a⁻¹ * b ∈ Z(G)` then `a` and `b` commute.
* `nonCommuting_distinct_image` — non-commuting elements have distinct images in
  `G ⧸ Z(G)`; equivalently, lie in distinct central cosets.
* `clique_inj_on_quotient` — the quotient map `G → G ⧸ Z(G)` is injective on any
  clique.
* `clique_card_le_index` — **(fully proved)** every clique has size at most
  `[G : Z(G)]`. This is the easy direction, with an explicit, sharp bound.
* `bounded_cliques_of_finite_index` — **(fully proved)** if `[G:Z(G)]` is finite then
  ω(Γ(G)) is finite, witnessed by the bound `[G:Z(G)]`.
* `neumann_hard_direction` — **(axiom, Neumann 1976)** if ω(Γ(G)) is finite then
  `[G:Z(G)]` is finite. This is the deep content of Erdős #1098.
* `neumann_full_theorem` — the equivalence ω(Γ(G)) finite ⟺ [G:Z(G)] finite.

## Honesty

The forward (bounding) direction is fully machine-checked with the explicit and sharp
bound `ω ≤ [G:Z(G)]`. The converse is B. H. Neumann's theorem, whose proof is a
genuinely non-trivial covering / BFC-group argument not available in Mathlib; it is
stated as a single, clearly-labelled axiom with citation. Status: axiomatized.

## Sorries

0 sorries. 1 axiom (`neumann_hard_direction`, Neumann 1976).

## Tags

Erdős, non-commuting-graph, clique-number, center, index, Neumann, group-theory
-/

import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Subgroup

namespace Erdos1098OQ01OQ03

variable {G : Type*} [Group G]

-- ============================================================
-- SECTION I: Definitions
-- ============================================================

/-- Two group elements do not commute (an edge of the non-commuting graph Γ(G)). -/
def nonCommuting (g h : G) : Prop := g * h ≠ h * g

/-- A clique in Γ(G): a finite set of pairwise non-commuting elements. -/
def IsClique (S : Finset G) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, g ≠ h → nonCommuting g h

/-- ω(Γ(G)) is finite: there is a uniform bound on the size of every clique. -/
def BoundedCliques (G : Type*) [Group G] : Prop :=
  ∃ B : ℕ, ∀ S : Finset G, IsClique S → S.card ≤ B

-- ============================================================
-- SECTION II: Cosets of the centre separate non-commuting elements
-- ============================================================

/-- If `a⁻¹ * b` lies in the centre, then `a` and `b` commute.
    Writing `b = a * c` with `c = a⁻¹ * b` central:
    `a * b = a * (a * c) = a * a * c` and `b * a = (a * c) * a = a * (c * a)
    = a * (a * c)` since `c` is central. -/
theorem commuting_of_invMul_mem_center {a b : G}
    (h : a⁻¹ * b ∈ Subgroup.center G) : a * b = b * a := by
  -- Centrality of `a⁻¹ * b` applied to `a`: `a * (a⁻¹ * b) = (a⁻¹ * b) * a`.
  have hc : a * (a⁻¹ * b) = (a⁻¹ * b) * a := Subgroup.mem_center_iff.mp h a
  calc a * b = a * ((a⁻¹ * b) * a) := by rw [← hc]; group
    _ = b * a := by group

/-- Non-commuting elements have distinct images in the quotient `G ⧸ Z(G)`;
    equivalently they lie in distinct cosets of the centre. -/
theorem nonCommuting_distinct_image {g h : G} (hnc : nonCommuting g h) :
    (g : G ⧸ Subgroup.center G) ≠ (h : G ⧸ Subgroup.center G) := by
  intro heq
  exact hnc (commuting_of_invMul_mem_center (QuotientGroup.eq.mp heq))

/-- The quotient map `G → G ⧸ Z(G)` is injective on any clique. -/
theorem clique_inj_on_quotient {S : Finset G} (hS : IsClique S) :
    Set.InjOn (fun g : G => (g : G ⧸ Subgroup.center G)) (S : Set G) := by
  intro a ha b hb hab
  by_contra hne
  exact nonCommuting_distinct_image (hS a ha b hb hne) hab

-- ============================================================
-- SECTION III: Easy direction — finite index bounds the clique number
-- ============================================================

/-- **(Easy direction, fully proved.)** Every clique has size at most `[G : Z(G)]`.

    The clique injects into the `[G:Z(G)]`-element quotient `G ⧸ Z(G)`
    (clique elements lie in distinct central cosets), so its cardinality is
    bounded by the index. The hypothesis `index ≠ 0` is Mathlib's encoding of
    "the index is finite". -/
theorem clique_card_le_index {S : Finset G} (hS : IsClique S)
    (hfin : (Subgroup.center G).index ≠ 0) :
    S.card ≤ (Subgroup.center G).index := by
  -- Finite index means the quotient is a finite type.
  have hpos : 0 < Nat.card (G ⧸ Subgroup.center G) := by
    rw [← Subgroup.index_eq_card]; omega
  have hfinite : Finite (G ⧸ Subgroup.center G) := (Nat.card_pos_iff.mp hpos).2
  haveI : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
  -- The quotient map injects the clique into the finite quotient.
  have hbound : S.card ≤ (Finset.univ : Finset (G ⧸ Subgroup.center G)).card :=
    Finset.card_le_card_of_injOn (fun g => (g : G ⧸ Subgroup.center G))
      (fun _ _ => Finset.mem_univ _) (clique_inj_on_quotient hS)
  calc S.card ≤ (Finset.univ : Finset (G ⧸ Subgroup.center G)).card := hbound
    _ = Fintype.card (G ⧸ Subgroup.center G) := Finset.card_univ
    _ = Nat.card (G ⧸ Subgroup.center G) := (Nat.card_eq_fintype_card).symm
    _ = (Subgroup.center G).index := (Subgroup.index_eq_card (Subgroup.center G)).symm

/-- **(Easy direction, fully proved.)** If `[G : Z(G)]` is finite then ω(Γ(G)) is
    finite, with the explicit bound `[G : Z(G)]`. -/
theorem bounded_cliques_of_finite_index
    (hfin : (Subgroup.center G).index ≠ 0) : BoundedCliques G :=
  ⟨(Subgroup.center G).index, fun _ hS => clique_card_le_index hS hfin⟩

-- ============================================================
-- SECTION IV: Hard direction — Neumann's theorem (axiom)
-- ============================================================

/-- **Axiom (B. H. Neumann, 1976).** If ω(Γ(G)) is finite — i.e. there is a uniform
    bound on the size of every set of pairwise non-commuting elements — then the
    centre `Z(G)` has finite index in `G`.

    This is the substantive content of Erdős Problem #1098. Neumann's proof is a
    covering / BFC-group argument (a group with bounded non-commuting sets is
    "boundedly finite-by-abelian") that has not been reduced to a Mathlib-checkable
    development, so it is asserted here as an external, peer-reviewed result.

    Reference: B. H. Neumann, *A problem of Paul Erdős on groups*,
    J. Austral. Math. Soc. **21** (1976), 467–472. See also
    https://erdosproblems.com/1098. -/
axiom neumann_hard_direction (G : Type*) [Group G] :
    BoundedCliques G → (Subgroup.center G).index ≠ 0

-- ============================================================
-- SECTION V: Neumann's full theorem
-- ============================================================

/-- **Neumann's Theorem (Erdős #1098).** The non-commuting graph Γ(G) has finite
    clique number if and only if the centre of `G` has finite index:

    > ω(Γ(G)) finite  ⟺  [G : Z(G)] finite.

    The reverse implication is fully proved here (with the sharp bound
    `ω ≤ [G:Z(G)]`); the forward implication is Neumann (1976), recorded as
    `neumann_hard_direction`. -/
theorem neumann_full_theorem :
    BoundedCliques G ↔ (Subgroup.center G).index ≠ 0 :=
  ⟨neumann_hard_direction G, bounded_cliques_of_finite_index⟩

/-- Abelian groups have finite (in fact trivial, index 1) centre index, hence
    bounded — indeed empty — cliques: a sanity check on the easy direction.
    Stated over a fresh type to avoid clashing with the ambient `[Group G]`. -/
theorem abelian_bounded_cliques {H : Type*} [CommGroup H] : BoundedCliques H := by
  apply bounded_cliques_of_finite_index
  rw [CommGroup.center_eq_top, Subgroup.index_top]
  exact one_ne_zero

end Erdos1098OQ01OQ03
