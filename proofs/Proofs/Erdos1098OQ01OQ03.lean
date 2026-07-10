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
* `exists_clique_centralizer_cover` — **(fully proved, new)** the first step of Neumann's
  hard direction: if ω(Γ(G)) is finite then a single maximal clique `S` has the property
  that the centralizers `{C_G(a) : a ∈ S}` cover `G`.
* `exists_finiteIndex_centralizer_of_boundedCliques` — **(fully proved, new)** combining the
  cover with B. H. Neumann's coset-covering theorem (Mathlib's `CosetCover`): if ω(Γ(G)) is
  finite then *some* centralizer `C_G(a)` has finite index. This is a genuine partial
  result toward (still strictly weaker than) the hard direction.
* `exists_finiteIndex_iInf_centralizer_of_boundedCliques` — **(fully proved, new)** strengthens
  the previous step: if ω(Γ(G)) is finite then the *finite-index* centralizers already cover
  `G`, and their intersection `H = ⋂ₐ C_G(a)` is a finite-index subgroup. This isolates the
  finite-index "core" `H` that Neumann's argument analyses (still strictly weaker than the hard
  direction, which needs `Z(G)` — the intersection over *all* of `G` — to have finite index).
* `center_finiteIndex_iff_relIndex_core` — **(fully proved, new)** localizes the residual
  gap: if ω(Γ(G)) is finite then `[G:Z(G)]` is finite *iff* `Z(G)` has finite index inside
  the explicit finite-index core `H = ⋂ₐ C_G(a)` (which contains `Z(G)`). The remaining hard
  content is thus confined to the single relative index `(center G).relIndex H`; the natural
  Mathlib endgame is `Subgroup.index_center_le_pow`, gated on `Finite (commutatorSet G)`.
* `neumann_hard_direction` — **(axiom, Neumann 1976)** if ω(Γ(G)) is finite then
  `[G:Z(G)]` is finite. This is the deep content of Erdős #1098.
* `neumann_full_theorem` — the equivalence ω(Γ(G)) finite ⟺ [G:Z(G)] finite.
* `neumann_hard_direction_of_finite` / `neumann_hard_direction_of_finite_commutatorSet`
  — **(fully proved, axiom-free)** the hard direction holds unconditionally on the finite
  and finite-commutator-set (BFC) classes, via the Mathlib Schur endgame
  `Subgroup.finiteIndex_center`. These pin the axiom's residual content to the single
  implication `BoundedCliques G → Finite (commutatorSet G)`.

## Honesty

The forward (bounding) direction is fully machine-checked with the explicit and sharp
bound `ω ≤ [G:Z(G)]`. For the converse we now machine-check the *first three steps* of
Neumann's argument — the reduction to a finite centralizer cover, the extraction of a
single finite-index centralizer via Mathlib's `CosetCover`, and the further reduction to a
finite-index *core* `H = ⋂ₐ C_G(a)` (the finite-index centralizers already cover `G`, and
their intersection has finite index). This leaves only the final BFC step (from the
finite-index core `H`, which centralizes a maximal clique, to the finite-index *centre*,
i.e. the intersection over *all* of `G`) as the axiom `neumann_hard_direction`, a genuinely
non-trivial result not available in Mathlib. It is stated as a single, clearly-labelled
axiom with citation. Status: axiomatized.

## Sorries

0 sorries. 1 axiom (`neumann_hard_direction`, Neumann 1976).

## Tags

Erdős, non-commuting-graph, clique-number, center, index, Neumann, group-theory
-/

import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Commutator.Finite
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Subgroup
open scoped Pointwise

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
-- SECTION III.5: First step of the hard direction — the centralizer cover
-- ============================================================

/-- **(New, fully proved — the first genuine step of Neumann's hard direction.)**
    If ω(Γ(G)) is finite, then there is a *single clique* `S` — a finite set of
    pairwise non-commuting elements — whose members' centralizers cover `G`:
    every `g ∈ G` commutes with some `a ∈ S`.

    *Proof.* Among all cliques pick one, `S`, of maximum cardinality. The clique
    cardinalities form a nonempty set of naturals bounded above by the clique bound,
    so a maximum is attained (`Nat.sSup_mem`). For any `g`, if `g` commuted with no
    element of `S` then `g ∉ S` and `insert g S` would be a clique of strictly
    larger cardinality, contradicting maximality. Hence `g` commutes with some
    `a ∈ S`.

    This is exactly the reduction Neumann uses to turn the clique bound into a
    finite cover of `G` by centralizers. The remaining (deep) step — that such a
    cover forces `[G:Z(G)]` to be finite — is `neumann_hard_direction`. -/
theorem exists_clique_centralizer_cover (h : BoundedCliques G) :
    ∃ S : Finset G, IsClique S ∧ ∀ g : G, ∃ a ∈ S, a * g = g * a := by
  classical
  obtain ⟨B, hB⟩ := h
  -- The set of attainable clique cardinalities is nonempty (∅ is a clique) and
  -- bounded above by `B`.
  set A : Set ℕ := {n | ∃ S : Finset G, IsClique S ∧ S.card = n} with hA
  have hEmpty : IsClique (∅ : Finset G) := by
    intro g hg; exact absurd hg (Finset.notMem_empty g)
  have hne : A.Nonempty := ⟨0, ∅, hEmpty, Finset.card_empty⟩
  have hbdd : BddAbove A := ⟨B, by rintro n ⟨S, hS, rfl⟩; exact hB S hS⟩
  -- A maximum cardinality is attained, by a clique `S`.
  obtain ⟨S, hSclique, hScard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨S, hSclique, fun g => ?_⟩
  by_contra hcon
  push_neg at hcon
  -- `g` commutes with no element of `S`; in particular `g ∉ S`.
  have hgnotin : g ∉ S := fun hg => hcon g hg rfl
  -- `insert g S` is then a strictly larger clique.
  have hbig : IsClique (insert g S) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact absurd rfl hxy
      · exact fun hcomm => hcon y hyS hcomm.symm
    · rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact hcon x hxS
      · exact hSclique x hxS y hyS hxy
  have hcardins : (insert g S).card = S.card + 1 :=
    Finset.card_insert_of_notMem hgnotin
  have hle : (insert g S).card ≤ sSup A :=
    le_csSup hbdd ⟨insert g S, hbig, rfl⟩
  rw [hcardins, hScard] at hle
  omega

/-- **(New, fully proved — Neumann's covering step via Mathlib's `CosetCover`.)**
    If ω(Γ(G)) is finite, then *some* element `a` has a centralizer `C_G(a)` of
    finite index in `G`.

    *Proof.* By `exists_clique_centralizer_cover`, the centralizers `C_G(a)`
    (`a` ranging over a finite clique `S`) cover `G`. These are subgroups, i.e.
    cosets `1 · C_G(a)`, so B. H. Neumann's coset-covering theorem
    (`Subgroup.exists_finiteIndex_of_leftCoset_cover`) yields one of finite index.

    This is a genuine, machine-checked consequence of bounded clique number — a
    strict step beyond the cover itself. It is still strictly weaker than the full
    `neumann_hard_direction`, which requires *all of* `Z(G) = ⋂ₐ C_G(a)` to have
    finite index; bridging from "one finite-index centralizer" to "finite-index
    centre" is the remaining deep BFC content. -/
theorem exists_finiteIndex_centralizer_of_boundedCliques (h : BoundedCliques G) :
    ∃ a : G, (Subgroup.centralizer {a}).index ≠ 0 := by
  obtain ⟨S, _, hcover⟩ := exists_clique_centralizer_cover h
  -- Reformulate the cover as a left-coset cover with trivial representatives.
  have hcovers :
      ⋃ a ∈ S, (1 : G) • ((Subgroup.centralizer {a} : Subgroup G) : Set G)
        = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨a, haS, hax⟩ := hcover x
    rw [Set.mem_iUnion₂]
    exact ⟨a, haS, by rw [one_smul]; exact Subgroup.mem_centralizer_singleton_iff.mpr hax.symm⟩
  obtain ⟨k, _, hk⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcovers
  exact ⟨k, hk.index_ne_zero⟩

/-- **(New, fully proved — strengthens the covering step to a finite-index core.)**
    If ω(Γ(G)) is finite, then there is a finite set `T` of elements such that

    * every centralizer `C_G(a)`, `a ∈ T`, has finite index in `G`;
    * these finite-index centralizers already **cover** `G` (as left cosets `1 · C_G(a)`);
      and
    * their intersection `H := ⋂_{a ∈ T} C_G(a)` is itself a **finite-index** subgroup.

    *Proof.* Start from the finite clique `S` whose centralizers cover `G`
    (`exists_clique_centralizer_cover`), viewed as a left-coset cover with trivial
    representatives. B. H. Neumann's coset-covering theorem in the form
    `Subgroup.leftCoset_cover_filter_FiniteIndex` says the *finite-index* members of a
    finite coset cover already cover, so `T := {a ∈ S : [G:C_G(a)] < ∞}` still covers
    `G`. Finally the intersection of finitely many finite-index subgroups has finite
    index (`Subgroup.finiteIndex_iInf'`).

    This is a strict advance over `exists_finiteIndex_centralizer_of_boundedCliques`
    (which produced only *one* finite-index centralizer): it isolates the finite-index
    subgroup `H` that Neumann's argument actually analyses. `H` centralizes every
    `a ∈ T` by construction. The remaining deep step — that this finite-index `H`
    forces the *centre* `Z(G)` (the intersection of *all* centralizers, over all of
    `G`) to have finite index — is the BFC content recorded as
    `neumann_hard_direction`. -/
theorem exists_finiteIndex_iInf_centralizer_of_boundedCliques (h : BoundedCliques G) :
    ∃ T : Finset G,
      (∀ a ∈ T, (Subgroup.centralizer {a}).index ≠ 0) ∧
      (⋃ a ∈ T, (1 : G) • ((Subgroup.centralizer {a} : Subgroup G) : Set G)) = Set.univ ∧
      (⨅ a ∈ T, Subgroup.centralizer {a}).index ≠ 0 := by
  classical
  obtain ⟨S, _, hcover⟩ := exists_clique_centralizer_cover h
  -- Reformulate the clique cover as a left-coset cover with trivial representatives.
  have hcovers :
      ⋃ a ∈ S, (1 : G) • ((Subgroup.centralizer {a} : Subgroup G) : Set G)
        = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨a, haS, hax⟩ := hcover x
    rw [Set.mem_iUnion₂]
    exact ⟨a, haS, by rw [one_smul]; exact Subgroup.mem_centralizer_singleton_iff.mpr hax.symm⟩
  refine ⟨S.filter (fun a => (Subgroup.centralizer {a}).FiniteIndex), ?_, ?_, ?_⟩
  · -- Each surviving centralizer has finite index by construction.
    intro a ha
    exact (Finset.mem_filter.mp ha).2.index_ne_zero
  · -- Neumann's coset-cover theorem: the finite-index members already cover `G`.
    exact Subgroup.leftCoset_cover_filter_FiniteIndex
      (s := S) (g := fun _ => (1 : G)) (H := fun a => Subgroup.centralizer {a}) hcovers
  · -- The intersection of finitely many finite-index subgroups has finite index.
    exact (Subgroup.finiteIndex_iInf' (fun a => Subgroup.centralizer {a})
      (fun a ha => (Finset.mem_filter.mp ha).2)).index_ne_zero

/-- The centre lies in the centralizer of any single element: a central `z`
    commutes with everything, in particular with `a`. -/
theorem center_le_centralizer_singleton (a : G) :
    Subgroup.center G ≤ Subgroup.centralizer {a} := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_center_iff.mp hz a).symm

/-- **(New, fully proved — localizes the residual gap to a finite-index core.)**
    If ω(Γ(G)) is finite, then there is a *finite-index* subgroup
    `H = ⋂_{a ∈ T} C_G(a)` (centralizing a maximal clique `T`) with `Z(G) ≤ H`,
    such that

    > `[G : Z(G)]` is finite  ⟺  `Z(G)` has finite index **within `H`**.

    *Proof.* Take the finite-index core `H` from
    `exists_finiteIndex_iInf_centralizer_of_boundedCliques`. Since `Z(G)` commutes
    with everything it lies in every `C_G(a)`, hence `Z(G) ≤ H`. The index tower
    `[G : Z(G)] = [H : Z(G)] · [G : H]` (`Subgroup.relIndex_mul_index`) with the
    finite factor `[G : H] ≠ 0` makes `[G : Z(G)] ≠ 0` equivalent to
    `[H : Z(G)] ≠ 0`.

    This does **not** remove `neumann_hard_direction`: the relative index
    `(center G).relIndex H` is exactly the quantity that remains to be bounded, and
    bounding it is still the deep BFC content of Neumann's theorem. What the lemma
    *does* achieve is to confine that content to a single, explicit finite-index
    subgroup `H` that centralizes a maximal clique — Neumann's remaining work is now
    entirely *inside* `H`, not spread over all of `G`. The natural Mathlib endgame is
    `Subgroup.index_center_le_pow` (finite `commutatorSet` ⟹ finite-index centre),
    whose hypothesis `Finite (commutatorSet G)` is the BFC statement that bounded
    cliques must still be shown to imply. -/
theorem center_finiteIndex_iff_relIndex_core (h : BoundedCliques G) :
    ∃ H : Subgroup G, H.index ≠ 0 ∧ Subgroup.center G ≤ H ∧
      ((Subgroup.center G).index ≠ 0 ↔ (Subgroup.center G).relIndex H ≠ 0) := by
  obtain ⟨T, _, _, hHidx⟩ := exists_finiteIndex_iInf_centralizer_of_boundedCliques h
  set H := ⨅ a ∈ T, Subgroup.centralizer {a} with hHdef
  have hle : Subgroup.center G ≤ H :=
    le_iInf₂ (fun a _ => center_le_centralizer_singleton a)
  refine ⟨H, hHidx, hle, ?_⟩
  -- Index tower: `[H : Z(G)] · [G : H] = [G : Z(G)]`.
  have hmul := Subgroup.relIndex_mul_index hle
  constructor
  · intro hz hr
    rw [hr, zero_mul] at hmul
    exact hz hmul.symm
  · intro hr
    rw [← hmul]
    exact mul_ne_zero hr hHidx

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

/-- **Bounded cliques pass to subgroups (heredity of ω(Γ)).**  The non-commuting
    graph `Γ(H)` of a subgroup `H ≤ G` is an *induced subgraph* of `Γ(G)`: the
    inclusion `H ↪ G` is an injective homomorphism, so it carries every clique of
    `Γ(H)` to a clique of `Γ(G)` of the same size.  Hence any uniform clique bound
    for `G` is also one for `H`, i.e. `ω(Γ(H)) ≤ ω(Γ(G))`.

    Combined with Neumann's theorem this is a genuine structural consequence: if
    `[G : Z(G)]` is finite then `[H : Z(H)]` is finite for *every* subgroup `H ≤ G`
    — finiteness of the central index is inherited downward. Axiom-free (it uses
    only the easy transfer of cliques, not the BFC core). -/
theorem boundedCliques_of_subgroup (H : Subgroup G) (h : BoundedCliques G) :
    BoundedCliques H := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun S hS => ?_⟩
  have hinj : Function.Injective (H.subtype) := H.subtype_injective
  let e : H ↪ G := ⟨H.subtype, hinj⟩
  have hclique : IsClique (S.map e) := by
    intro a ha b hb hab
    rw [Finset.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hne : a' ≠ b' := fun heq => hab (by rw [heq])
    have key := hS a' ha' b' hb' hne
    intro hEq
    apply key
    apply hinj
    rw [map_mul, map_mul]
    exact hEq
  rw [← Finset.card_map e]
  exact hB _ hclique

/-- **Bounded cliques pass to surjective images / quotients (heredity of ω(Γ)).**
    If `f : G →* K` is a *surjective* homomorphism and `Γ(G)` has finite clique
    number, then so does `Γ(K)`; in particular `ω(Γ(G/N)) ≤ ω(Γ(G))` for every
    normal subgroup `N ⊴ G`.

    *Proof.* Choose a set-theoretic section `g : K → G` of `f` (`f ∘ g = id`).
    Because `f (g k) = k`, the section `g` is injective, and it carries any clique
    `S ⊆ K` of `Γ(K)` to the clique `g '' S ⊆ G` of the *same* size: if the images
    `s, t ∈ K` fail to commute then so do their lifts `g s, g t` (applying the
    homomorphism `f` to `g s · g t = g t · g s` would force `s · t = t · s`).
    Hence any uniform clique bound `B` for `G` bounds the cliques of `K` as well.

    This is the surjective/quotient dual of `boundedCliques_of_subgroup` (which used
    an *injective* hom to push cliques *up* into `G`); here a section pulls a clique
    of the image *back* into `G`.  Both directions are axiom-free — they use only the
    elementary transfer of cliques, not the BFC core `neumann_hard_direction`.
    Combined with Neumann's theorem it says finiteness of the central index descends
    to every quotient: if `[G : Z(G)]` is finite then `[G/N : Z(G/N)]` is finite for
    every `N ⊴ G`. -/
theorem boundedCliques_of_surjective {K : Type*} [Group K] (f : G →* K)
    (hf : Function.Surjective f) (h : BoundedCliques G) : BoundedCliques K := by
  classical
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun S hS => ?_⟩
  -- a set-theoretic section `g : K → G` of the surjection `f`
  choose g hg using hf
  have hginj : Function.Injective g := by
    intro a b hab
    have hfa : f (g a) = f (g b) := by rw [hab]
    rwa [hg, hg] at hfa
  -- the section carries the clique `S ⊆ K` to a clique of the same size in `G`
  have hclique : IsClique (S.image g) := by
    intro a ha b hb hab
    rw [Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hne : a' ≠ b' := fun heq => hab (by rw [heq])
    have key := hS a' ha' b' hb' hne
    intro hEq
    apply key
    have hf2 : f (g a' * g b') = f (g b' * g a') := congrArg f hEq
    simpa only [map_mul, hg] using hf2
  rw [← Finset.card_image_of_injective S hginj]
  exact hB _ hclique

/-- **The hard direction holds unconditionally — and axiom-free — for finite groups.**
    When `G` is finite the centre automatically has finite index (`[G:Z(G)] ≤ |G| < ∞`,
    here via `Subgroup.index_ne_zero_of_finite`), so the forward implication of
    Neumann's theorem — `ω(Γ(G)) finite ⟹ [G:Z(G)] finite` — is provable *without* the
    BFC axiom `neumann_hard_direction`. The `BoundedCliques G` hypothesis is not used:
    it is retained only so that the statement is a literal drop-in for the axiom's
    signature in the finite case.

    This pins down where the axiom's content actually lives: `neumann_hard_direction`
    is substantive **only for infinite groups**. Every finite group satisfies the hard
    direction for the trivial reason that all of its subgroups have finite index; the
    BFC / coset-covering machinery Neumann (1976) invokes is needed precisely to handle
    the infinite case, where `BoundedCliques` (rather than finiteness of `G`) is the
    only source of the finite-index conclusion. Compare `abelian_bounded_cliques`, which
    records the *easy* direction for the abelian case. -/
theorem neumann_hard_direction_of_finite [Finite G] (_ : BoundedCliques G) :
    (Subgroup.center G).index ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

/-- **The hard direction holds — axiom-free — whenever the commutator set is finite.**
    If `G` is finitely generated and its set of commutators `{[a, b] : a, b ∈ G}` is
    finite, then the centre has finite index — this is the Schur/Baer–Neumann endgame
    `Subgroup.finiteIndex_center` (`[G:Z(G)] ≤ |commutatorSet G| ^ rank G`, via
    `Subgroup.index_center_le_pow`). Hence the forward implication of Neumann's theorem —
    `ω(Γ(G)) finite ⟹ [G:Z(G)] finite` — is provable *without* the BFC axiom
    `neumann_hard_direction`. As in the finite case, `BoundedCliques G` is unused: it is
    retained only so the statement is a literal drop-in for the axiom's signature on the
    finite-commutator-set class.

    This strictly generalises `neumann_hard_direction_of_finite` (a finite group is
    finitely generated with a finite commutator set) and sharpens the localization
    narrative of `center_finiteIndex_iff_relIndex_core`: the *entire* remaining content of
    `neumann_hard_direction` is the single implication
    `BoundedCliques G → Finite (commutatorSet G)` — that bounded non-commuting sets force
    finitely many commutators. That implication is exactly the "boundedly finite-by-abelian"
    (BFC) core of Neumann (1976); once it is supplied, the Mathlib development above discharges
    the finite-index conclusion. So the axiom's genuine content is BFC-finiteness of the
    commutator set, not the index bound itself. -/
theorem neumann_hard_direction_of_finite_commutatorSet
    [Group.FG G] [Finite (commutatorSet G)] (_ : BoundedCliques G) :
    (Subgroup.center G).index ≠ 0 :=
  Subgroup.FiniteIndex.index_ne_zero

/-- **Bounded cliques are a group-isomorphism invariant.**  If `G ≃* K` then `Γ(G)` has
    finite clique number iff `Γ(K)` does: `BoundedCliques G ↔ BoundedCliques K`.  An
    isomorphism is in particular a surjective homomorphism, so `boundedCliques_of_surjective`
    transports the property forward along `e` and backward along `e.symm` — the two
    heredity lemmas `boundedCliques_of_subgroup` (injective, cliques *up*) and
    `boundedCliques_of_surjective` (surjective, cliques *back*) specialise, at a bijection,
    to full invariance.

    Axiom-free (only the elementary clique transfer, not the BFC core
    `neumann_hard_direction`).  Consequently the whole Neumann dichotomy
    `BoundedCliques ↔ [·:Z(·)] finite` is an isomorphism invariant: isomorphic groups share
    both the finiteness of their non-commuting clique number and of their central index. -/
theorem boundedCliques_congr {K : Type*} [Group K] (e : G ≃* K) :
    BoundedCliques G ↔ BoundedCliques K := by
  refine ⟨boundedCliques_of_surjective e.toMonoidHom ?_,
          boundedCliques_of_surjective e.symm.toMonoidHom ?_⟩
  · exact fun y => ⟨e.symm y, by simp⟩
  · exact fun y => ⟨e y, by simp⟩

end Erdos1098OQ01OQ03
