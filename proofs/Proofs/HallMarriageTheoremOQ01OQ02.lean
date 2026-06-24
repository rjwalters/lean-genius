import Mathlib
import Proofs.HallMarriageTheoremOQ01OQ01

/-
# König's theorem from defect Hall (OQ-01 → OQ-02)

The companion entry `HallMarriageTheoremOQ01OQ01` proves the **defect** (Ore)
form of Hall's marriage theorem: for a finite family `t : ι → Finset α`, a
matching saturating all but `d` indices exists iff every sub-family `s` obeys
`#s ≤ #(s.biUnion t) + d`.

This file derives the **König–Egerváry theorem** — the min–max duality at the
heart of bipartite combinatorial optimisation — directly from that defect form:

> In a bipartite graph the **maximum matching** size equals the **minimum vertex
> cover** size.

## Set-system encoding

We model a bipartite graph by its left-neighbourhood family `t : ι → Finset α`:
the left vertices are `ι`, the right vertices are `α`, and the edges are the
pairs `(i, a)` with `a ∈ t i`.

* A **matching** is a set `J ⊆ ι` with an injective-on-`J` choice `f` landing in
  the target sets (`f i ∈ t i`); its size is `#J` (`IsMatching`).
* A **vertex cover** is a pair `(A, B)`, `A ⊆ ι`, `B ⊆ α`, that meets every edge
  (`i ∈ A ∨ a ∈ B` whenever `a ∈ t i`); its size is `#A + #B` (`IsVertexCover`).

## What is proved

* `matching_card_le_cover` — **weak duality**: every matching is at most every
  cover. Elementary: a matched index is covered on its left endpoint (landing in
  `A`) or, injectively through `f`, on its right endpoint (landing in `B`).
* `konig` — **the König theorem, certificate form**: there exist a matching and a
  vertex cover *of equal size*, and (consequently) that matching is maximum and
  that cover is minimum. The cover is read off the **deficiency-minimising**
  subset `s`, namely `(ι \ s, s.biUnion t)`, while the matching of matching size
  `#ι − (#s − #(s.biUnion t))` comes from the defect Hall theorem.

The crucial bridge is that the size of the cover `(ι \ s, s.biUnion t)` is exactly
`#ι − (#s − #(s.biUnion t))` once `s` minimises the cover size — minimality forces
`#(s.biUnion t) ≤ #s`, so the natural-number subtraction never truncates.

Mathlib has Hall's theorem but, at the time of writing, no König–Egerváry duality
for set systems; this file fills that gap from the gallery's own defect Hall.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no
`native_decide`.
-/

open Finset Function

namespace HallKonig

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [Nonempty α]

/-- A **matching** of the bipartite family `t : ι → Finset α`: a set `J ⊆ ι` and
a choice `f` injective on `J` with `f i ∈ t i` for `i ∈ J`. Its size is `J.card`. -/
def IsMatching (t : ι → Finset α) (J : Finset ι) (f : ι → α) : Prop :=
  Set.InjOn f ↑J ∧ ∀ i ∈ J, f i ∈ t i

/-- A **vertex cover** of `t`: a pair `(A, B)` of vertex sets meeting every edge,
i.e. for every `i` and every `a ∈ t i` either `i ∈ A` or `a ∈ B`. Its size is
`A.card + B.card`. -/
def IsVertexCover (t : ι → Finset α) (A : Finset ι) (B : Finset α) : Prop :=
  ∀ i, ∀ a ∈ t i, i ∈ A ∨ a ∈ B

/-- The **cover size** of the canonical cover attached to a subset `s ⊆ ι`,
namely `(ι \ s, s.biUnion t)`. The König minimum is the minimum of this over all
`s`. -/
def coverSize (t : ι → Finset α) (s : Finset ι) : ℕ :=
  (univ \ s).card + (s.biUnion t).card

omit [Fintype ι] [Nonempty α] in
/-- **Weak duality.** Every matching is no larger than every vertex cover. Map a
matched index `i` to its covering vertex: `Sum.inl i` if `i ∈ A`, else
`Sum.inr (f i)` (which lies in `B` because the edge `(i, f i)` must be covered).
This map is injective on `J`, landing in `A ⊕ B`, so `#J ≤ #A + #B`. -/
theorem matching_card_le_cover {t : ι → Finset α} {J : Finset ι} {f : ι → α}
    {A : Finset ι} {B : Finset α} (hM : IsMatching t J f) (hC : IsVertexCover t A B) :
    J.card ≤ A.card + B.card := by
  classical
  obtain ⟨hInj, hMem⟩ := hM
  set g : ι → ι ⊕ α := fun i => if i ∈ A then Sum.inl i else Sum.inr (f i) with hgdef
  have hbound : J.card ≤ (A.image Sum.inl ∪ B.image Sum.inr).card := by
    apply Finset.card_le_card_of_injOn g
    · -- the map lands in `A ⊕ B`
      intro i hi
      rw [Finset.mem_coe] at hi
      rw [Finset.mem_coe]
      simp only [hgdef]
      by_cases hiA : i ∈ A
      · rw [if_pos hiA]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hiA)
      · rw [if_neg hiA]
        have hfB : f i ∈ B := by
          rcases hC i (f i) (hMem i hi) with h | h
          · exact absurd h hiA
          · exact h
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hfB)
    · -- the map is injective on `J`
      intro i hi j hj hij
      simp only [hgdef] at hij
      by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A
      · rw [if_pos hiA, if_pos hjA] at hij; exact Sum.inl.inj hij
      · rw [if_pos hiA, if_neg hjA] at hij; exact (Sum.inl_ne_inr hij).elim
      · rw [if_neg hiA, if_pos hjA] at hij; exact (Sum.inr_ne_inl hij).elim
      · rw [if_neg hiA, if_neg hjA] at hij
        exact hInj hi hj (Sum.inr.inj hij)
  have htarget : (A.image Sum.inl ∪ B.image Sum.inr).card ≤ A.card + B.card := by
    calc (A.image Sum.inl ∪ B.image Sum.inr).card
        ≤ (A.image Sum.inl).card + (B.image Sum.inr).card := Finset.card_union_le _ _
      _ = A.card + B.card := by
          rw [Finset.card_image_of_injective _ Sum.inl_injective,
            Finset.card_image_of_injective _ Sum.inr_injective]
  exact le_trans hbound htarget

/-- **König–Egerváry theorem (certificate form).** For every finite bipartite
family `t : ι → Finset α` there are a matching `(J, f)` and a vertex cover
`(A, B)` of **equal size** `#J = #A + #B`; consequently `(J, f)` is a *maximum*
matching and `(A, B)` is a *minimum* cover (final two clauses). Hence the maximum
matching size equals the minimum vertex cover size. -/
theorem konig (t : ι → Finset α) :
    ∃ (J : Finset ι) (f : ι → α) (A : Finset ι) (B : Finset α),
      IsMatching t J f ∧ IsVertexCover t A B ∧ J.card = A.card + B.card ∧
      (∀ J' f', IsMatching t J' f' → J'.card ≤ J.card) ∧
      (∀ A' B', IsVertexCover t A' B' → A.card + B.card ≤ A'.card + B'.card) := by
  classical
  -- choose `s` minimising the cover size over all subsets of `ι`
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_min_image univ.powerset (coverSize t) ⟨∅, by simp⟩
  have hmem : ∀ s' : Finset ι, coverSize t s ≤ coverSize t s' := fun s' =>
    hs s' (Finset.mem_powerset.mpr (Finset.subset_univ s'))
  -- `#(ι \ s') = #ι − #s'`
  have hcompl : ∀ s' : Finset ι, (univ \ s').card = Fintype.card ι - s'.card := by
    intro s'
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  have hle : ∀ s' : Finset ι, s'.card ≤ Fintype.card ι := fun s' => Finset.card_le_univ s'
  -- at the minimiser, `#(s.biUnion t) ≤ #s` (else `s = ∅` would be smaller)
  have hNS : (s.biUnion t).card ≤ s.card := by
    have h0 := hmem ∅
    simp only [coverSize, Finset.sdiff_empty, Finset.biUnion_empty, Finset.card_empty,
      add_zero, Finset.card_univ] at h0
    rw [hcompl s] at h0
    have := hle s
    omega
  -- the deficiency `d` realised by `s`
  set d : ℕ := s.card - (s.biUnion t).card with hd
  -- defect Hall hypothesis holds for this `d`, by minimality of `s`
  have Hd : ∀ s' : Finset ι, s'.card ≤ (s'.biUnion t).card + d := by
    intro s'
    have h1 := hmem s'
    simp only [coverSize] at h1
    rw [hcompl s, hcompl s'] at h1
    have := hle s'; have := hle s; have := hNS
    omega
  -- extract the matching of size `≥ #ι − d`
  obtain ⟨J, f, hJcard, hInj, hMem⟩ := HallDefect.exists_matching_of_deficiency_le Hd
  have hMatch : IsMatching t J f := ⟨hInj, hMem⟩
  -- the canonical cover `(ι \ s, s.biUnion t)`
  have hCover : IsVertexCover t (univ \ s) (s.biUnion t) := by
    intro i a ha
    by_cases hi : i ∈ s
    · exact Or.inr (mem_biUnion.mpr ⟨i, hi, ha⟩)
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨mem_univ i, hi⟩)
  -- its size equals `#ι − d`
  have hCcard : (univ \ s).card + (s.biUnion t).card = Fintype.card ι - d := by
    rw [hcompl s, hd]
    have := hle s; have := hNS
    omega
  -- so the matching is at least as large as the cover
  have hge : (univ \ s).card + (s.biUnion t).card ≤ J.card := by
    rw [hCcard]; exact hJcard
  -- weak duality pins the matching size to the cover size
  have heq : J.card = (univ \ s).card + (s.biUnion t).card :=
    le_antisymm (matching_card_le_cover hMatch hCover) hge
  refine ⟨J, f, univ \ s, s.biUnion t, hMatch, hCover, heq, ?_, ?_⟩
  · -- the matching is maximum
    intro J' f' hM'
    exact le_trans (matching_card_le_cover hM' hCover) heq.ge
  · -- the cover is minimum
    intro A' B' hC'
    calc (univ \ s).card + (s.biUnion t).card = J.card := heq.symm
      _ ≤ A'.card + B'.card := matching_card_le_cover hMatch hC'

end HallKonig
