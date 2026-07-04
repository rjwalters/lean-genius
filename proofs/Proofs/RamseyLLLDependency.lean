/-
# The LLL Dependency-Degree Bound for Monochromatic-Clique Events

This file supplies the one combinatorial ingredient that the gallery entry
`ramsey-r4k-extensions` (Part VII, Spencer's improved diagonal Ramsey bound)
*asserts without proof*: when the Lovász Local Lemma is applied to the events

  `A_S = "the k-subset S ⊆ [n] is monochromatic"`

each event `A_S` is mutually independent of all `A_T` except those whose index
set `T` shares at least two vertices with `S` (sharing `≤ 1` vertex means the two
cliques share no edge, so the colourings of their edge sets are independent).
The **dependency degree** `d` fed into the symmetric LLL condition
`e·p·(d+1) ≤ 1` is therefore the number of `k`-sets `T ≠ S` with `|S ∩ T| ≥ 2`,
and the textbook (Alon–Spencer, *The Probabilistic Method*, §5.5) upper bound for
it is

  `d ≤ C(k,2) · C(n-2, k-2)`.

That is exactly what is proved here, purely as a finite `Finset` cardinality
statement over an arbitrary `Fintype`:

* `card_supersets` — for a fixed `P` with `|P| ≤ k`, the number of `k`-subsets of
  a `Fintype α` containing `P` is `C(|α| - |P|, k - |P|)`. Proved by the explicit
  bijection `T ↦ T \ P` (inverse `U ↦ U ∪ P`) onto the `(k-|P|)`-subsets of the
  `|α|-|P|` points outside `P`.
* `card_dependency_le` — for `|S| = k` and `k ≥ 2`, the number of `k`-subsets `T`
  with `T ≠ S` and `|S ∩ T| ≥ 2` is at most `C(k,2) · C(|α|-2, k-2)`. Proved by
  covering the dependency set by the supersets of the `2`-element subsets of `S`
  (every `T` sharing `≥ 2` vertices with `S` contains some `2`-subset of `S`) and
  bounding the cover by `card_supersets`.

Everything is `sorry`-free and axiom-free. Specialised to `|α| = n` this is the
`d ≤ C(k,2)·C(n-2,k-2)` used to instantiate `e·p·(d+1) ≤ 1` in Spencer's argument.

Erdős & Lovász (1975); Spencer (1977); Alon & Spencer, *The Probabilistic Method*.
-/
import Mathlib

open Finset

namespace RamseyLLLDependency

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Counting the `k`-subsets containing a fixed set `P`.**
For `P : Finset α` with `|P| ≤ k`, the number of `k`-element subsets of `α`
that contain `P` is `C(|α| - |P|, k - |P|)`.

The bijection `T ↦ T \ P` (with inverse `U ↦ U ∪ P`) matches the supersets of
`P` with the `(k - |P|)`-element subsets of the `|α| - |P|` points outside `P`. -/
theorem card_supersets (P : Finset α) (k : ℕ) (hPk : P.card ≤ k) :
    ((univ.powersetCard k).filter (fun T => P ⊆ T)).card
      = (Fintype.card α - P.card).choose (k - P.card) := by
  have hbij :
      ((univ.powersetCard k).filter (fun T => P ⊆ T)).card
        = ((univ \ P).powersetCard (k - P.card)).card := by
    apply Finset.card_bij'
      (fun T _ => T \ P) (fun U _ => U ∪ P)
    · -- forward: T ↦ T \ P lands in the (k-|P|)-subsets of univ \ P
      intro T hT
      rw [mem_filter, mem_powersetCard] at hT
      obtain ⟨⟨_, hTcard⟩, hPT⟩ := hT
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [mem_sdiff] at hx
        exact mem_sdiff.mpr ⟨mem_univ x, hx.2⟩
      · rw [card_sdiff, hTcard, Finset.inter_eq_left.mpr hPT]
    · -- backward: U ↦ U ∪ P lands in the k-subsets containing P
      intro U hU
      rw [mem_powersetCard] at hU
      obtain ⟨hUsub, hUcard⟩ := hU
      have hd : Disjoint U P :=
        Finset.disjoint_left.mpr fun x hxU hxP => (mem_sdiff.mp (hUsub hxU)).2 hxP
      rw [mem_filter, mem_powersetCard]
      refine ⟨⟨subset_univ _, ?_⟩, subset_union_right⟩
      rw [card_union_of_disjoint hd, hUcard]
      omega
    · -- left inverse: (T \ P) ∪ P = T because P ⊆ T
      intro T hT
      rw [mem_filter] at hT
      have hPT : P ⊆ T := hT.2
      ext x
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro (⟨hx, _⟩ | hx)
        · exact hx
        · exact hPT hx
      · intro hx
        by_cases hxP : x ∈ P
        · exact Or.inr hxP
        · exact Or.inl ⟨hx, hxP⟩
    · -- right inverse: (U ∪ P) \ P = U because U is disjoint from P
      intro U hU
      rw [mem_powersetCard] at hU
      have hUsub : U ⊆ univ \ P := hU.1
      ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hx | hx, hxnP⟩
        · exact hx
        · exact absurd hx hxnP
      · intro hx
        exact ⟨Or.inl hx, fun hxP => (mem_sdiff.mp (hUsub hx)).2 hxP⟩
  have huniv : (univ \ P).card = Fintype.card α - P.card := by
    rw [card_sdiff, Finset.inter_univ, card_univ]
  rw [hbij, card_powersetCard, huniv]

/-- **The LLL dependency-degree bound for monochromatic-clique events.**
Let `S` be a `k`-element set (`|S| = k`) with `k ≥ 2`. The number of `k`-element
sets `T` that are *dependent* on `S` — i.e. `T ≠ S` and `|S ∩ T| ≥ 2`, so the
cliques on `S` and `T` share an edge — is at most `C(k,2) · C(|α|-2, k-2)`.

This is the degree `d` used in the symmetric LLL condition `e·p·(d+1) ≤ 1` in
Spencer's improved diagonal Ramsey lower bound. -/
theorem card_dependency_le (S : Finset α) (k : ℕ) (hS : S.card = k) (hk : 2 ≤ k) :
    ((univ.powersetCard k).filter (fun T => T ≠ S ∧ 2 ≤ (S ∩ T).card)).card
      ≤ k.choose 2 * (Fintype.card α - 2).choose (k - 2) := by
  -- Cover the dependency set by the k-supersets of the 2-subsets of S.
  set B := (S.powersetCard 2).biUnion
      (fun P => (univ.powersetCard k).filter (fun T => P ⊆ T)) with hB
  have hsub :
      (univ.powersetCard k).filter (fun T => T ≠ S ∧ 2 ≤ (S ∩ T).card) ⊆ B := by
    intro T hT
    rw [mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨hTsub, hTcard⟩, _, hcap⟩ := hT
    -- pick a 2-element subset P of S ∩ T
    obtain ⟨P, hPmem⟩ := Finset.powersetCard_nonempty.mpr hcap
    rw [mem_powersetCard] at hPmem
    obtain ⟨hPsub, hPcard⟩ := hPmem
    rw [hB, mem_biUnion]
    refine ⟨P, ?_, ?_⟩
    · rw [mem_powersetCard]
      exact ⟨hPsub.trans inter_subset_left, hPcard⟩
    · rw [mem_filter, mem_powersetCard]
      exact ⟨⟨hTsub, hTcard⟩, hPsub.trans inter_subset_right⟩
  calc
    ((univ.powersetCard k).filter (fun T => T ≠ S ∧ 2 ≤ (S ∩ T).card)).card
        ≤ B.card := card_le_card hsub
    _ ≤ ∑ P ∈ S.powersetCard 2,
          ((univ.powersetCard k).filter (fun T => P ⊆ T)).card := card_biUnion_le
    _ = ∑ _P ∈ S.powersetCard 2, (Fintype.card α - 2).choose (k - 2) := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [mem_powersetCard] at hP
        have hPc : P.card = 2 := hP.2
        rw [card_supersets P k (by rw [hPc]; exact hk), hPc]
    _ = (S.powersetCard 2).card * (Fintype.card α - 2).choose (k - 2) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = k.choose 2 * (Fintype.card α - 2).choose (k - 2) := by
        rw [card_powersetCard, hS]

end RamseyLLLDependency
