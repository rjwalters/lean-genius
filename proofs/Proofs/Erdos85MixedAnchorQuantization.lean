import Proofs.Erdos85MixedAnchorFiber
import Proofs.Erdos85CycleCoverPairMass

/-!
# Pair-mass quantization: equal-size and singleton blocks

The two remaining block types of the mixed pair-mass quantization
program, complementing the cyclic-cover case of
`Erdos85CycleCoverPairMass`:

* **singleton blocks** (each anchor has at most one neighbor on the
  target cycle — the `Q(c,e) ≤ 1` direction of a covering pair seen from
  the small side): the pair mass vanishes at every nonzero difference;
* **equal-size blocks**: under either global orientation the row
  supports are translates, so the pair multiplicity is constant along
  the source cycle and, by the rectangular Sidon property, equals the
  indicator of a block ordered difference.  The mass is
  `ℓ · [δ ∈ ODS(block)] ∈ {0, ℓ}`.

Together with the covering case, every block of the second-order defect
decomposition has quantized pair mass.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Singleton block mass.**  If every anchor on the source cycle has at
most one neighbor on the target cycle, the pair mass vanishes at every
nonzero difference. -/
theorem sum_anchorPairMultiplicity_of_singleton
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r n : ℕ} [NeZero r] [NeZero n]
    (u : ZMod r → V) (v : ZMod n → V)
    (hcard : ∀ x, (mixedAnchorSupport G (u x) v).card ≤ 1)
    (δ : ZMod n) (hδ : δ ≠ 0) :
    ∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rw [anchorPairMultiplicity, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro t ht htδ
  have hne : t ≠ t + δ := fun h ↦ hδ (by linear_combination -h)
  have h2 : 2 ≤ (mixedAnchorSupport G (u x) v).card := by
    have hsub : ({t, t + δ} : Finset (ZMod n)) ⊆
        mixedAnchorSupport G (u x) v := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ht
      · rw [Finset.mem_singleton.mp hw]
        exact htδ
    calc 2 = ({t, t + δ} : Finset (ZMod n)).card := by
          rw [Finset.card_insert_of_notMem (by simpa using hne),
            Finset.card_singleton]
      _ ≤ _ := Finset.card_le_card hsub
  have := hcard x
  omega

/-- Row supports of a rectangular block translate under either global
orientation: `S(u t) = S(u 0) + ε t`. -/
theorem mem_mixedAnchorSupport_rect_translate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} [NeZero m] {u v : ZMod m → V} {ε : ZMod m}
    (hshift : ∀ x s : ZMod m,
      G.Adj (u (x + 1)) (v (s + ε)) ↔ G.Adj (u x) (v s))
    (t s : ZMod m) :
    s ∈ mixedAnchorSupport G (u t) v ↔
      s - ε * t ∈ mixedAnchorSupport G (u 0) v := by
  have hn : ∀ (k : ℕ) (x s : ZMod m),
      G.Adj (u (x + (k : ZMod m))) (v (s + ε * (k : ZMod m))) ↔
        G.Adj (u x) (v s) := by
    intro k
    induction k with
    | zero => intro x s; simp
    | succ k ih =>
      intro x s
      have hx : x + ((k + 1 : ℕ) : ZMod m) = (x + (k : ZMod m)) + 1 := by
        push_cast; ring
      have hs : s + ε * ((k + 1 : ℕ) : ZMod m) =
          (s + ε * (k : ZMod m)) + ε := by
        push_cast; ring
      rw [hx, hs, hshift, ih]
  rw [mem_mixedAnchorSupport_iff, mem_mixedAnchorSupport_iff]
  have h := hn t.val 0 (s - ε * t)
  rw [ZMod.natCast_rightInverse t, zero_add] at h
  have harg : s - ε * t + ε * t = s := by ring
  rw [harg] at h
  exact h

/-- Pair multiplicities are constant along the source cycle of a
translating block. -/
theorem anchorPairMultiplicity_rect_translate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} [NeZero m] {u v : ZMod m → V} {ε : ZMod m}
    (hshift : ∀ x s : ZMod m,
      G.Adj (u (x + 1)) (v (s + ε)) ↔ G.Adj (u x) (v s))
    (t δ : ZMod m) :
    anchorPairMultiplicity G (u t) v δ =
      anchorPairMultiplicity G (u 0) v δ := by
  rw [anchorPairMultiplicity, anchorPairMultiplicity]
  apply Finset.card_bij (fun s _ ↦ s - ε * t)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨hs1, hs2⟩ := hs
    rw [mem_mixedAnchorSupport_rect_translate G hshift t s] at hs1
    rw [mem_mixedAnchorSupport_rect_translate G hshift t (s + δ)] at hs2
    refine ⟨hs1, ?_⟩
    have harg : s + δ - ε * t = s - ε * t + δ := by ring
    rw [harg] at hs2
    exact hs2
  · intro s₁ h₁ s₂ h₂ h
    linear_combination h
  · intro w hw
    rw [Finset.mem_filter] at hw
    refine ⟨w + ε * t, Finset.mem_filter.mpr ⟨?_, ?_⟩, by ring⟩
    · rw [mem_mixedAnchorSupport_rect_translate G hshift t (w + ε * t)]
      have h1 : w + ε * t - ε * t = w := by ring
      rw [h1]
      exact hw.1
    · rw [mem_mixedAnchorSupport_rect_translate G hshift t (w + ε * t + δ)]
      have h2 : w + ε * t + δ - ε * t = w + δ := by ring
      rw [h2]
      exact hw.2

/-- Sidon reduces any anchor's pair multiplicity to the ordered-difference
indicator of its support. -/
theorem anchorPairMultiplicity_eq_indicator_of_sidon
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} [NeZero m] (x : V) (v : ZMod m → V)
    (hsidon : IsOrderedSidon (mixedAnchorSupport G x v))
    (δ : ZMod m) (hδ : δ ≠ 0) :
    anchorPairMultiplicity G x v δ =
      if δ ∈ orderedDifferenceSet (mixedAnchorSupport G x v)
      then 1 else 0 := by
  set A := mixedAnchorSupport G x v with hA
  rw [anchorPairMultiplicity]
  split_ifs with hmem
  · obtain ⟨b, hb, hbδ⟩ :=
      (mem_orderedDifferenceSet_iff_exists_pair A δ hδ).mp hmem
    rw [Finset.card_eq_one]
    refine ⟨b, ?_⟩
    ext s
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, hsδ⟩
      have hpair1 : ((s + δ, s) : ZMod m × ZMod m) ∈
          orderedDistinctPairs A := by
        rw [mem_orderedDistinctPairs_iff]
        exact ⟨hsδ, hs, fun h ↦ hδ (by linear_combination h)⟩
      have hpair2 : ((b + δ, b) : ZMod m × ZMod m) ∈
          orderedDistinctPairs A := by
        rw [mem_orderedDistinctPairs_iff]
        exact ⟨hbδ, hb, fun h ↦ hδ (by linear_combination h)⟩
      have hdiff : (fun p : ZMod m × ZMod m ↦ p.1 - p.2) (s + δ, s) =
          (fun p : ZMod m × ZMod m ↦ p.1 - p.2) (b + δ, b) := by
        show (s + δ) - s = (b + δ) - b
        ring
      have := hsidon (Finset.mem_coe.mpr hpair1)
        (Finset.mem_coe.mpr hpair2) hdiff
      exact congrArg Prod.snd this
    · rintro rfl
      exact ⟨hb, hbδ⟩
  · rw [Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hsδ
    exact hmem ((mem_orderedDifferenceSet_iff_exists_pair A δ hδ).mpr
      ⟨s, hs, hsδ⟩)

/-- **Equal-size block mass quantization.**  For two equal-length odd
defect cycles of a commuting two-factor, the pair mass of the rectangular
block is `m` times the ordered-difference indicator of the base row —
in particular it lies in `{0, m}`. -/
theorem sum_anchorPairMultiplicity_of_equalSize
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    {m : ℕ} [NeZero m] (hm3 : 3 ≤ m) (hmOdd : Odd m)
    (u v : ZMod m → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hvD : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)})
    (hfree : ¬ containsC4 V G)
    (δ : ZMod m) (hδ : δ ≠ 0) :
    ∑ x : ZMod m, anchorPairMultiplicity G (u x) v δ =
      if δ ∈ orderedDifferenceSet (mixedAnchorSupport G (u 0) v)
      then m else 0 := by
  have hOrient := graph_equalOddCycleBlock_orientation hm3 hmOdd G D
    u v huinj hvinj hcomm huD hvD
  have hshift : ∃ ε : ZMod m, ∀ x s : ZMod m,
      G.Adj (u (x + 1)) (v (s + ε)) ↔ G.Adj (u x) (v s) := by
    rcases hOrient with hcirc | hrev
    · refine ⟨1, fun x s ↦ ?_⟩
      have h := hcirc x s
      simp only [SimpleGraph.adjMatrix_apply] at h
      by_cases h1 : G.Adj (u (x + 1)) (v (s + 1)) <;>
        by_cases h2 : G.Adj (u x) (v s) <;> simp [h1, h2] at h ⊢
    · refine ⟨-1, fun x s ↦ ?_⟩
      have h := hrev x s
      simp only [SimpleGraph.adjMatrix_apply] at h
      have harg : s + -1 = s - 1 := by ring
      rw [harg]
      by_cases h1 : G.Adj (u (x + 1)) (v (s - 1)) <;>
        by_cases h2 : G.Adj (u x) (v s) <;> simp [h1, h2] at h ⊢
  obtain ⟨ε, hε⟩ := hshift
  have hsidon : IsOrderedSidon (mixedAnchorSupport G (u 0) v) := by
    rw [mixedAnchorSupport_eq_graphCycleBlockZeroSupport]
    exact isOrderedSidon_zeroRowSupport_of_c4Free_orientation
      G hfree u v huinj hvinj hOrient
  rw [Finset.sum_congr rfl fun x _ ↦
    anchorPairMultiplicity_rect_translate G hε x δ,
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul,
    anchorPairMultiplicity_eq_indicator_of_sidon G (u 0) v hsidon δ hδ]
  split_ifs <;> simp

/-- Set-valued form of the equal-size quantization. -/
theorem sum_anchorPairMultiplicity_of_equalSize_mem
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    {m : ℕ} [NeZero m] (hm3 : 3 ≤ m) (hmOdd : Odd m)
    (u v : ZMod m → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hvD : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)})
    (hfree : ¬ containsC4 V G)
    (δ : ZMod m) (hδ : δ ≠ 0) :
    (∑ x : ZMod m, anchorPairMultiplicity G (u x) v δ) ∈
      ({0, m} : Set ℕ) := by
  rw [sum_anchorPairMultiplicity_of_equalSize G D hm3 hmOdd u v huinj
    hvinj hcomm huD hvD hfree δ hδ]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

end

end Erdos85
