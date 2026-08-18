import Proofs.Erdos85MixedAnchorSupport

/-!
# The diagonal split of the aggregated mixed cover

On an odd target cycle the diagonal block is circulant, so all on-cycle
anchors have the same pair multiplicity, equal (by the Sidon property) to
the indicator of the difference being a diagonal ordered difference.
Subtracting from the aggregated cover yields a sharp dichotomy: for every
admissible difference `δ ∉ {0, 1, -1}`,

* either `δ` is an ordered difference of the diagonal support and then
  **no** off-cycle anchor covers any `δ`-pair,
* or `δ` is not, and then the off-cycle anchors cover **all** `ℓ` pairs.

This is the exact-cover half of the mixed-length parity engine; only the
distribution of the off-cycle mass among the other components (the
rectangular transpose relation) remains beyond it.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On a cycle whose diagonal block is translation invariant, anchor
supports translate: `S(v t) = S(v 0) + t`. -/
theorem mem_mixedAnchorSupport_translate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hshift : ∀ x y : ZMod m,
      G.Adj (v (x + 1)) (v (y + 1)) ↔ G.Adj (v x) (v y))
    (t s : ZMod m) :
    s ∈ mixedAnchorSupport G (v t) v ↔
      s - t ∈ mixedAnchorSupport G (v 0) v := by
  have hn : ∀ (n : ℕ) (x y : ZMod m),
      G.Adj (v (x + (n : ZMod m))) (v (y + (n : ZMod m))) ↔
        G.Adj (v x) (v y) := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      have hx : x + ((n + 1 : ℕ) : ZMod m) = (x + (n : ZMod m)) + 1 := by
        push_cast; ring
      have hy : y + ((n + 1 : ℕ) : ZMod m) = (y + (n : ZMod m)) + 1 := by
        push_cast; ring
      rw [hx, hy, hshift, ih]
  rw [mem_mixedAnchorSupport_iff, mem_mixedAnchorSupport_iff]
  have h := hn t.val 0 (s - t)
  rw [ZMod.natCast_rightInverse t, zero_add, sub_add_cancel] at h
  exact h

/-- Translation invariance makes all on-cycle pair multiplicities equal
to the base-point multiplicity. -/
theorem anchorPairMultiplicity_translate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hshift : ∀ x y : ZMod m,
      G.Adj (v (x + 1)) (v (y + 1)) ↔ G.Adj (v x) (v y))
    (t δ : ZMod m) :
    anchorPairMultiplicity G (v t) v δ =
      anchorPairMultiplicity G (v 0) v δ := by
  rw [anchorPairMultiplicity, anchorPairMultiplicity]
  apply Finset.card_bij (fun s _ ↦ s - t)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨hs1, hs2⟩ := hs
    rw [mem_mixedAnchorSupport_translate G hshift t s] at hs1
    rw [mem_mixedAnchorSupport_translate G hshift t (s + δ)] at hs2
    refine ⟨hs1, ?_⟩
    have harg : s + δ - t = s - t + δ := by ring
    rw [harg] at hs2
    exact hs2
  · intro s₁ h₁ s₂ h₂ h
    linear_combination h
  · intro w hw
    rw [Finset.mem_filter] at hw
    refine ⟨w + t, Finset.mem_filter.mpr ⟨?_, ?_⟩, by ring⟩
    · rw [mem_mixedAnchorSupport_translate G hshift t (w + t)]
      have h1 : w + t - t = w := by ring
      rw [h1]
      exact hw.1
    · rw [mem_mixedAnchorSupport_translate G hshift t (w + t + δ)]
      have h2 : w + t + δ - t = w + δ := by ring
      rw [h2]
      exact hw.2

/-- Membership in the ordered difference set through a `δ`-pair. -/
theorem mem_orderedDifferenceSet_iff_exists_pair
    {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (δ : ZMod m) (hδ : δ ≠ 0) :
    δ ∈ orderedDifferenceSet A ↔ ∃ b ∈ A, b + δ ∈ A := by
  constructor
  · intro h
    rw [orderedDifferenceSet, Finset.mem_image] at h
    obtain ⟨p, hp, hpd⟩ := h
    rw [mem_orderedDistinctPairs_iff] at hp
    refine ⟨p.2, hp.2.1, ?_⟩
    have hδ' : p.1 - p.2 = δ := hpd
    have hsum : p.2 + δ = p.1 := by linear_combination -hδ'
    rw [hsum]
    exact hp.1
  · rintro ⟨b, hb, hbδ⟩
    rw [orderedDifferenceSet, Finset.mem_image]
    refine ⟨(b + δ, b), ?_, ?_⟩
    · rw [mem_orderedDistinctPairs_iff]
      exact ⟨hbδ, hb, fun h ↦ hδ (by linear_combination h)⟩
    · show b + δ - b = δ
      ring

/-- Sidon reduces the base-point pair multiplicity to the indicator of a
diagonal ordered difference. -/
theorem anchorPairMultiplicity_zero_eq_indicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hsidon : IsOrderedSidon (mixedAnchorSupport G (v 0) v))
    (δ : ZMod m) (hδ : δ ≠ 0) :
    anchorPairMultiplicity G (v 0) v δ =
      if δ ∈ orderedDifferenceSet (mixedAnchorSupport G (v 0) v)
      then 1 else 0 := by
  set A := mixedAnchorSupport G (v 0) v with hA
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

/-- **The off-cycle dichotomy.**  On an odd target cycle, for every
admissible difference: either `δ` is a diagonal ordered difference and no
off-cycle anchor covers any `δ`-pair, or it is not and the off-cycle
anchors cover all `m` pairs. -/
theorem sum_offCycle_anchorPairMultiplicity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hvinj : Function.Injective v) (hm3 : 3 ≤ m) (hmOdd : Odd m)
    (hvD : ∀ z, (secondOrderDefectGraph G).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (δ : ZMod m) (hδ0 : δ ≠ 0) (hδ1 : δ ≠ 1) (hδ2 : δ ≠ -1) :
    ∑ x ∈ Finset.univ.filter (fun x : V ↦ x ∉ Set.range v),
      anchorPairMultiplicity G x v δ =
      if δ ∈ orderedDifferenceSet (mixedAnchorSupport G (v 0) v)
      then 0 else m := by
  have hshift : ∀ x y : ZMod m,
      G.Adj (v (x + 1)) (v (y + 1)) ↔ G.Adj (v x) (v y) :=
    graph_equalOddCycle_diagBlock_adj_shift_iff hm3 hmOdd G
      (secondOrderDefectGraph G) v hvinj
      (adjMatrix_comm_secondOrderDefect_of_even
        G hfree hd heven hmin hcard) hvD
  have hOrient := graph_equalOddCycleBlock_orientation hm3 hmOdd G
    (secondOrderDefectGraph G) v v hvinj hvinj
    (adjMatrix_comm_secondOrderDefect_of_even
      G hfree hd heven hmin hcard) hvD hvD
  have hsidon : IsOrderedSidon (mixedAnchorSupport G (v 0) v) := by
    rw [mixedAnchorSupport_eq_graphCycleBlockZeroSupport]
    exact isOrderedSidon_zeroRowSupport_of_c4Free_orientation
      G hfree v v hvinj hvinj hOrient
  have htotal := sum_anchorPairMultiplicity_eq_length
    G hfree hd heven hmin hcard hvinj hvD δ hδ0 hδ1 hδ2
  have hsplit : ∑ x : V, anchorPairMultiplicity G x v δ =
      (∑ x ∈ Finset.univ.filter (fun x : V ↦ x ∈ Set.range v),
        anchorPairMultiplicity G x v δ) +
      ∑ x ∈ Finset.univ.filter (fun x : V ↦ x ∉ Set.range v),
        anchorPairMultiplicity G x v δ :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have hon : ∑ x ∈ Finset.univ.filter (fun x : V ↦ x ∈ Set.range v),
      anchorPairMultiplicity G x v δ =
      m * anchorPairMultiplicity G (v 0) v δ := by
    have himage : Finset.univ.filter (fun x : V ↦ x ∈ Set.range v) =
        Finset.univ.image v := by
      ext x
      simp [Set.mem_range, eq_comm]
    rw [himage, Finset.sum_image (fun t _ s _ h ↦ hvinj h)]
    rw [Finset.sum_congr rfl fun t _ ↦
      anchorPairMultiplicity_translate G hshift t δ,
      Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  have hind := anchorPairMultiplicity_zero_eq_indicator G hsidon δ hδ0
  rw [hsplit, hon, hind] at htotal
  split_ifs at htotal ⊢ with hmem
  · omega
  · omega

end

end Erdos85
