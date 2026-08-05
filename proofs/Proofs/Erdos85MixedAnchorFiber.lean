import Proofs.Erdos85MixedAnchorDiagonal
import Proofs.Erdos85GraphDiagonalAnchor
import Proofs.Erdos85ZModProjectionFiber

/-!
# Fiber partition of the mixed diagonal anchor count

The mod-`p` bookkeeping of the mixed parity engine, per target cycle.
Doubling is a bijection on an odd cycle compatible with reduction mod
`p`, and the diagonal anchor `h ∈ S` is detected by its doubled ordered
difference `2h ∈ ODS(S)`.  Since the diagonal ordered differences avoid
`{0, 1, -1}` (the mixed leave), the projected diagonal count partitions
the admissible fiber:

  `#{h ∈ S : h ≡ s} + #{w ≡ 2s admissible, w ∉ ODS(S)}
      = #{w ≡ 2s admissible}`

and the admissible fiber count is `m/p` minus explicit three-point
corrections.  Combined with the off-cycle dichotomy, the second summand
is exactly the number of `δ`-classes covered by other components — the
quantity the quantization program computes.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The admissible differences of a cycle: everything except `0, ±1`. -/
def admissibleDifferences (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ \ {0, 1, -1}

theorem mem_admissibleDifferences_iff {m : ℕ} [NeZero m] (w : ZMod m) :
    w ∈ admissibleDifferences m ↔ w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 := by
  simp [admissibleDifferences, not_or]

/-- The diagonal ordered differences are admissible: zero is never an
ordered difference, and `±1` would violate the mixed leave. -/
theorem orderedDifferenceSet_diag_subset_admissible
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {m : ℕ} [NeZero m] {v : ZMod m → V}
    (hvinj : Function.Injective v) (hm3 : 3 ≤ m)
    (hvD : ∀ z, (secondOrderDefectGraph G).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    orderedDifferenceSet (mixedAnchorSupport G (v 0) v) ⊆
      admissibleDifferences m := by
  intro w hw
  rw [mem_admissibleDifferences_iff]
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0] at hw
    exact zero_not_mem_orderedDifferenceSet _ hw
  · intro h1
    rw [h1, mem_orderedDifferenceSet_iff_exists_pair _ _ hone] at hw
    obtain ⟨b, hb, hb1⟩ := hw
    exact mixedAnchorSupport_no_consecutive G hfree hd heven hmin hcard
      hvinj hm3 hvD (v 0) b hb hb1
  · intro h2
    have hminus : (-1 : ZMod m) ≠ 0 := neg_ne_zero.mpr hone
    rw [h2, mem_orderedDifferenceSet_iff_exists_pair _ _ hminus] at hw
    obtain ⟨b, hb, hbm⟩ := hw
    have hb' : b - 1 ∈ mixedAnchorSupport G (v 0) v := by
      have : b + -1 = b - 1 := by ring
      rw [← this]
      exact hbm
    have hbp : (b - 1) + 1 ∈ mixedAnchorSupport G (v 0) v := by
      have : (b - 1) + 1 = b := by ring
      rw [this]
      exact hb
    exact mixedAnchorSupport_no_consecutive G hfree hd heven hmin hcard
      hvinj hm3 hvD (v 0) (b - 1) hb' hbp

/-- Doubling carries the diagonal fiber at `s` bijectively onto the
ordered-difference fiber at `2s`. -/
theorem card_diag_fiber_eq_card_ods_fiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {m p : ℕ} [NeZero m] [NeZero p]
    (hm3 : 3 ≤ m) (hmOdd : Odd m) (hdvd : p ∣ m) (hpOdd : Odd p)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {v : ZMod m → V} (hvinj : Function.Injective v)
    (hvRange : Set.range v = c.supp)
    (hvD : ∀ z, (secondOrderDefectGraph G).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : ZMod p) :
    ((mixedAnchorSupport G (v 0) v).filter
      (fun h ↦ ZMod.castHom hdvd (ZMod p) h = s)).card =
    ((orderedDifferenceSet (mixedAnchorSupport G (v 0) v)).filter
      (fun w ↦ ZMod.castHom hdvd (ZMod p) w = 2 * s)).card := by
  have hdouble : ∀ h : ZMod m,
      h ∈ mixedAnchorSupport G (v 0) v ↔
        2 * h ∈ orderedDifferenceSet (mixedAnchorSupport G (v 0) v) := by
    intro h
    rw [mixedAnchorSupport_eq_graphCycleBlockZeroSupport]
    exact mem_graphCycleBlockZeroSupport_self_iff_two_mul_difference
      G hfree hd heven hmin hcard hm3 hmOdd c v hvinj hvRange hvD h
  have htwo_m : IsUnit (2 : ZMod m) := by
    simpa using (ZMod.isUnit_iff_coprime 2 m).mpr
      (Nat.coprime_two_left.mpr hmOdd)
  have htwo_p : IsUnit (2 : ZMod p) := by
    simpa using (ZMod.isUnit_iff_coprime 2 p).mpr
      (Nat.coprime_two_left.mpr hpOdd)
  apply Finset.card_bij (fun h _ ↦ 2 * h)
  · intro h hh
    rw [Finset.mem_filter] at hh ⊢
    refine ⟨(hdouble h).mp hh.1, ?_⟩
    rw [map_mul, map_ofNat, hh.2]
  · intro h₁ hh₁ h₂ hh₂ heq
    exact htwo_m.mul_left_cancel heq
  · intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨u2, hu2⟩ := htwo_m
    have h2w : 2 * ((u2⁻¹ : (ZMod m)ˣ) * w) = w := by
      rw [← hu2, ← mul_assoc]
      simp
    refine ⟨(u2⁻¹ : (ZMod m)ˣ) * w, ?_, h2w⟩
    rw [Finset.mem_filter]
    constructor
    · rw [hdouble, h2w]
      exact hw.1
    · apply htwo_p.mul_left_cancel
      have hcast2 : (ZMod.castHom hdvd (ZMod p))
          (2 * ((u2⁻¹ : (ZMod m)ˣ) * w)) =
          2 * (ZMod.castHom hdvd (ZMod p)) ((u2⁻¹ : (ZMod m)ˣ) * w) := by
        rw [map_mul, map_ofNat]
      rw [← hcast2, h2w, hw.2]

/-- **The fiber partition.**  On an odd target cycle with `p ∣ m`, the
projected diagonal anchor count at `s` plus the non-diagonal admissible
classes at `2s` equals the full admissible fiber at `2s`. -/
theorem diag_fiber_add_complement_eq_admissible_fiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {m p : ℕ} [NeZero m] [NeZero p]
    (hm3 : 3 ≤ m) (hmOdd : Odd m) (hdvd : p ∣ m) (hpOdd : Odd p)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {v : ZMod m → V} (hvinj : Function.Injective v)
    (hvRange : Set.range v = c.supp)
    (hvD : ∀ z, (secondOrderDefectGraph G).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : ZMod p) :
    ((mixedAnchorSupport G (v 0) v).filter
        (fun h ↦ ZMod.castHom hdvd (ZMod p) h = s)).card +
      (((admissibleDifferences m).filter
        (fun w ↦ ZMod.castHom hdvd (ZMod p) w = 2 * s ∧
          w ∉ orderedDifferenceSet (mixedAnchorSupport G (v 0) v))).card)
      = ((admissibleDifferences m).filter
          (fun w ↦ ZMod.castHom hdvd (ZMod p) w = 2 * s)).card := by
  rw [card_diag_fiber_eq_card_ods_fiber G hfree hd heven hmin hcard hm3
    hmOdd hdvd hpOdd c hvinj hvRange hvD s]
  have hsub := orderedDifferenceSet_diag_subset_admissible G hfree hd
    heven hmin hcard hvinj hm3 hvD
  have hods : ((orderedDifferenceSet (mixedAnchorSupport G (v 0) v)).filter
      (fun w ↦ ZMod.castHom hdvd (ZMod p) w = 2 * s)).card =
      (((admissibleDifferences m).filter
        (fun w ↦ ZMod.castHom hdvd (ZMod p) w = 2 * s ∧
          w ∈ orderedDifferenceSet (mixedAnchorSupport G (v 0) v))).card) := by
    congr 1
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, hc⟩
      exact ⟨hsub hw, hc, hw⟩
    · rintro ⟨_, hc, hw⟩
      exact ⟨hw, hc⟩
  rw [hods]
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (admissibleDifferences m).filter
      (fun w ↦ ZMod.castHom hdvd (ZMod p) w = 2 * s))
    (p := fun w ↦
      w ∈ orderedDifferenceSet (mixedAnchorSupport G (v 0) v))
  rw [Finset.filter_filter, Finset.filter_filter] at hpart
  exact hpart

/-- The admissible fiber count: `m / p` minus the explicit three-point
corrections. -/
theorem card_admissible_fiber
    {m p : ℕ} [NeZero m] [NeZero p]
    (hm3 : 3 ≤ m) (hdvd : p ∣ m) (hp7 : 7 ≤ p) (t : ZMod p) :
    ((admissibleDifferences m).filter
      (fun w ↦ ZMod.castHom hdvd (ZMod p) w = t)).card
      = m / p - ((if t = 0 then 1 else 0) + (if t = 1 then 1 else 0) +
          (if t = -1 then 1 else 0)) := by
  classical
  have hfull : (Finset.univ.filter
      (fun w : ZMod m ↦ ZMod.castHom hdvd (ZMod p) w = t)).card = m / p := by
    have := card_projectionFiber_zmod_castHom hdvd t
    rw [← this, projectionFiber]
  have hsplit : (admissibleDifferences m).filter
      (fun w ↦ ZMod.castHom hdvd (ZMod p) w = t) =
      (Finset.univ.filter
        (fun w : ZMod m ↦ ZMod.castHom hdvd (ZMod p) w = t)) \
        (({0, 1, -1} : Finset (ZMod m)).filter
          (fun w ↦ ZMod.castHom hdvd (ZMod p) w = t)) := by
    ext w
    simp only [admissibleDifferences, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  rw [hsplit, Finset.card_sdiff_of_subset (by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ w, hw.2⟩), hfull]
  congr 1
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have hmone : (-1 : ZMod m) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination -h
    have := Nat.le_of_dvd (by norm_num)
      ((ZMod.natCast_eq_zero_iff 2 m).mp h2)
    omega
  have hmone0 : (-1 : ZMod m) ≠ 0 := neg_ne_zero.mpr hone
  have hc0 : (ZMod.castHom hdvd (ZMod p)) (0 : ZMod m) = 0 := map_zero _
  have hc1 : (ZMod.castHom hdvd (ZMod p)) (1 : ZMod m) = 1 := map_one _
  have hcm : (ZMod.castHom hdvd (ZMod p)) (-1 : ZMod m) = -1 := by
    rw [map_neg, map_one]
  have hp1 : (1 : ZMod p) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have hpm1 : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -h
    have := Nat.le_of_dvd (by norm_num)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
    omega
  have hpm0 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr hp1
  rw [Finset.card_filter]
  rw [show ({0, 1, -1} : Finset (ZMod m)) =
    insert (0 : ZMod m) (insert (1 : ZMod m) ({-1} : Finset (ZMod m)))
    from rfl]
  rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hone.symm, hmone0.symm⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact hmone.symm),
    Finset.sum_singleton]
  rw [hc0, hc1, hcm]
  have e0 : ((0 : ZMod p) = t) = (t = 0) := by
    apply propext; exact eq_comm
  have e1 : ((1 : ZMod p) = t) = (t = 1) := by
    apply propext; exact eq_comm
  have e2 : ((-1 : ZMod p) = t) = (t = -1) := by
    apply propext; exact eq_comm
  simp only [e0, e1, e2]
  ring

end

end Erdos85
