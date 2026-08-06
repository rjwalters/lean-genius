import Proofs.Erdos85CoverAdmissibleFiberParity
import Proofs.Erdos85MixedComplementComponentSum

/-!
# Parity of unequal mixed-cycle block fibers
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- For a positive block from a shorter source, the full-mass fiber is
literally the admissible source-divisibility fiber. -/
theorem shorter_positive_fullMass_fiber_eq_divisibility_fiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ a : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero a.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c e)
    (t : ZMod p) (hpe : p ∣ e.supp.ncard) :
    (admissibleDifferences e.supp.ncard).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t ∧
          (∑ z : ZMod c.supp.ncard,
            anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard) =
      (admissibleDifferences e.supp.ncard).filter (fun δ ↦
        ZMod.castHom hpe (ZMod p) δ = t ∧ c.supp.ncard ∣ δ.val) := by
  have hdiv := secondOrder_componentQuotientMatrix_pos_imp_size_dvd_or_dvd
    G hfree hd heven hmin hcard c e hpos
  have hrn : c.supp.ncard ∣ e.supp.ncard := hdiv.resolve_right (by
    intro h
    have := Nat.le_of_dvd c.nonempty_supp.ncard_pos h
    omega)
  have hmass := sum_anchorPairMultiplicity_shorter_positive_eq_ite_dvd
    G hfree hd heven hmin hcard (hℓ3 c) (hℓ3 e) c e hlt hpos
      (u c) (u e) (hu c) (hu e) (huRange c) (huRange e)
      (huD c) (huD e)
  ext δ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hadm, hcast, hfull⟩
    refine ⟨hadm, ?_, ?_⟩
    · simpa [zmod_castHom_eq_val_cast hpe] using hcast
    · rw [hmass δ] at hfull
      split_ifs at hfull with hdvd
      · exact hdvd
      · exact False.elim ((NeZero.ne e.supp.ncard) hfull.symm)
  · rintro ⟨hadm, hcast, hdvd⟩
    refine ⟨hadm, ?_, ?_⟩
    · simpa [zmod_castHom_eq_val_cast hpe] using hcast
    · rw [hmass δ, if_pos hdvd]

/-- A shorter zero quotient block has no admissible full-mass classes. -/
theorem shorter_zero_fullMass_fiber_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ a : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero a.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hq0 : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0)
    (t : ZMod p) :
    (admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard) = ∅ := by
  ext δ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hadm, _, hmass⟩
    exfalso
    have hδ0 := (mem_admissibleDifferences_iff δ).mp hadm |>.1
    have hz := sum_anchorPairMultiplicity_shorter_zero_eq_zero G hfree hd
      heven hmin hcard c e (u c) (u e) (hu e) (huRange c) (huRange e)
        hq0 δ hδ0
    rw [hz] at hmass
    exact (NeZero.ne e.supp.ncard) hmass.symm
  · simp

/-- A longer source block has no admissible full-mass classes. -/
theorem longer_fullMass_fiber_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ a : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero a.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hgt : e.supp.ncard < c.supp.ncard) (t : ZMod p) :
    (admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard) = ∅ := by
  ext δ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hadm, _, hmass⟩
    exfalso
    have hδ0 := (mem_admissibleDifferences_iff δ).mp hadm |>.1
    have hz := sum_anchorPairMultiplicity_longer_eq_zero G hfree hd heven
      hmin hcard c e hgt (u c) (u e) (hu e) (huRange c) (huRange e)
        δ hδ0
    rw [hz] at hmass
    exact (NeZero.ne e.supp.ncard) hmass.symm
  · simp

end

end Erdos85
