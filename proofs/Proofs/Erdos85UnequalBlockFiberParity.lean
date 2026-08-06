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

/-- Every positive unequal cover block has an even full-mass fiber over the
zero residue.  If `p` divides the source length this is `n/r - 1`; otherwise
it is the residual-cover zero-fiber parity theorem. -/
theorem shorter_positive_fullMass_zeroFiber_even
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
    (hp : Nat.Prime p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c e)
    (hpe : p ∣ e.supp.ncard) :
    Even ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = 0 ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard)).card := by
  have hdiv := secondOrder_componentQuotientMatrix_pos_imp_size_dvd_or_dvd
    G hfree hd heven hmin hcard c e hpos
  have hrn : c.supp.ncard ∣ e.supp.ncard := hdiv.resolve_right (by
    intro h
    have := Nat.le_of_dvd c.nonempty_supp.ncard_pos h
    omega)
  rw [shorter_positive_fullMass_fiber_eq_divisibility_fiber G hfree hd
    heven hmin hcard u hu huRange huD hℓ3 c e hlt hpos 0 hpe]
  by_cases hpc : p ∣ c.supp.ncard
  · have hfilt :
        (admissibleDifferences e.supp.ncard).filter (fun δ ↦
          ZMod.castHom hpe (ZMod p) δ = 0 ∧ c.supp.ncard ∣ δ.val) =
        (admissibleDifferences e.supp.ncard).filter
          (fun δ ↦ c.supp.ncard ∣ δ.val) := by
      ext δ
      simp only [Finset.mem_filter]
      constructor
      · exact fun h ↦ ⟨h.1, h.2.2⟩
      · rintro ⟨hadm, hdvd⟩
        exact ⟨hadm,
          castHom_eq_zero_of_sourceLength_dvd_val hpc hrn δ hdvd, hdvd⟩
    rw [hfilt]
    exact even_admissible_sourceLength_dvd (hℓ3 c) hrn (hodd c hpc)
      (hodd e hpe)
  · exact (residual_cover_admissibleFiber_parity hp (hℓ3 c) hrn hpe
      hpc (hodd e hpe) 0).2 rfl

/-- For a nonzero residue and a source length not divisible by `p`, an
unequal block has odd full-mass fiber exactly when its quotient entry is
positive. -/
theorem odd_unequal_residual_fullMass_fiber_iff_quotient_pos
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
    (hp : Nat.Prime p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlen : c.supp.ncard ≠ e.supp.ncard)
    (hpc : ¬ p ∣ c.supp.ncard) (hpe : p ∣ e.supp.ncard)
    (t : ZMod p) (ht : t ≠ 0) :
    Odd ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard)).card ↔
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
  constructor
  · intro hfiber
    by_contra hnpos
    have hq0 : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0 :=
      Nat.eq_zero_of_not_pos hnpos
    rcases lt_or_gt_of_ne hlen with hlt | hgt
    · rw [shorter_zero_fullMass_fiber_eq_empty G hfree hd heven hmin
        hcard u hu huRange c e hq0 t] at hfiber
      exact (Nat.not_odd_iff_even.mpr (by simp)) hfiber
    · rw [longer_fullMass_fiber_eq_empty G hfree hd heven hmin hcard
        u hu huRange c e hgt t] at hfiber
      exact (Nat.not_odd_iff_even.mpr (by simp)) hfiber
  · intro hpos
    have hdiv := secondOrder_componentQuotientMatrix_pos_imp_size_dvd_or_dvd
      G hfree hd heven hmin hcard c e hpos
    have hrn : c.supp.ncard ∣ e.supp.ncard := hdiv.resolve_right (fun h ↦
      hpc (dvd_trans hpe h))
    have hlt : c.supp.ncard < e.supp.ncard :=
      lt_of_le_of_ne (Nat.le_of_dvd e.nonempty_supp.ncard_pos hrn) hlen
    rw [shorter_positive_fullMass_fiber_eq_divisibility_fiber G hfree hd
      heven hmin hcard u hu huRange huD hℓ3 c e hlt hpos t hpe]
    exact (residual_cover_admissibleFiber_parity hp (hℓ3 c) hrn hpe hpc
      (hodd e hpe) t).1 ht

/-- Unequal blocks between two `p`-divisible odd components always have
even full-mass fibers. -/
theorem even_unequal_selected_fullMass_fiber
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
    (hp : Nat.Prime p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlen : c.supp.ncard ≠ e.supp.ncard)
    (hpc : p ∣ c.supp.ncard) (hpe : p ∣ e.supp.ncard)
    (t : ZMod p) :
    Even ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard)).card := by
  by_cases ht : t = 0
  · subst t
    rcases lt_or_gt_of_ne hlen with hlt | hgt
    · by_cases hpos : 0 < componentQuotientMatrix G
          (secondOrderDefectGraph G) c e
      · exact shorter_positive_fullMass_zeroFiber_even G hfree hd heven
          hmin hcard hp u hu huRange huD hℓ3 hodd c e hlt hpos hpe
      · have hq0 := Nat.eq_zero_of_not_pos hpos
        rw [shorter_zero_fullMass_fiber_eq_empty G hfree hd heven hmin
          hcard u hu huRange c e hq0 0]
        simp
    · rw [longer_fullMass_fiber_eq_empty G hfree hd heven hmin hcard
        u hu huRange c e hgt 0]
      simp

  · rcases lt_or_gt_of_ne hlen with hlt | hgt
    · by_cases hpos : 0 < componentQuotientMatrix G
          (secondOrderDefectGraph G) c e
      · have hdiv :=
          secondOrder_componentQuotientMatrix_pos_imp_size_dvd_or_dvd
            G hfree hd heven hmin hcard c e hpos
        have hrn : c.supp.ncard ∣ e.supp.ncard := hdiv.resolve_right (by
          intro h
          have := Nat.le_of_dvd c.nonempty_supp.ncard_pos h
          omega)
        rw [shorter_positive_fullMass_fiber_eq_divisibility_fiber G hfree
          hd heven hmin hcard u hu huRange huD hℓ3 c e hlt hpos t hpe]
        have hfilt :
            (admissibleDifferences e.supp.ncard).filter (fun δ ↦
              ZMod.castHom hpe (ZMod p) δ = t ∧
                c.supp.ncard ∣ δ.val) = ∅ := by
          ext δ
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨_, hcast, hdvd⟩
            exfalso
            have hz := castHom_eq_zero_of_sourceLength_dvd_val hpc hrn δ hdvd
            exact ht (hcast.symm.trans hz)
          · simp
        rw [hfilt]
        simp
      · have hq0 := Nat.eq_zero_of_not_pos hpos
        rw [shorter_zero_fullMass_fiber_eq_empty G hfree hd heven hmin
          hcard u hu huRange c e hq0 t]
        simp
    · rw [longer_fullMass_fiber_eq_empty G hfree hd heven hmin hcard
        u hu huRange c e hgt t]
      simp

/-- At the zero residue, every unequal block into a selected odd target has
even full-mass fiber, with no condition on the source's prime divisibility. -/
theorem even_unequal_fullMass_zeroFiber
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
    (hp : Nat.Prime p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlen : c.supp.ncard ≠ e.supp.ncard) (hpe : p ∣ e.supp.ncard) :
    Even ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = 0 ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard)).card := by
  rcases lt_or_gt_of_ne hlen with hlt | hgt
  · by_cases hpos : 0 < componentQuotientMatrix G
        (secondOrderDefectGraph G) c e
    · exact shorter_positive_fullMass_zeroFiber_even G hfree hd heven
        hmin hcard hp u hu huRange huD hℓ3 hodd c e hlt hpos hpe
    · have hq0 := Nat.eq_zero_of_not_pos hpos
      rw [shorter_zero_fullMass_fiber_eq_empty G hfree hd heven hmin
        hcard u hu huRange c e hq0 0]
      simp
  · rw [longer_fullMass_fiber_eq_empty G hfree hd heven hmin hcard
      u hu huRange c e hgt 0]
    simp

end

end Erdos85
