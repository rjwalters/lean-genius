import Proofs.Erdos85ThreeLevelEigenSupportC4Bound
import Proofs.Erdos85NegativeSizeTwoThreeLevelAction

/-! # Exact first reduction for the size-two `mu = -1` branch -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

abbrev MuNegOnePositiveShore
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent)
    (s : V → ℤ) := {x : V // x ∈ c.supp ∧ s x = 1}

abbrev MuNegOneNegativeShore
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent)
    (s : V → ℤ) := {x : V // x ∈ c.supp ∧ s x = -1}

abbrev MuNegOnePositiveExteriorFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → ℤ) :=
  {z : V // (G.adjMatrix ℤ).mulVec s z + 2 * s z = 2}

abbrev MuNegOneNegativeExteriorFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → ℤ) :=
  {z : V // (G.adjMatrix ℤ).mulVec s z + 2 * s z = -2}

/-- A two-neighbor signed component forces every outside extreme owner to
have the corresponding `2+0` or `0+2` component-neighbor profile. -/
theorem sizeTwo_extreme_owner_neighborProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hcard : ∀ z,
      (componentNeighborFinset G D c z).card = 2)
    (z : V) (hzout : z ∉ c.supp)
    (hw : (G.adjMatrix ℤ).mulVec s z + 2 * s z = 2 ∨
      (G.adjMatrix ℤ).mulVec s z + 2 * s z = -2) :
    let Xp := MuNegOnePositiveShore D c s
    let Xm := MuNegOneNegativeShore D c s
    (((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z).card,
      ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z).card) =
      if (G.adjMatrix ℤ).mulVec s z + 2 * s z = 2 then (2, 0) else (0, 2) := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let w : V → ℤ := fun x => A.mulVec s x + 2 * s x
  let Xp := MuNegOnePositiveShore D c s
  let Xm := MuNegOneNegativeShore D c s
  let C := (G.neighborFinset z).filter fun x => D.connectedComponentMk x = c
  let Cp := C.filter fun x => s x = 1
  let Cm := C.filter fun x => s x = -1
  have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  have hCcard : C.card = 2 := hcard z
  have hcover : C = Cp ∪ Cm := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Cp, Cm]
    constructor
    · intro hx
      have hxc : x ∈ c.supp := (hmem x).mpr (Finset.mem_filter.mp hx).2
      rcases hs_in x hxc with hm | hp
      · exact Or.inr ⟨hx, hm⟩
      · exact Or.inl ⟨hx, hp⟩
    · rintro (hx | hx) <;> exact hx.1
  have hdisj : Disjoint Cp Cm := by
    rw [Finset.disjoint_left]
    intro x hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hcards : Cp.card + Cm.card = 2 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hcover, hCcard]
  have hsumFull : ∑ x ∈ G.neighborFinset z, s x = w z := by
    rw [← SimpleGraph.adjMatrix_mulVec_apply]
    have hsz : s z = 0 := hs_out z hzout
    simp [w, A, hsz]
  have hsumC : ∑ x ∈ C, s x = w z := by
    rw [← hsumFull]
    symm
    rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset z)
      (fun x => D.connectedComponentMk x = c)]
    have houtzero : ∑ x ∈ (G.neighborFinset z).filter
        (fun x => ¬ D.connectedComponentMk x = c), s x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply hs_out x
      intro hxc
      exact (Finset.mem_filter.mp hx).2 ((hmem x).mp hxc)
    rw [houtzero, add_zero]
  have hsumSplit : (Cp.card : ℤ) - Cm.card = w z := by
    rw [hcover, Finset.sum_union hdisj] at hsumC
    have hp : ∑ x ∈ Cp, s x = (Cp.card : ℤ) := by
      calc
        _ = ∑ _x ∈ Cp, (1 : ℤ) := Finset.sum_congr rfl
          (fun x hx => (Finset.mem_filter.mp hx).2)
        _ = _ := by simp
    have hm : ∑ x ∈ Cm, s x = -(Cm.card : ℤ) := by
      calc
        _ = ∑ _x ∈ Cm, (-1 : ℤ) := Finset.sum_congr rfl
          (fun x hx => (Finset.mem_filter.mp hx).2)
        _ = _ := by simp
    rw [hp, hm] at hsumC
    exact hsumC
  have hXp : Finset.image Subtype.val
      ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z) = Cp := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Cp, C]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(G.mem_neighborFinset _ _).mpr hy.symm,
        (hmem y.1).mp y.2.1⟩, y.2.2⟩
    · rintro ⟨⟨hxz, hxc⟩, hsx⟩
      exact ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
        ((G.mem_neighborFinset _ _).mp hxz).symm, rfl⟩
  have hXm : Finset.image Subtype.val
      ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z) = Cm := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Cm, C]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(G.mem_neighborFinset _ _).mpr hy.symm,
        (hmem y.1).mp y.2.1⟩, y.2.2⟩
    · rintro ⟨⟨hxz, hxc⟩, hsx⟩
      exact ⟨⟨x, (hmem x).mpr hxc, hsx⟩,
        ((G.mem_neighborFinset _ _).mp hxz).symm, rfl⟩
  have hpCard : ((Finset.univ : Finset Xp).filter
      fun x => G.Adj x.1 z).card = Cp.card := by
    rw [← hXp, Finset.card_image_of_injective _ Subtype.val_injective]
  have hmCard : ((Finset.univ : Finset Xm).filter
      fun x => G.Adj x.1 z).card = Cm.card := by
    rw [← hXm, Finset.card_image_of_injective _ Subtype.val_injective]
  split_ifs with hpos
  · rw [hpCard, hmCard]
    have hpos' : w z = 2 := by simpa [w, A] using hpos
    apply Prod.ext <;> omega
  · rw [hpCard, hmCard]
    rcases hw with hw | hw
    · exact (hpos hw).elim
    · have hw' : w z = -2 := by simpa [w, A] using hw
      apply Prod.ext <;> omega

/-- The handshake identity and the C4 square bound leave exactly seven
possible cross/induced-edge census triples at extreme-fibre size eight. -/
theorem muNegOne_extreme_census_cases
    (cross ep em : Nat) (heven : Even cross) (hle : cross ≤ 12)
    (heq : ep = em) (hhand : 2 * ep = cross + 16) :
    (cross = 0 ∧ ep = 8 ∧ em = 8) ∨
    (cross = 2 ∧ ep = 9 ∧ em = 9) ∨
    (cross = 4 ∧ ep = 10 ∧ em = 10) ∨
    (cross = 6 ∧ ep = 11 ∧ em = 11) ∨
    (cross = 8 ∧ ep = 12 ∧ em = 12) ∨
    (cross = 10 ∧ ep = 13 ∧ em = 13) ∨
    (cross = 12 ∧ ep = 14 ∧ em = 14) := by
  obtain ⟨k, rfl⟩ := heven
  omega

/-- A C4-free graph on eight vertices with minimum degree at least two has
an actual degree-two vertex. -/
theorem exists_degree_eq_two_of_card_eight_of_c4Free
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W = 8) (hfree : ¬ containsC4 W H)
    (hmin : ∀ x, 2 ≤ H.degree x) : ∃ x, H.degree x = 2 := by
  by_contra hnone
  push Not at hnone
  have hthree : ∀ x, 3 ≤ H.degree x := by
    intro x
    have := hmin x
    have := hnone x
    omega
  let e : W ≃ Fin 8 := Fintype.equivOfCardEq hcard
  let R : SimpleGraph (Fin 8) := SimpleGraph.comap e.symm H
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  have hRdegree : ∀ i, R.degree i = H.degree (e.symm i) := by
    intro i
    exact (SimpleGraph.Iso.comap e.symm H).degree_eq i |>.symm
  have hRmin : 3 ≤ R.minDegree := by
    apply R.le_minDegree_of_forall_le_degree
    intro i
    rw [hRdegree]
    exact hthree _
  have hRfour := containsC4_of_eight_min_degree_three R hRmin
  exact hfree ((containsC4_iff_of_iso
    (SimpleGraph.Iso.comap e.symm H)).mp hRfour)

theorem degree_induce_finset_eq_internalNeighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (x : (↑S : Set V)) :
    (G.induce (↑S : Set V)).degree x =
      ((G.neighborFinset x.1).filter fun y => y ∈ S).card := by
  rw [← (G.induce (↑S : Set V)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hadj :=
      ((G.induce (↑S : Set V)).mem_neighborFinset x y).mp hy
    change G.Adj x.1 y.1 at hadj
    apply Finset.mem_filter.mpr
    exact ⟨(G.mem_neighborFinset x.1 y.1).mpr hadj,
      Finset.mem_coe.mp y.2⟩
  · intro y₁ _ y₂ _ hy
    exact Subtype.ext hy
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨⟨y, Finset.mem_coe.mpr hy'.2⟩, ?_, rfl⟩
    exact ((G.induce (↑S : Set V)).mem_neighborFinset x _).mpr
      ((G.mem_neighborFinset x.1 y).mp hy'.1)

/-- In the `mu = -1` joint-line branch the two extreme fibres both have
eight vertices and minimum internal degree two.  Their induced edge counts
agree, and their entire remaining census is one of seven explicit cases. -/
theorem orderSixtyFour_sizeTwo_muNegOne_extreme_structure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-1 : ℤ) * s z) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    let cross := ∑ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card
    let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
    let em := (G.induce (↑Sm : Set V)).edgeFinset.card
    Sp.card = 8 ∧ Sm.card = 8 ∧
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card) ∧
    ((cross = 0 ∧ ep = 8 ∧ em = 8) ∨
      (cross = 2 ∧ ep = 9 ∧ em = 9) ∨
      (cross = 4 ∧ ep = 10 ∧ em = 10) ∨
      (cross = 6 ∧ ep = 11 ∧ em = 11) ∨
      (cross = 8 ∧ ep = 12 ∧ em = 12) ∨
      (cross = 10 ∧ ep = 13 ∧ em = 13) ∨
      (cross = 12 ∧ ep = 14 ∧ em = 14)) := by
  dsimp only
  let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
  let cross := ∑ u ∈ Sp,
    ((G.neighborFinset u).filter fun y => y ∈ Sm).card
  let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
  let em := (G.induce (↑Sm : Set V)).edgeFinset.card
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - (-1 : ℤ)) ∧
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card)
      at hprofile
  have hSp : Sp.card = 8 := by omega
  have hSm : Sm.card = 8 := by omega
  have hdeg := orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2) at hdeg
  have hcensus := extreme_support_edgeCensus_of_degreeBalance
    G Sp Sm hprofile.1 hdeg.1 hdeg.2
  change Even cross ∧ ep = em ∧
    2 * ep = cross + 2 * Sp.card ∧
    2 * em = cross + 2 * Sm.card at hcensus
  have hbound :=
    orderSixtyFour_sizeTwo_muNegOne_extreme_cross_le_twelve_edges_le_fourteen
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  change cross ≤ 12 ∧ ep ≤ 14 at hbound
  refine ⟨hSp, hSm, hprofile.2.2.1, hprofile.2.2.2, ?_⟩
  exact muNegOne_extreme_census_cases cross ep em hcensus.1 hbound.1
    hcensus.2.1 (by simpa [hSp] using hcensus.2.2.1)

/-- The `mu = -1` extreme owner fibres each have eight vertices, all outside
the distinguished component, and have exact same-sign neighbor profiles. -/
theorem orderSixtyFour_sizeTwo_muNegOne_extremeOwner_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-1 : ℤ) * s z) :
    Fintype.card (MuNegOnePositiveExteriorFiber G s) = 8 ∧
    Fintype.card (MuNegOneNegativeExteriorFiber G s) = 8 ∧
    (∀ z : MuNegOnePositiveExteriorFiber G s,
      z.1 ∉ c.supp ∧
      ((Finset.univ : Finset
        (MuNegOnePositiveShore (secondOrderDefectGraph G) c s)).filter
          fun x => G.Adj x.1 z.1).card = 2 ∧
      ((Finset.univ : Finset
        (MuNegOneNegativeShore (secondOrderDefectGraph G) c s)).filter
          fun x => G.Adj x.1 z.1).card = 0) ∧
    ∀ z : MuNegOneNegativeExteriorFiber G s,
      z.1 ∉ c.supp ∧
      ((Finset.univ : Finset
        (MuNegOnePositiveShore (secondOrderDefectGraph G) c s)).filter
          fun x => G.Adj x.1 z.1).card = 0 ∧
      ((Finset.univ : Finset
        (MuNegOneNegativeShore (secondOrderDefectGraph G) c s)).filter
          fun x => G.Adj x.1 z.1).card = 2 := by
  classical
  let w : V → ℤ := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := (Finset.univ : Finset V).filter fun x => w x = 2
  let Sm := (Finset.univ : Finset V).filter fun x => w x = -2
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - (-1 : ℤ)) ∧ _ at hprofile
  have hSp : Sp.card = 8 := by omega
  have hSm : Sm.card = 8 := by omega
  have hthree := orderSixtyFour_sizeTwo_signedJoint_threeLevelAction_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  have hSpOut : ∀ x ∈ Sp, x ∉ c.supp := by
    intro x hx hxc
    have hw0 := hthree.1 x hxc
    have hw2 : w x = 2 := (Finset.mem_filter.mp hx).2
    change w x = 0 at hw0
    omega
  have hSmOut : ∀ x ∈ Sm, x ∉ c.supp := by
    intro x hx hxc
    have hw0 := hthree.1 x hxc
    have hwm2 : w x = -2 := (Finset.mem_filter.mp hx).2
    change w x = 0 at hw0
    omega
  have hpCard : Fintype.card (MuNegOnePositiveExteriorFiber G s) = 8 := by
    rw [Fintype.card_subtype]
    change Sp.card = 8
    exact hSp
  have hmCard : Fintype.card (MuNegOneNegativeExteriorFiber G s) = 8 := by
    rw [Fintype.card_subtype]
    change Sm.card = 8
    exact hSm
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  refine ⟨hpCard, hmCard, ?_, ?_⟩
  · intro z
    have hzmem : z.1 ∈ Sp :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩
    have hzout := hSpOut z.1 hzmem
    have hn := sizeTwo_extreme_owner_neighborProfile G
      (secondOrderDefectGraph G) c s hs_out hs_in P.componentNeighborCard
        z.1 hzout (Or.inl z.2)
    rw [if_pos z.2] at hn
    exact ⟨hzout, congrArg Prod.fst hn, congrArg Prod.snd hn⟩
  · intro z
    have hzmem : z.1 ∈ Sm :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩
    have hzout := hSmOut z.1 hzmem
    have hn := sizeTwo_extreme_owner_neighborProfile G
      (secondOrderDefectGraph G) c s hs_out hs_in P.componentNeighborCard
        z.1 hzout (Or.inr z.2)
    have hne : (G.adjMatrix ℤ).mulVec s z.1 + 2 * s z.1 ≠ 2 := by
      omega
    rw [if_neg hne] at hn
    exact ⟨hzout, congrArg Prod.fst hn, congrArg Prod.snd hn⟩

/-- Each `mu = -1` extreme shore contains a degree-two vertex with no edge
to the opposite extreme shore. -/
theorem orderSixtyFour_sizeTwo_muNegOne_exists_cross_isolated_extremes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-1 : ℤ) * s z) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    (∃ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card = 2 ∧
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card = 0) ∧
    ∃ v ∈ Sm,
      ((G.neighborFinset v).filter fun y => y ∈ Sm).card = 2 ∧
      ((G.neighborFinset v).filter fun y => y ∈ Sp).card = 0 := by
  dsimp only
  let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - (-1 : ℤ)) ∧
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card)
      at hprofile
  have hSp : Sp.card = 8 := by omega
  have hSm : Sm.card = 8 := by omega
  have hdeg := orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  change (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2) at hdeg
  let Hp := G.induce (↑Sp : Set V)
  let Hm := G.induce (↑Sm : Set V)
  have hpcard : Fintype.card (↑Sp : Set V) = 8 := by simp [hSp]
  have hmcard : Fintype.card (↑Sm : Set V) = 8 := by simp [hSm]
  have hpmin : ∀ x : (↑Sp : Set V), 2 ≤ Hp.degree x := by
    intro x
    rw [show Hp.degree x =
      ((G.neighborFinset x.1).filter fun y => y ∈ Sp).card by
        exact degree_induce_finset_eq_internalNeighbor_card G Sp x]
    exact hprofile.2.2.1 x.1 x.2
  have hmmin : ∀ x : (↑Sm : Set V), 2 ≤ Hm.degree x := by
    intro x
    rw [show Hm.degree x =
      ((G.neighborFinset x.1).filter fun y => y ∈ Sm).card by
        exact degree_induce_finset_eq_internalNeighbor_card G Sm x]
    exact hprofile.2.2.2 x.1 x.2
  obtain ⟨u, hu2⟩ := exists_degree_eq_two_of_card_eight_of_c4Free
    Hp hpcard (not_containsC4_induce_finset G hfree Sp) hpmin
  obtain ⟨v, hv2⟩ := exists_degree_eq_two_of_card_eight_of_c4Free
    Hm hmcard (not_containsC4_induce_finset G hfree Sm) hmmin
  have huInternal :
      ((G.neighborFinset u.1).filter fun y => y ∈ Sp).card = 2 := by
    rw [← degree_induce_finset_eq_internalNeighbor_card G Sp u]
    exact hu2
  have hvInternal :
      ((G.neighborFinset v.1).filter fun y => y ∈ Sm).card = 2 := by
    rw [← degree_induce_finset_eq_internalNeighbor_card G Sm v]
    exact hv2
  refine ⟨⟨u.1, u.2, huInternal, ?_⟩,
    ⟨v.1, v.2, hvInternal, ?_⟩⟩
  · have hz :
        ((G.neighborFinset u.1).filter fun y => y ∈ Sm).card + 2 = 2 :=
      (hdeg.1 u.1 u.2).symm.trans huInternal
    have hz0 : ((G.neighborFinset u.1).filter fun y => y ∈ Sm).card = 0 := by
      omega
    simpa [Sm, w] using hz0
  · have hz :
        ((G.neighborFinset v.1).filter fun y => y ∈ Sp).card + 2 = 2 :=
      (hdeg.2 v.1 v.2).symm.trans hvInternal
    have hz0 : ((G.neighborFinset v.1).filter fun y => y ∈ Sp).card = 0 := by
      omega
    simpa [Sp, w] using hz0

end

end Erdos85

#print axioms Erdos85.muNegOne_extreme_census_cases
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_extreme_structure
#print axioms Erdos85.sizeTwo_extreme_owner_neighborProfile
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_extremeOwner_profile
#print axioms Erdos85.exists_degree_eq_two_of_card_eight_of_c4Free
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_exists_cross_isolated_extremes
