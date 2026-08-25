import Proofs.Erdos85PureEndpointStrictBoundaryGridCard

/-!
# Canonical unused off-shore points at the strict boundary

The equality grid uses all but exactly `m` points of the off-shore class `U`.
Every row through one of these unused points has private occupancy one.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
theorem c4Free_binarySquare_pureEndpoint_privateCut_boundary_unusedU
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v, (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun p =>
        (G.neighborFinset p ∩ fullLineCenters G S q).card = 1) = 2 * q - 4) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
    let U := Sᶜ
    let B := Fᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    let H := B.filter fun b => 1 < r b
    let Q := (U ∪ X).filter fun y =>
      0 < (Z.filter fun z => G.Adj z y).card ∧
      0 < (H.filter fun b => G.Adj b y).card
    let U₀ := U \ Q
    let O := B.filter fun b => r b = 1
    U₀.card = m ∧ ∀ u ∈ U₀, G.neighborFinset u ⊆ O := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
  let U := Sᶜ
  let B := Fᶜ
  let r : V → ℕ := fun b => (G.neighborFinset b ∩ P).card
  let Z := B.filter fun b => r b = 0
  let H := B.filter fun b => 1 < r b
  let weight : V → ℕ := fun b => r b - 1
  let Q := (U ∪ X).filter fun y =>
    0 < (Z.filter fun z => G.Adj z y).card ∧
    0 < (H.filter fun b => G.Adj b y).card
  let U₀ := U \ Q
  let O := B.filter fun b => r b = 1
  have hs :=
    (c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_rowProfile_and_saturation
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri).2 hcut
  have hZcard : Z.card = q - 2 := hs.1
  have hrowTwo : ∀ b ∈ H, r b = 2 := hs.2.2.1
  have hUdeg : ∀ u ∈ U, (Z.filter fun z => G.Adj z u).card ≤ 1 :=
    hs.2.2.2.1
  have hUbalance : ∀ u ∈ U,
      (Z.filter fun z => G.Adj z u).card =
        ∑ b ∈ H.filter (fun b => G.Adj b u), weight b :=
    hs.2.2.2.2.1
  have hweightCard : ∀ y,
      (∑ b ∈ H.filter (fun b => G.Adj b y), weight b) =
        (H.filter fun b => G.Adj b y).card := by
    intro y
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro b hb
    have hbH := (Finset.mem_filter.mp hb).1
    simp [weight, hrowTwo b hbH]
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hPcard : P.card = q := by simpa [P, F] using hprofile.2.1
  have hXdouble : 2 * X.card = q * (q - 1) := by
    simpa [X, F] using hprofile.2.2.1
  have hSX : S = P ∪ X := by
    ext x
    simp only [P, X, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases (hprofile.1 x).mp hx with h1 | h2
      · exact Or.inl ⟨hx, by simpa [F] using h1⟩
      · exact Or.inr ⟨hx, by simpa [F] using h2⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hPX : Disjoint P X := by
    rw [Finset.disjoint_left]
    intro x hxP hxX
    have h1 := (Finset.mem_filter.mp hxP).2
    have h2 := (Finset.mem_filter.mp hxX).2
    omega
  have hScard : S.card = P.card + X.card := by
    rw [hSX, Finset.card_union_of_disjoint hPX]
  have hXcard : X.card = m * (q - 1) := by
    rw [hqm] at hXdouble ⊢
    ring_nf at hXdouble ⊢
    omega
  have hUcard : U.card = m * (q - 1) := by
    have hUc : U.card = Fintype.card V - S.card := by
      simpa [U] using (Finset.card_compl S)
    have hqpos : 1 ≤ q := by omega
    have hqsplit : q * q = q + q * (q - 1) := by
      have hqe : q = (q - 1) + 1 := (Nat.sub_add_cancel hqpos).symm
      nth_rewrite 1 [hqe]
      ring
    rw [hcard, hScard, hPcard, hXcard, hqsplit] at hUc
    rw [hqm] at hUc ⊢
    ring_nf at hUc ⊢
    omega
  have hrowU : ∀ z ∈ Z, (U.filter fun u => G.Adj z u).card = m := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have hzNotF : z ∉ F := by simpa [B] using hzB
    have hzHalf :=
      (c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri z hzNotF).1
    have hsplit := neighbor_inter_complement_card G S z
    have hUeq : U.filter (fun u => G.Adj z u) = G.neighborFinset z ∩ Sᶜ := by
      ext u
      simp [U, SimpleGraph.mem_neighborFinset, and_comm]
    rw [hUeq]
    calc
      (G.neighborFinset z ∩ Sᶜ).card = q - m := by
        simpa only [Finset.compl_eq_univ_sdiff, hreg z, hzHalf] using hsplit
      _ = m := by omega
  let QU := U.filter fun u =>
    0 < (Z.filter fun z => G.Adj z u).card ∧
    0 < (H.filter fun b => G.Adj b u).card
  have hQUpos : QU = U.filter fun u =>
      0 < (Z.filter fun z => G.Adj z u).card := by
    ext u
    simp only [QU, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · intro h
      refine ⟨h.1, h.2, ?_⟩
      have hb : 0 < ∑ b ∈ H.filter (fun b => G.Adj b u), weight b := by
        rw [← hUbalance u h.1]
        exact h.2
      rwa [hweightCard] at hb
  have hQUcard : QU.card = m * Z.card := by
    rw [hQUpos, Finset.card_eq_sum_ones, Finset.sum_filter]
    calc
      (∑ u ∈ U,
          if 0 < (Z.filter fun z => G.Adj z u).card then 1 else 0) =
          ∑ u ∈ U, (Z.filter fun z => G.Adj z u).card := by
        apply Finset.sum_congr rfl
        intro u hu
        have hd := hUdeg u hu
        by_cases hp : 0 < (Z.filter fun z => G.Adj z u).card
        · simp [hp]
          omega
        · have hz : (Z.filter fun z => G.Adj z u).card = 0 := by omega
          simp [hz]
      _ = ∑ z ∈ Z, (U.filter fun u => G.Adj z u).card := by
        simp only [Finset.card_eq_sum_ones]
        simp_rw [Finset.sum_filter]
        exact Finset.sum_comm
      _ = ∑ _z ∈ Z, m := Finset.sum_congr rfl hrowU
      _ = m * Z.card := by simp [Nat.mul_comm]
  have hUinterQ : U ∩ Q = QU := by
    ext u
    simp [Q, QU]
    intro hu _ _
    exact Or.inl hu
  have hUzeroCard : U₀.card = m := by
    have hsub := Finset.card_sdiff_add_card_inter U Q
    change U₀.card + (U ∩ Q).card = U.card at hsub
    rw [hUinterQ, hQUcard, hZcard, hUcard] at hsub
    have hqdec : q - 1 = (q - 2) + 1 := by omega
    rw [hqdec] at hsub
    rw [Nat.mul_add] at hsub
    omega
  refine ⟨hUzeroCard, ?_⟩
  intro u hu b hbu
  have huU : u ∈ U := (Finset.mem_sdiff.mp hu).1
  have huNotQ : u ∉ Q := (Finset.mem_sdiff.mp hu).2
  have hbB : b ∈ B := by
    apply Finset.mem_compl.mpr
    intro hbF
    have hbFull : (G.neighborFinset b ∩ S).card = q := by
      simpa [F] using (Finset.mem_filter.mp hbF).2
    have huS : u ∈ S := by
      have hle : (G.neighborFinset b).card ≤ (G.neighborFinset b ∩ S).card := by
        rw [hbFull, G.card_neighborFinset_eq_degree, hreg b]
      have heq : G.neighborFinset b ∩ S = G.neighborFinset b :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
      have hub : u ∈ G.neighborFinset b :=
        (G.mem_neighborFinset b u).mpr ((G.mem_neighborFinset u b).mp hbu).symm
      exact (Finset.mem_inter.mp (heq.symm ▸ hub)).2
    exact (Finset.mem_compl.mp huU huS).elim
  apply Finset.mem_filter.mpr
  refine ⟨hbB, ?_⟩
  by_cases hr0 : r b = 0
  · have hbZ : b ∈ Z := Finset.mem_filter.mpr ⟨hbB, hr0⟩
    have hzpos : 0 < (Z.filter fun z => G.Adj z u).card := by
      apply Finset.card_pos.mpr
      exact ⟨b, Finset.mem_filter.mpr
        ⟨hbZ, ((G.mem_neighborFinset u b).mp hbu).symm⟩⟩
    have hhpos : 0 < (H.filter fun h => G.Adj h u).card := by
      have : 0 < ∑ h ∈ H.filter (fun h => G.Adj h u), weight h := by
        rw [← hUbalance u huU]
        exact hzpos
      rwa [hweightCard] at this
    exact (huNotQ (Finset.mem_filter.mpr
      ⟨Finset.mem_union_left X huU, hzpos, hhpos⟩)).elim
  · by_cases hrH : 1 < r b
    · have hbH : b ∈ H := Finset.mem_filter.mpr ⟨hbB, hrH⟩
      have hhpos : 0 < (H.filter fun h => G.Adj h u).card := by
        apply Finset.card_pos.mpr
        exact ⟨b, Finset.mem_filter.mpr
          ⟨hbH, ((G.mem_neighborFinset u b).mp hbu).symm⟩⟩
      have hzpos : 0 < (Z.filter fun z => G.Adj z u).card := by
        rw [hUbalance u huU, hweightCard]
        exact hhpos
      exact (huNotQ (Finset.mem_filter.mpr
        ⟨Finset.mem_union_left X huU, hzpos, hhpos⟩)).elim
    · change r b = 1
      omega

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_boundary_unusedU
