import Proofs.Erdos85PureEndpointStrictCutArithmetic
import Proofs.Erdos85LinearTradeCombinedShoreCollision
import Proofs.Erdos85PureEndpointPairPointTrade
import Proofs.Erdos85PureEndpointPrivateOccupancyMoments
import Proofs.Erdos85DefectCutLaplacianSupport
import Proofs.Erdos85PureEndpointStrictBoundarySaturation
import Proofs.Erdos85LinearTradeStrictBoundaryRowCapacity

/-!
# A uniform strict-cut gap at the pure endpoint

The combined complementary-shore/pair-point collision bound gives a
quadratic constraint on the number of zero-private rows.  Together with the
elementary energy bounds it excludes the whole interval below `2q - 4`.
-/

namespace Erdos85

open Finset BigOperators SimpleGraph

noncomputable section

/-- If the average of a natural-valued function on a finite set is at most
one, its total excess above one is bounded by its number of zero entries. -/
theorem sum_sub_one_positive_le_card_zeros_of_sum_le_card
    {α : Type*} [DecidableEq α] (s : Finset α) (r : α → ℕ)
    (hsum : ∑ x ∈ s, r x ≤ s.card) :
    ∑ x ∈ s.filter (fun x => 1 < r x), (r x - 1) ≤
      (s.filter fun x => r x = 0).card := by
  classical
  have hbalance :
      (s.filter fun x => r x = 0).card + (∑ x ∈ s, r x) =
        s.card + ∑ x ∈ s, (r x - 1) := by
    calc
      (s.filter fun x => r x = 0).card + (∑ x ∈ s, r x) =
          (∑ x ∈ s, if r x = 0 then 1 else 0) + ∑ x ∈ s, r x := by
            rw [Finset.card_filter]
      _ = ∑ x ∈ s, ((if r x = 0 then 1 else 0) + r x) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ s, (1 + (r x - 1)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            cases hr : r x with
            | zero => simp
            | succ n => simp [Nat.add_comm]
      _ = s.card + ∑ x ∈ s, (r x - 1) := by
            rw [Finset.sum_add_distrib]
            simp
  have hfilter : ∑ x ∈ s.filter (fun x => 1 < r x), (r x - 1) =
      ∑ x ∈ s, (r x - 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hx : 1 < r x
    · simp [hx]
    · have : r x ≤ 1 := by omega
      simp [hx, Nat.sub_eq_zero_of_le this]
  rw [hfilter]
  omega

/-- Exact version with a nonnegative deficit term. -/
theorem sum_sub_one_positive_add_defect_eq_card_zeros
    {α : Type*} [DecidableEq α] (s : Finset α) (r : α → ℕ)
    (defect : ℕ)
    (hsum : (∑ x ∈ s, r x) + defect = s.card) :
    (∑ x ∈ s.filter (fun x => 1 < r x), (r x - 1)) + defect =
      (s.filter fun x => r x = 0).card := by
  classical
  have hbalance :
      (s.filter fun x => r x = 0).card + (∑ x ∈ s, r x) =
        s.card + ∑ x ∈ s, (r x - 1) := by
    calc
      (s.filter fun x => r x = 0).card + (∑ x ∈ s, r x) =
          (∑ x ∈ s, if r x = 0 then 1 else 0) + ∑ x ∈ s, r x := by
            rw [Finset.card_filter]
      _ = ∑ x ∈ s, ((if r x = 0 then 1 else 0) + r x) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ s, (1 + (r x - 1)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            cases hr : r x with
            | zero => simp
            | succ n => simp [Nat.add_comm]
      _ = s.card + ∑ x ∈ s, (r x - 1) := by
            rw [Finset.sum_add_distrib]
            simp
  have hfilter : ∑ x ∈ s.filter (fun x => 1 < r x), (r x - 1) =
      ∑ x ∈ s, (r x - 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hx : 1 < r x
    · simp [hx]
    · have : r x ≤ 1 := by omega
      simp [hx, Nat.sub_eq_zero_of_le this]
  rw [hfilter]
  omega

/-- Collision plus the exact pair-shore moment gives the strict-cut gap. -/
theorem two_mul_sub_four_le_of_combinedShore_collision
    {q m z s load : ℕ} (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hz : m ≤ z) (henergy : 2 * z ≤ s)
    (hcollision : m * z + load ≤ z ^ 2)
    (hmoment : load + s = m * z) :
    2 * q - 4 ≤ s := by
  apply two_mul_sub_four_le_of_strictCut_quadratic hq hqm hz henergy
  rw [hqm]
  nlinarith

set_option maxHeartbeats 800000 in
/-- At every preconnected pure endpoint, the canonical private-set defect
cut is at least `2q - 4`; equality pins exactly `q - 2` zero-private rows. -/
theorem c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_rowProfile_and_saturation
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
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
    let U := Sᶜ
    let B := Fᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    let H := B.filter fun b => 1 < r b
    let weight := fun b => r b - 1
    let cut := finsetGraphCutSize (secondOrderDefectGraph G) P
    2 * q - 4 ≤ cut ∧
      (cut = 2 * q - 4 → Z.card = q - 2 ∧ H.card = q - 2 ∧
        (∀ b ∈ H, r b = 2) ∧
        (∀ u ∈ U, (Z.filter fun z => G.Adj z u).card ≤ 1) ∧
        (∀ x ∈ X, 0 < (∑ b ∈ H.filter (fun b => G.Adj b x), weight b) →
          (Z.filter fun z => G.Adj z x).card = 1 ∧
            (∑ b ∈ H.filter (fun b => G.Adj b x), weight b) = 1) ∧
        ∀ z ∈ Z, ∀ b ∈ H, 0 < weight b →
          (U.filter fun u => G.Adj z u ∧ G.Adj b u).card +
            (X.filter fun x => G.Adj z x ∧ G.Adj b x).card = 1) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let B := Fᶜ
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
  let U := Sᶜ
  let r : V → ℕ := fun b => (G.neighborFinset b ∩ P).card
  let Z := B.filter fun b => r b = 0
  let H := B.filter fun b => 1 < r b
  let weight : V → ℕ := fun b => r b - 1
  let D := secondOrderDefectGraph G
  let cut := finsetGraphCutSize D P
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hPcard : P.card = q := by simpa [P, F] using hprofile.2.1
  have hBcard : B.card = q * (q - 1) := by
    change Fᶜ.card = _
    rw [Finset.card_compl, show F.card = q by simpa [F] using hCcard,
      hcard, Nat.mul_sub_left_distrib]
    simp
  have hrowU : ∀ b ∈ B, (U.filter fun u => G.Adj b u).card = m := by
    intro b hb
    have hbNotF : b ∉ F := by simpa [B] using hb
    have hbHalf :=
      (c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri b hbNotF).1
    have hsplit := neighbor_inter_complement_card G S b
    have hUeq : U.filter (fun u => G.Adj b u) = G.neighborFinset b ∩ Sᶜ := by
      ext u
      simp [U, SimpleGraph.mem_neighborFinset, and_comm]
    rw [hUeq]
    calc
      (G.neighborFinset b ∩ Sᶜ).card = q - m := by
        simpa only [Finset.compl_eq_univ_sdiff, hreg b, hbHalf] using hsplit
      _ = m := by omega
  have hPdeg : ∀ p ∈ P, (G.neighborFinset p ∩ B).card = q - 1 := by
    intro p hp
    have hpOne : (G.neighborFinset p ∩ F).card = 1 :=
      (Finset.mem_filter.mp hp).2
    have hsplit := neighbor_inter_complement_card G F p
    change (G.neighborFinset p ∩ Fᶜ).card = q - 1
    simpa only [Finset.compl_eq_univ_sdiff, hreg p, hpOne] using hsplit
  have hsumB : ∑ b ∈ B, r b = B.card := by
    have hdouble := sum_neighbor_inter_card_comm G B P
    change (∑ b ∈ B, r b) = _ at hdouble
    calc
      (∑ b ∈ B, r b) =
          ∑ p ∈ P, (G.neighborFinset p ∩ B).card := hdouble
      _ = P.card * (q - 1) := Finset.sum_const_nat hPdeg
      _ = B.card := by rw [hPcard, hBcard]
  have hweightAll : ∑ b ∈ B, weight b = Z.card := by
    symm
    simpa [Z, weight] using
      card_zeros_eq_sum_sub_one_of_sum_eq_finset_card B r hsumB
  have hweight : ∑ b ∈ H, weight b = Z.card := by
    rw [← hweightAll]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hbr : 1 < r b
    · simp [hbr]
    · have hrle : r b ≤ 1 := by omega
      simp [hbr, weight, Nat.sub_eq_zero_of_le hrle]
  have hPUzero : ∀ p ∈ P, ∀ u ∈ U, ¬ D.Adj p u := by
    intro p hp u hu hpu
    have hcutProfile :=
      (c4Free_binarySquare_pureEndpoint_defectCut_biregular
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.2.2.2
    have hpS := (Finset.mem_filter.mp hp).1
    have hpZero := (hcutProfile p hpS).2 (Finset.mem_filter.mp hp).2
    have hmem : u ∈ D.neighborFinset p ∩ Sᶜ :=
      Finset.mem_inter.mpr
        ⟨(D.mem_neighborFinset p u).mpr hpu, by simpa [U] using hu⟩
    rw [Finset.card_eq_zero.mp hpZero] at hmem
    simp at hmem
  have hlocalSumU : ∀ u ∈ U,
      ∑ b ∈ G.neighborFinset u, r b = (G.neighborFinset u).card := by
    intro u hu
    have hdouble := sum_neighbor_inter_card_comm G (G.neighborFinset u) P
    change (∑ b ∈ G.neighborFinset u, r b) = _ at hdouble
    calc
      (∑ b ∈ G.neighborFinset u, r b) =
          ∑ p ∈ P, (G.neighborFinset p ∩ G.neighborFinset u).card := hdouble
      _ = P.card := by
        calc
          _ = ∑ _p ∈ P, 1 := by
            apply Finset.sum_congr rfl
            intro p hp
            have hne : p ≠ u := by
              intro h
              subst u
              exact (Finset.mem_compl.mp hu) (Finset.mem_filter.mp hp).1
            have hnotD := hPUzero p hp u hu
            have hzeroIff := secondOrderDefectGraph_adj_iff_card_common_eq_zero
              G hfree hne
            have hneZero :
                (G.neighborFinset p ∩ G.neighborFinset u).card ≠ 0 := by
              intro hz
              exact hnotD (hzeroIff.mpr hz)
            have hle := card_inter_neighborFinset_le_one hfree hne
            omega
          _ = P.card := by simp
      _ = (G.neighborFinset u).card := by
        rw [hPcard, G.card_neighborFinset_eq_degree, hreg]
  have hneighborsB : ∀ u ∈ U, G.neighborFinset u ⊆ B := by
    intro u hu b hbu
    apply Finset.mem_compl.mpr
    intro hbF
    have hbFull : (G.neighborFinset b ∩ S).card = q :=
      (mem_fullLineCenters G S q b).mp (by simpa [F] using hbF)
    have hbSubset : G.neighborFinset b ⊆ S := by
      have heq : G.neighborFinset b ∩ S = G.neighborFinset b := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        rw [hbFull, G.card_neighborFinset_eq_degree, hreg]
      intro x hx
      have hx' : x ∈ G.neighborFinset b ∩ S := by rw [heq]; exact hx
      exact (Finset.mem_inter.mp hx').2
    exact (Finset.mem_compl.mp hu)
      (hbSubset ((G.mem_neighborFinset b u).mpr
        ((G.mem_neighborFinset u b).mp hbu).symm))
  have hUbalance : ∀ u ∈ U,
      (Z.filter fun z => G.Adj z u).card =
        ∑ b ∈ H.filter (fun b => G.Adj b u), weight b := by
    intro u hu
    have hzeroLocal := card_zeros_eq_sum_sub_one_of_sum_eq_finset_card
      (G.neighborFinset u) r (hlocalSumU u hu)
    have hNB : G.neighborFinset u = B.filter fun b => G.Adj b u := by
      ext b
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · intro hub
        exact ⟨hneighborsB u hu ((G.mem_neighborFinset u b).mpr hub), hub.symm⟩
      · exact fun hb => hb.2.symm
    rw [hNB] at hzeroLocal
    have hzeroFilter :
        (B.filter (fun b => G.Adj b u)).filter (fun b => r b = 0) =
          Z.filter fun z => G.Adj z u := by
      ext b
      simp [Z, and_assoc, and_left_comm, and_comm]
    rw [hzeroFilter] at hzeroLocal
    have hposFilter :
        ∑ b ∈ H.filter (fun b => G.Adj b u), weight b =
          ∑ b ∈ B.filter (fun b => G.Adj b u), (r b - 1) := by
      have hHadj : H.filter (fun b => G.Adj b u) =
          (B.filter fun b => G.Adj b u).filter (fun b => 1 < r b) := by
        ext b
        simp [H, and_assoc, and_left_comm, and_comm]
      rw [hHadj, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbr : 1 < r b
      · simp [hbr, weight]
      · have hrle : r b ≤ 1 := by omega
        simp [hbr, weight, Nat.sub_eq_zero_of_le hrle]
    rw [hposFilter]
    exact hzeroLocal
  have hSX : S = P ∪ X := by
    ext x
    simp only [P, X, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases (hprofile.1 x).mp hx with h1 | h2
      · exact Or.inl ⟨hx, by simpa [F] using h1⟩
      · exact Or.inr ⟨hx, by simpa [F] using h2⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hPXdisj : Disjoint P X := by
    rw [Finset.disjoint_left]
    intro x hxP hxX
    have h1 := (Finset.mem_filter.mp hxP).2
    have h2 := (Finset.mem_filter.mp hxX).2
    omega
  let defect : V → ℕ := fun x => (D.neighborFinset x ∩ P).card
  have hXlocal : ∀ x ∈ X,
      (∑ b ∈ H.filter (fun b => G.Adj b x), weight b) + defect x =
        (Z.filter fun z => G.Adj z x).card := by
    intro x hx
    have hi :=
      c4Free_binarySquare_pureEndpoint_pairPoint_privateOccupancy_add_defect
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri x hx
    change (∑ b ∈ G.neighborFinset x ∩ B, r b) + defect x =
      (G.neighborFinset x ∩ B).card at hi
    have hg := sum_sub_one_positive_add_defect_eq_card_zeros
      (G.neighborFinset x ∩ B) r (defect x) hi
    have hHfilter :
        (G.neighborFinset x ∩ B).filter (fun b => 1 < r b) =
          H.filter fun b => G.Adj b x := by
      ext b
      simp [H, SimpleGraph.mem_neighborFinset, G.adj_comm,
        and_assoc, and_left_comm, and_comm]
    have hZfilter :
        (G.neighborFinset x ∩ B).filter (fun b => r b = 0) =
          Z.filter fun b => G.Adj b x := by
      ext b
      simp [Z, SimpleGraph.mem_neighborFinset, G.adj_comm,
        and_assoc, and_left_comm, and_comm]
    simpa [hHfilter, hZfilter, weight] using hg
  have hZrowX : ∀ z ∈ Z, (X.filter fun x => G.Adj z x).card = m := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have hzNotF : z ∉ F := by simpa [B] using hzB
    have hmOcc :=
      (c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri z hzNotF).1
    have hzP : (G.neighborFinset z ∩ P).card = 0 := by
      simpa [r] using (Finset.mem_filter.mp hz).2
    have hsplit : (G.neighborFinset z ∩ S).card =
        (G.neighborFinset z ∩ P).card +
          (G.neighborFinset z ∩ X).card := by
      rw [hSX, Finset.inter_union_distrib_left,
        Finset.card_union_of_disjoint]
      exact hPXdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have hfilter : X.filter (fun x => G.Adj z x) =
        G.neighborFinset z ∩ X := by
      ext x
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hfilter]
    omega
  have hHrowX : ∀ b ∈ H, (X.filter fun x => G.Adj b x).card ≤ m - 2 := by
    intro b hb
    have hbB := (Finset.mem_filter.mp hb).1
    have hbPos := (Finset.mem_filter.mp hb).2
    have hbNotF : b ∉ F := by simpa [B] using hbB
    have hmOcc :=
      (c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri b hbNotF).1
    have hsplit : (G.neighborFinset b ∩ S).card =
        (G.neighborFinset b ∩ P).card +
          (G.neighborFinset b ∩ X).card := by
      rw [hSX, Finset.inter_union_distrib_left,
        Finset.card_union_of_disjoint]
      exact hPXdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have hfilter : X.filter (fun x => G.Adj b x) =
        G.neighborFinset b ∩ X := by
      ext x
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hfilter]
    change 1 < (G.neighborFinset b ∩ P).card at hbPos
    omega
  have hcompl : Finset.univ \ P = X ∪ U := by
    ext x
    by_cases hxS : x ∈ S
    · rcases (hprofile.1 x).mp hxS with h1 | h2
      · have hxP : x ∈ P := Finset.mem_filter.mpr ⟨hxS, by simpa [F] using h1⟩
        have hxNotX : x ∉ X := fun hxX =>
          Finset.disjoint_left.mp hPXdisj hxP hxX
        simp [U, hxP, hxNotX, hxS]
      · have hxX : x ∈ X := Finset.mem_filter.mpr ⟨hxS, by simpa [F] using h2⟩
        have hxNotP : x ∉ P := fun hxP =>
          Finset.disjoint_left.mp hPXdisj hxP hxX
        simp [U, hxNotP, hxX, hxS]
    · have hxNotP : x ∉ P := fun hxP =>
        hxS (Finset.mem_filter.mp hxP).1
      have hxNotX : x ∉ X := fun hxX =>
        hxS (Finset.mem_filter.mp hxX).1
      simp [U, hxNotP, hxNotX, hxS]
  have hXUdisj : Disjoint X U := by
    rw [Finset.disjoint_left]
    intro x hxX hxU
    exact (Finset.mem_compl.mp hxU) (Finset.mem_filter.mp hxX).1
  have hdefectU : ∀ u ∈ U, defect u = 0 := by
    intro u hu
    apply Finset.card_eq_zero.mpr
    ext p
    constructor
    · intro hp
      have hpP := (Finset.mem_inter.mp hp).2
      have hpu := (D.mem_neighborFinset u p).mp (Finset.mem_inter.mp hp).1
      exact (hPUzero p hpP u hu hpu.symm).elim
    · simp
  have hdefectSum : ∑ x ∈ X, defect x = cut := by
    have hout := sum_outside_inter_eq_finsetGraphCutSize D P
    rw [hcompl, Finset.sum_union hXUdisj] at hout
    have hUz : ∑ u ∈ U, (D.neighborFinset u ∩ P).card = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact hdefectU u hu
    change (∑ x ∈ X, defect x) +
      ∑ u ∈ U, (D.neighborFinset u ∩ P).card = cut at hout
    rw [hUz, add_zero] at hout
    exact hout
  have hmom := privateOccupancy_pairShore_moment_and_two_mul_zero_le
    G.Adj X Z H weight defect m cut (by omega : 2 ≤ m)
      hXlocal hZrowX hHrowX hdefectSum hweight
  let load := ∑ x ∈ X, ∑ b ∈ H.filter (fun b => G.Adj b x), weight b
  have hmoment : load + cut = m * Z.card := by simpa [load] using hmom.1
  have henergy : 2 * Z.card ≤ cut := hmom.2
  have hXdom : ∀ x ∈ X,
      (∑ b ∈ H.filter (fun b => G.Adj b x), weight b) ≤
        (Z.filter fun z => G.Adj z x).card := by
    intro x hx
    have := hXlocal x hx
    omega
  have hpair : ∀ z ∈ Z, ∀ b ∈ H,
      weight b *
        ((U.filter fun u => G.Adj z u ∧ G.Adj b u).card +
          (X.filter fun x => G.Adj z x ∧ G.Adj b x).card) ≤ weight b := by
    intro z hz b hb
    have hz0 : r z = 0 := (Finset.mem_filter.mp hz).2
    have hbPos : 1 < r b := (Finset.mem_filter.mp hb).2
    have hzb : z ≠ b := by intro h; subst b; omega
    let QU := U.filter fun u => G.Adj z u ∧ G.Adj b u
    let QX := X.filter fun x => G.Adj z x ∧ G.Adj b x
    have hdisj : Disjoint QU QX := by
      apply Finset.disjoint_left.mpr
      intro x hxU hxX
      exact Finset.disjoint_left.mp hXUdisj
        (Finset.mem_filter.mp hxX).1 (Finset.mem_filter.mp hxU).1
    have hsub : QU ∪ QX ⊆ G.neighborFinset z ∩ G.neighborFinset b := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxU | hxX
      · have ha := (Finset.mem_filter.mp hxU).2
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset z x).mpr ha.1,
            (G.mem_neighborFinset b x).mpr ha.2⟩
      · have ha := (Finset.mem_filter.mp hxX).2
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset z x).mpr ha.1,
            (G.mem_neighborFinset b x).mpr ha.2⟩
    have hcommon : (G.neighborFinset z ∩ G.neighborFinset b).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro u hu v hv
      by_contra huv
      exact hfree (containsC4_of_two_common hzb huv
        ((G.mem_neighborFinset z u).mp (Finset.mem_inter.mp hu).1).symm
        ((G.mem_neighborFinset b u).mp (Finset.mem_inter.mp hu).2).symm
        ((G.mem_neighborFinset z v).mp (Finset.mem_inter.mp hv).1).symm
        ((G.mem_neighborFinset b v).mp (Finset.mem_inter.mp hv).2).symm)
    have hcard : QU.card + QX.card ≤ 1 := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact (Finset.card_le_card hsub).trans hcommon
    simpa [QU, QX] using Nat.mul_le_mul_left (weight b) hcard
  have hcollision0 := linear_trade_combinedShore_collision_le
    G.Adj U X Z H weight m
    (fun z hz => hrowU z (Finset.mem_filter.mp hz).1)
    hUbalance hXdom hpair hweight
  have hcollision : m * Z.card + load ≤ Z.card ^ 2 := by
    simpa [load, pow_two] using hcollision0
  have hzLower : m ≤ Z.card := by
    simpa [F, B, P, r, Z] using
      c4Free_binarySquare_pureEndpoint_zeroPrivateRows_card_ge
        G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hbound : 2 * q - 4 ≤ cut :=
    two_mul_sub_four_le_of_combinedShore_collision
    hq hqm hzLower henergy hcollision hmoment
  have hquad : q * Z.card ≤ Z.card ^ 2 + cut := by
    rw [hqm]
    nlinarith
  refine ⟨hbound, ?_⟩
  intro hcutEq
  have hZcardEq := zero_card_eq_sub_two_of_strictCut_quadratic_eq
    hq hqm hzLower henergy hquad hcutEq
  have hcutEq' : cut = 2 * q - 4 := by
    simpa [cut, D, P, F] using hcutEq
  have hmTwo : 2 ≤ m := by omega
  have hcutTwoZ : cut = 2 * Z.card := by
    rw [hcutEq', hZcardEq]
    omega
  have hmulSplit : (m - 2) * Z.card + 2 * Z.card = m * Z.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hmTwo]
  have hloadEq : load = (m - 2) * Z.card := by omega
  have hloadReindex : load =
      ∑ b ∈ H, weight b * (X.filter fun x => G.Adj b x).card := by
    simp only [load, Finset.sum_filter]
    have hswap :
        (∑ x ∈ X, ∑ b ∈ H, if G.Adj b x then weight b else 0) =
          ∑ b ∈ H, ∑ x ∈ X, if G.Adj b x then weight b else 0 :=
      Finset.sum_comm
    rw [hswap]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hbx : G.Adj b x <;> simp [hbx]
  have hrowCapEq : ∀ b ∈ H, 0 < weight b →
      (X.filter fun x => G.Adj b x).card = m - 2 := by
    apply weighted_row_capacity_eq_of_sum_eq H weight
      (fun b => (X.filter fun x => G.Adj b x).card)
      (m - 2) Z.card hHrowX hweight
    rw [← hloadReindex]
    exact hloadEq
  have hrowTwo : ∀ b ∈ H, r b = 2 := by
    intro b hb
    have hbB := (Finset.mem_filter.mp hb).1
    have hbPos := (Finset.mem_filter.mp hb).2
    have hbNotF : b ∉ F := by simpa [B] using hbB
    have hmOcc :=
      (c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri b hbNotF).1
    have hsplit : (G.neighborFinset b ∩ S).card =
        (G.neighborFinset b ∩ P).card +
          (G.neighborFinset b ∩ X).card := by
      rw [hSX, Finset.inter_union_distrib_left,
        Finset.card_union_of_disjoint]
      exact hPXdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have hfilter : X.filter (fun x => G.Adj b x) =
        G.neighborFinset b ∩ X := by
      ext x
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    have hwPos : 0 < weight b := by
      change 0 < r b - 1
      omega
    have hxEq := hrowCapEq b hb hwPos
    rw [hfilter] at hxEq
    change (G.neighborFinset b ∩ P).card = 2
    omega
  have hHcardEq : H.card = q - 2 := by
    calc
      H.card = ∑ _b ∈ H, 1 := by simp
      _ = ∑ b ∈ H, weight b := by
        apply Finset.sum_congr rfl
        intro b hb
        have hr := hrowTwo b hb
        simp [weight, hr]
      _ = Z.card := hweight
      _ = q - 2 := hZcardEq
  have hrig := linear_trade_combinedShore_rigidity_of_strictBoundary
    G.Adj U X Z H weight q m cut hqm (by omega) hcutEq' hZcardEq
    (fun z hz => hrowU z (Finset.mem_filter.mp hz).1)
    hUbalance hXdom hpair hweight hmoment
  exact ⟨hZcardEq, hHcardEq, hrowTwo, hrig.2.1, hrig.2.2, hrig.1⟩

/-- Compatibility projection exposing the strict gap and pair saturation. -/
theorem c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_and_saturation
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
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
    let U := Sᶜ
    let B := Fᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    let H := B.filter fun b => 1 < r b
    let weight := fun b => r b - 1
    let cut := finsetGraphCutSize (secondOrderDefectGraph G) P
    2 * q - 4 ≤ cut ∧
      (cut = 2 * q - 4 → Z.card = q - 2 ∧
        ∀ z ∈ Z, ∀ b ∈ H, 0 < weight b →
          (U.filter fun u => G.Adj z u ∧ G.Adj b u).card +
            (X.filter fun x => G.Adj z x ∧ G.Adj b x).card = 1) := by
  have h :=
    c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_rowProfile_and_saturation
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  exact ⟨h.1, fun hcut => ⟨(h.2 hcut).1, (h.2 hcut).2.2.2.2.2⟩⟩

/-- The strict gap and zero-row boundary profile, projected from the stronger
pointwise saturation theorem. -/
theorem c4Free_binarySquare_pureEndpoint_privateCut_gap_and_boundary_zero_card
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
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let B := Fᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    let cut := finsetGraphCutSize (secondOrderDefectGraph G) P
    2 * q - 4 ≤ cut ∧ (cut = 2 * q - 4 → Z.card = q - 2) := by
  have h := c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_and_saturation
    G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  exact ⟨h.1, fun hcut => (h.2 hcut).1⟩

/-- Compatibility projection of the strict private-cut gap. -/
theorem c4Free_binarySquare_pureEndpoint_privateCut_two_mul_sub_four_le
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
      (G.neighborFinset v ∩ S).card = q) :
    2 * q - 4 ≤ finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun p =>
        (G.neighborFinset p ∩ fullLineCenters G S q).card = 1) := by
  exact (c4Free_binarySquare_pureEndpoint_privateCut_gap_and_boundary_zero_card
    G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri).1

end

end Erdos85

#print axioms Erdos85.sum_sub_one_positive_le_card_zeros_of_sum_le_card
#print axioms Erdos85.sum_sub_one_positive_add_defect_eq_card_zeros
#print axioms Erdos85.two_mul_sub_four_le_of_combinedShore_collision
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_rowProfile_and_saturation
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_and_saturation
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_gap_and_boundary_zero_card
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_two_mul_sub_four_le
