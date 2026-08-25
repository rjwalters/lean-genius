import Proofs.Erdos85LinearUniformTradeEqualityGrid
import Proofs.Erdos85PureEndpointMinimumPrivateCutRows

/-!
# The equality grid at a minimum private cut

At cut energy `q`, the uniform private trade attains its support lower bound.
Consequently every zero-private exterior row meets every positive-excess row
in exactly one point of the complementary shore.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

private theorem commonNeighbor_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hv, v', hv', hvv⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at hv hv'
  exact hfree (containsC4_of_two_common hxy hvv hv.1.symm hv.2.symm
    hv'.1.symm hv'.2.symm)

/-- A minimum private cut produces the complete zero/positive intersection
grid on the complementary shore. -/
theorem c4Free_binarySquare_pureEndpoint_minimumPrivateCut_grid_and_exists_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hfour : 4 ∣ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun x =>
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1) = q) :
    let F := fullLineCenters G S q
    let B := Fᶜ
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let U := Sᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    (∀ z ∈ Z, ∀ w ∈ B, 1 < r w →
      (U.filter fun u => G.Adj z u ∧ G.Adj w u).card = 1) ∧
    ∃ w ∈ B, 1 < r w := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let B := Fᶜ
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let U := Sᶜ
  let r : V → ℕ := fun b => (G.neighborFinset b ∩ P).card
  let Z := B.filter fun b => r b = 0
  have hPcard : P.card = q := by
    simpa [P, F] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  have hBcard : B.card = q * (q - 1) := by
    change Fᶜ.card = _
    rw [Finset.card_compl, show F.card = q by simpa [F] using hCcard,
      hcard, Nat.mul_sub_left_distrib]
    simp
  have hrow : ∀ b ∈ B, (U.filter fun u => G.Adj b u).card = m := by
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
      (∑ b ∈ B, r b) = ∑ p ∈ P, (G.neighborFinset p ∩ B).card := hdouble
      _ = P.card * (q - 1) := Finset.sum_const_nat hPdeg
      _ = B.card := by rw [hPcard, hBcard]
  have hweight : ∑ b ∈ B, (r b - 1) = Z.card := by
    symm
    simpa [Z] using
      card_zeros_eq_sum_sub_one_of_sum_eq_finset_card B r hsumB
  have hPUzero : ∀ p ∈ P, ∀ u ∈ U,
      ¬ (secondOrderDefectGraph G).Adj p u := by
    intro p hp u hu hpu
    have hcutBireg :=
      (c4Free_binarySquare_pureEndpoint_defectCut_biregular
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.2.2.2
    have hpS := (Finset.mem_filter.mp hp).1
    have hpZero := (hcutBireg p hpS).2 (Finset.mem_filter.mp hp).2
    have hmem : u ∈ (secondOrderDefectGraph G).neighborFinset p ∩ Sᶜ :=
      Finset.mem_inter.mpr
        ⟨((secondOrderDefectGraph G).mem_neighborFinset p u).mpr hpu,
          by simpa [U] using hu⟩
    rw [Finset.card_eq_zero.mp hpZero] at hmem
    simp at hmem
  have hlocalSum : ∀ u ∈ U,
      ∑ b ∈ G.neighborFinset u, r b = (G.neighborFinset u).card := by
    intro u hu
    have hdouble := sum_neighbor_inter_card_comm G (G.neighborFinset u) P
    change (∑ b ∈ G.neighborFinset u, r b) = _ at hdouble
    calc
      (∑ b ∈ G.neighborFinset u, r b) =
          ∑ p ∈ P, (G.neighborFinset p ∩ G.neighborFinset u).card := hdouble
      _ = P.card := by
        calc
          (∑ p ∈ P, (G.neighborFinset p ∩ G.neighborFinset u).card) =
              P.card * 1 := by
            apply Finset.sum_const_nat
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
            have hle := commonNeighbor_card_le_one G hfree hne
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
  have hbalance : ∀ u ∈ U,
      (Z.filter fun z => G.Adj z u).card =
        ∑ b ∈ B.filter (fun b => G.Adj b u), (r b - 1) := by
    intro u hu
    have hzeroLocal := card_zeros_eq_sum_sub_one_of_sum_eq_finset_card
      (G.neighborFinset u) r (hlocalSum u hu)
    have hNB : G.neighborFinset u = B.filter fun b => G.Adj b u := by
      ext b
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · intro hub
        exact ⟨hneighborsB u hu ((G.mem_neighborFinset u b).mpr hub), hub.symm⟩
      · exact fun hb => hb.2.symm
    rw [hNB] at hzeroLocal
    have hfilter :
        (B.filter (fun b => G.Adj b u)).filter (fun b => r b = 0) =
          Z.filter fun z => G.Adj z u := by
      ext b
      simp [Z, and_assoc, and_left_comm, and_comm]
    rw [hfilter] at hzeroLocal
    exact hzeroLocal
  have hlinear : ∀ z ∈ Z, ∀ b ∈ B,
      (r b - 1) * (U.filter fun u => G.Adj z u ∧ G.Adj b u).card ≤ r b - 1 := by
    intro z hz b hb
    by_cases hzb : z = b
    · subst b
      have hz0 := (Finset.mem_filter.mp hz).2
      simp [hz0]
    · have hsub : U.filter (fun u => G.Adj z u ∧ G.Adj b u) ⊆
          G.neighborFinset z ∩ G.neighborFinset b := by
        intro u hu
        have hd := Finset.mem_filter.mp hu
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset z u).mpr hd.2.1,
            (G.mem_neighborFinset b u).mpr hd.2.2⟩
      have hcardCommon := (Finset.card_le_card hsub).trans
        (commonNeighbor_card_le_one G hfree hzb)
      simpa using Nat.mul_le_mul_left (r b - 1) hcardCommon
  have hzeroGlobal :=
    (c4Free_binarySquare_pureEndpoint_minimumPrivateCut_rowProfile
      G hfree hq hqm hfour hreg hcard S hempty hCcard hshore htri hcut).1
  have hZupper : Z.card ≤ m := by
    have hsub : Z ⊆ Finset.univ.filter fun v =>
        (G.neighborFinset v ∩ P).card = 0 := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2⟩
    have hc := Finset.card_le_card hsub
    change 2 * (Finset.univ.filter fun v =>
      (G.neighborFinset v ∩ P).card = 0).card = q at hzeroGlobal
    omega
  have hZlower : m ≤ Z.card := by
    simpa [F, B, P, r, Z] using
      c4Free_binarySquare_pureEndpoint_zeroPrivateRows_card_ge
        G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hZeq : m = Z.card := by omega
  have hgrid := linear_uniform_trade_eq_card_common_eq_one
    G.Adj U Z B (fun b => r b - 1) m
    (fun z hz => hrow z (Finset.mem_filter.mp hz).1)
    hbalance hlinear hweight hZeq
  constructor
  · intro z hz w hw hrw
    exact hgrid z hz w hw (Nat.sub_pos_of_lt hrw)
  · have hZnonempty : Z.Nonempty := by
      apply Finset.card_pos.mp
      rw [← hZeq]
      omega
    obtain ⟨z, hz⟩ := hZnonempty
    by_contra hnone
    push Not at hnone
    have hstrict : (∑ b ∈ B, r b) < ∑ _b ∈ B, 1 := by
      apply Finset.sum_lt_sum
      · intro b hb
        exact hnone b hb
      · refine ⟨z, (Finset.mem_filter.mp hz).1, ?_⟩
        have hzZero := (Finset.mem_filter.mp hz).2
        omega
    rw [hsumB] at hstrict
    simp at hstrict

/-- Compatibility projection of the equality-grid theorem. -/
theorem c4Free_binarySquare_pureEndpoint_minimumPrivateCut_grid
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hfour : 4 ∣ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun x =>
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1) = q) :
    let F := fullLineCenters G S q
    let B := Fᶜ
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let U := Sᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    ∀ z ∈ Z, ∀ w ∈ B, 1 < r w →
      (U.filter fun u => G.Adj z u ∧ G.Adj w u).card = 1 := by
  exact (c4Free_binarySquare_pureEndpoint_minimumPrivateCut_grid_and_exists_positive
    G hfree hq hqm hfour hreg hcard hconn S hempty hCcard hshore htri hcut).1

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_minimumPrivateCut_grid_and_exists_positive
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_minimumPrivateCut_grid
