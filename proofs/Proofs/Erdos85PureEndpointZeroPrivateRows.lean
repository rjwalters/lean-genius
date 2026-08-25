import Proofs.Erdos85PureEndpointCanonicalPrivatePoints
import Proofs.Erdos85PureEndpointDefectBiregularCut
import Proofs.Erdos85PureEndpointExteriorParallelClass

/-!
# Zero-private rows at the pure endpoint

The exterior incidence supplies more than the defect-cut energy bound.  The
centered private occupancy is an integral trade on the complementary shore.
In a linear uniform incidence structure, such a trade must have at least one
half-row of negative support for every point on a row.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- If a natural-valued function has average one on a finset, its number of
zero entries equals its total positive excess over one. -/
theorem card_zeros_eq_sum_sub_one_of_sum_eq_finset_card
    {α : Type*} [DecidableEq α] (s : Finset α) (r : α → ℕ)
    (hsum : ∑ x ∈ s, r x = s.card) :
    (s.filter fun x => r x = 0).card = ∑ x ∈ s, (r x - 1) := by
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
  omega

/-- In a linear uniform incidence structure, a nonzero integral trade whose
negative coefficients are all `-1` has at least one negative block for every
point on a block. -/
theorem linear_uniform_trade_negative_card_ge
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (Inc : β → α → Prop) [DecidableRel Inc]
    (U : Finset α) (Z P : Finset β)
    (weight : β → ℕ) (m : ℕ)
    (hZ : Z.Nonempty)
    (hrow : ∀ z ∈ Z, (U.filter fun u => Inc z u).card = m)
    (hbalance : ∀ u ∈ U,
      (Z.filter fun z => Inc z u).card =
        ∑ p ∈ P.filter (fun p => Inc p u), weight p)
    (hlinear : ∀ z ∈ Z, ∀ p ∈ P,
      weight p * (U.filter fun u => Inc z u ∧ Inc p u).card ≤ weight p)
    (hweight : ∑ p ∈ P, weight p = Z.card) :
    m ≤ Z.card := by
  classical
  let C := ∑ z ∈ Z, ∑ p ∈ P,
    weight p * (U.filter fun u => Inc z u ∧ Inc p u).card
  have hCupper : C ≤ Z.card * Z.card := by
    calc
      C ≤ ∑ z ∈ Z, ∑ p ∈ P, weight p * 1 := by
        apply Finset.sum_le_sum
        intro z hz
        apply Finset.sum_le_sum
        intro p hp
        simpa using hlinear z hz p hp
      _ = Z.card * Z.card := by
        simp_rw [mul_one]
        rw [hweight]
        simp
  have hCreindex : C = ∑ u ∈ U,
      (Z.filter fun z => Inc z u).card *
        (∑ p ∈ P.filter (fun p => Inc p u), weight p) := by
    simp only [C, Finset.card_eq_sum_ones]
    simp_rw [Finset.sum_filter]
    simp only [ite_and]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    have hswap :
        (∑ z ∈ Z, ∑ p ∈ P, ∑ u ∈ U,
            if Inc z u then if Inc p u then weight p else 0 else 0) =
          ∑ u ∈ U, ∑ p ∈ P, ∑ z ∈ Z,
            if Inc z u then if Inc p u then weight p else 0 else 0 := by
      calc
        (∑ z ∈ Z, ∑ p ∈ P, ∑ u ∈ U,
            if Inc z u then if Inc p u then weight p else 0 else 0) =
            ∑ p ∈ P, ∑ z ∈ Z, ∑ u ∈ U,
              if Inc z u then if Inc p u then weight p else 0 else 0 :=
                Finset.sum_comm
        _ = ∑ p ∈ P, ∑ u ∈ U, ∑ z ∈ Z,
              if Inc z u then if Inc p u then weight p else 0 else 0 := by
                apply Finset.sum_congr rfl
                intro p _hp
                exact Finset.sum_comm
        _ = ∑ u ∈ U, ∑ p ∈ P, ∑ z ∈ Z,
              if Inc z u then if Inc p u then weight p else 0 else 0 :=
                Finset.sum_comm
    simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
    rw [hswap]
    apply Finset.sum_congr rfl
    intro u _hu
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hzu : Inc z u <;> by_cases hpu : Inc p u <;>
      simp [hzu, hpu]
  have hClower : m * Z.card ≤ C := by
    rw [hCreindex]
    calc
      m * Z.card = ∑ u ∈ U, (Z.filter fun z => Inc z u).card := by
        calc
          m * Z.card = Z.card * m := Nat.mul_comm _ _
          _ = ∑ z ∈ Z, (U.filter fun u => Inc z u).card := by
            symm
            exact Finset.sum_const_nat hrow
          _ = ∑ u ∈ U, (Z.filter fun z => Inc z u).card := by
            simp only [Finset.card_eq_sum_ones]
            simp_rw [Finset.sum_filter]
            exact Finset.sum_comm
      _ ≤ ∑ u ∈ U,
          (Z.filter fun z => Inc z u).card *
            (∑ p ∈ P.filter (fun p => Inc p u), weight p) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [← hbalance u hu]
        exact Nat.le_mul_self _
  have hmz : m * Z.card ≤ Z.card * Z.card := hClower.trans hCupper
  exact Nat.le_of_mul_le_mul_right (by
    simpa [Nat.mul_comm] using hmz) (Finset.card_pos.mpr hZ)

private theorem c4Free_commonNeighbor_card_le_one
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

/-- At a preconnected pure endpoint, at least half of the exterior rows
contain no private point.  This is uniform in the private-cut energy. -/
theorem c4Free_binarySquare_pureEndpoint_zeroPrivateRows_card_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
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
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    m ≤ (Fᶜ.filter fun b => (G.neighborFinset b ∩ P).card = 0).card := by
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
  have hZ : Z.Nonempty := by
    obtain ⟨w, hwNotF, _hBcard, _hKzero, _hpair, _hcover, hownerTwo⟩ :=
      c4Free_binarySquare_pureEndpoint_exists_exterior_parallelClass
        G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
    refine ⟨w, Finset.mem_filter.mpr ⟨by simpa [B, F] using hwNotF, ?_⟩⟩
    have hzero : (G.neighborFinset w ∩ P).card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext p
      constructor
      · intro hp
        have hpP := (Finset.mem_inter.mp hp).2
        have hpB := (Finset.mem_inter.mp hp).1
        have hpOwnerTwo := hownerTwo p
          (Finset.mem_inter.mpr ⟨hpB, (Finset.mem_filter.mp hpP).1⟩)
        have hpOwnerOne := (Finset.mem_filter.mp hpP).2
        change (G.neighborFinset p ∩ F).card = 2 at hpOwnerTwo
        omega
      · simp
    simpa [r, P, F] using hzero
  have hPUzero : ∀ p ∈ P, ∀ u ∈ U,
      ¬ (secondOrderDefectGraph G).Adj p u := by
    intro p hp u hu hpu
    have hcut :=
      (c4Free_binarySquare_pureEndpoint_defectCut_biregular
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.2.2.2
    have hpS := (Finset.mem_filter.mp hp).1
    have hpZero := (hcut p hpS).2 (Finset.mem_filter.mp hp).2
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
            have hle := c4Free_commonNeighbor_card_le_one G hfree hne
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
      have hx' : x ∈ G.neighborFinset b ∩ S := by
        rw [heq]
        exact hx
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
        exact ⟨hneighborsB u hu
          ((G.mem_neighborFinset u b).mpr hub), hub.symm⟩
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
      have hcard := (Finset.card_le_card hsub).trans
        (c4Free_commonNeighbor_card_le_one G hfree hzb)
      simpa using Nat.mul_le_mul_left (r b - 1) hcard
  have htrade := linear_uniform_trade_negative_card_ge
    G.Adj U Z B (fun b => r b - 1) m hZ
    (by intro z hz; exact hrow z (Finset.mem_filter.mp hz).1)
    hbalance hlinear hweight
  simpa [F, B, P, r, Z] using htrade

end

end Erdos85

#print axioms Erdos85.linear_uniform_trade_negative_card_ge
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_zeroPrivateRows_card_ge
