import Proofs.Erdos85DegreeSixColorSectorSplit
import Proofs.Erdos85DegreeSixOddDiagonal
import Proofs.Erdos85DegreeSixOddDiagonalSmall

/-!
# Degree-six empty-sector assembly

Carrier lemmas for the empty color-sector branch of the degree-six exact
boundary.  The master contradiction is assembled here once the remaining
odd-diagonal discharge is available.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Common quotient data used by every odd diagonal-two exclusion at the
degree-six boundary. -/
theorem degreeSix_diagonal_two_quotient_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent) :
    let D := secondOrderDefectGraph G
    let Q := componentQuotientMatrix G D
    let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
    (∑ c, size c) = 33 ∧
    (∀ c, (∑ t, Q c t) = 6) ∧
    (∀ c t, size c * Q c t = size t * Q t c) ∧
    (∑ t, Q w t * Q t w) = size w + 3 ∧
    ∀ c t, Q c t ≤ 6 := by
  dsimp
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hrow : ∀ c : D.ConnectedComponent, (∑ t, Q c t) = 6 := by
    intro c
    exact sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hbal : ∀ c t, size c * Q c t = size t * Q t c := by
    intro c t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c t
  have hsq : (∑ t, Q w t * Q t w) = size w + 3 := by
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w w
    simpa [Q, size, D, Matrix.mul_apply, Nat.add_comm] using hs
  refine ⟨htotal, hrow, hbal, hsq, ?_⟩
  intro c t
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ t)).trans_eq (hrow c)

/-- The degree-six boundary order `33` is odd, so some defect component
has odd order. -/
theorem degreeSix_exists_odd_order_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hcard : Fintype.card V = 33) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard := by
  classical
  by_contra hnone
  push Not at hnone
  have hparts : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard) = Fintype.card V := by
    simpa using sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)
  have hdvd : 2 ∣ ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard := by
    apply Finset.dvd_sum
    intro c _
    exact (Nat.not_odd_iff_even.mp (hnone c)).two_dvd
  rw [hparts, hcard] at hdvd
  omega

/-- Once all odd components are zero-diagonal, the nonsquare trace six
must be carried by a positive-diagonal even component. -/
theorem degreeSix_exists_even_carrier_of_odd_zero_diagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hodd0 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      Even c.supp.ncard ∧
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  classical
  have htrace := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (by norm_num)
  by_contra hnone
  push Not at hnone
  have hzero : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
    intro c
    by_cases hoddc : Odd c.supp.ncard
    · exact hodd0 c hoddc
    · have heven : Even c.supp.ncard := Nat.not_odd_iff_even.mp hoddc
      have := hnone c heven
      omega
  have hsum : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c c) = 0 :=
    Finset.sum_eq_zero fun c _ => hzero c
  rw [hsum] at htrace
  exact absurd htrace.symm (by norm_num)

/-! ## Order-eleven discharge -/

theorem false_of_degreeSix_orderEleven_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (coord : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hcoord : ∀ c, Function.Injective (coord c))
    (hcoordRange : ∀ c, Set.range (coord c) = c.supp)
    (hcoordD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (coord c x) =
      {coord c (x - 1), coord c (x + 1)})
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw11 : w.supp.ncard = 11)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) : False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  let S : Finset D.ConnectedComponent := Finset.univ.erase w
  let q : D.ConnectedComponent → ℕ := fun t ↦ Q w t
  let r : D.ConnectedComponent → ℕ := fun t ↦ Q t w
  obtain ⟨htotal, hrow, hbal, hsq, hle⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  change ∀ c t, size c * Q c t = size t * Q t c at hbal
  change (∑ t, Q w t * Q t w) = size w + 3 at hsq
  change ∀ c t, Q c t ≤ 6 at hle
  have hsw : size w = 11 := hw11
  have hdiagQ : Q w w = 2 := hdiag
  have hextRow : (∑ t ∈ S, q t) = 4 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun t ↦ Q w t) (Finset.mem_univ w)
    have hwrow := hrow w
    change Q w w + (∑ t ∈ Finset.univ.erase w, Q w t) = ∑ t, Q w t at hadd
    change (∑ t ∈ Finset.univ.erase w, Q w t) = 4
    rw [hdiagQ] at hadd
    omega
  have hextSq : (∑ t ∈ S, q t * r t) = 10 := by
    have hadd := Finset.add_sum_erase Finset.univ
      (fun t ↦ Q w t * Q t w) (Finset.mem_univ w)
    change Q w w * Q w w + (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) =
      ∑ t, Q w t * Q t w at hadd
    change (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) = 10
    rw [hdiagQ] at hadd
    rw [hsw] at hsq
    omega
  have hextSize : (∑ t ∈ S, size t) = 22 := by
    have hadd := Finset.add_sum_erase Finset.univ size (Finset.mem_univ w)
    change size w + (∑ t ∈ Finset.univ.erase w, size t) = ∑ t, size t at hadd
    change (∑ t ∈ Finset.univ.erase w, size t) = 22
    rw [hsw, htotal] at hadd
    omega
  have hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 11 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 22 ∧ q t = 2 ∧ r t = 1) ∨
      (size t = 11 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 11 ∧ q t = 3 ∧ r t = 3) ∨
      (size t = 22 ∧ q t = 4 ∧ r t = 2) := by
    intro t ht
    rcases Nat.eq_zero_or_pos (q t) with hq0 | hqpos
    · exact Or.inl hq0
    right
    have htw : t ≠ w := by simpa [S] using ht
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal, hsw] at hpair
    have hst : size t ≤ 22 := by omega
    have hqle : q t ≤ 4 := by
      have hterm := Finset.single_le_sum (f := q) (fun _ _ ↦ Nat.zero_le _) ht
      rw [hextRow] at hterm
      exact hterm
    have hb := hbal w t
    rw [hsw] at hb
    change 11 * q t = size t * r t at hb
    have hst3 : 3 ≤ size t := hr t
    change 3 ≤ size t at hst3
    have hrpos : 1 ≤ r t := by
      by_contra hn
      have hr0 : r t = 0 := by omega
      rw [hr0, mul_zero] at hb
      omega
    have hrle : r t ≤ 6 := hle t w
    have hprod : q t * r t ≤ 10 := by
      have hterm := Finset.single_le_sum (f := fun z ↦ q z * r z)
        (fun _ _ ↦ Nat.zero_le _) ht
      rw [hextSq] at hterm
      exact hterm
    exact OddDiagonalSmall.eleven_partner_type hb hqpos hqle hrpos hrle hprod hst
  have hagg := OddDiagonalSmall.eleven_contact_aggregate S size q r hclass
  have husedLe : (∑ t ∈ S, if q t = 0 then 0 else size t) ≤ 22 := by
    calc
      _ ≤ ∑ t ∈ S, size t := by
        apply Finset.sum_le_sum
        intro t _
        by_cases hqt : q t = 0 <;> simp [hqt]
      _ = 22 := hextSize
  rw [hextRow] at hagg
  rw [hextSq] at hagg
  rw [hagg.2.2] at husedLe
  have hc := OddDiagonalSmall.eleven_pattern_counts hagg.1.symm hagg.2.1.symm husedLe
  let P1 := S.filter fun t ↦ size t = 11 ∧ q t = 1 ∧ r t = 1
  let P4 := S.filter fun t ↦ size t = 11 ∧ q t = 3 ∧ r t = 3
  have hP1 : P1.card = 1 := hc.1
  have hP4 : P4.card = 1 := hc.2.2.2.1
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hP1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hP4
  have huData := Finset.mem_filter.mp (show u ∈ P1 by rw [hu]; simp)
  have htData := Finset.mem_filter.mp (show t ∈ P4 by rw [ht]; simp)
  have hwu : w ≠ u := Ne.symm (by simpa [S] using huData.1)
  have hwt : w ≠ t := Ne.symm (by simpa [S] using htData.1)
  have htu : t ≠ u := by intro h; subst t; omega
  have husedEq : (∑ z ∈ S, if q z = 0 then 0 else size z) = 22 := by
    rw [hagg.2.2]
    omega
  have hqposAll : ∀ v ∈ S, 0 < q v := by
    intro v hv
    by_contra hn
    have hq0 : q v = 0 := by omega
    have haddUsed := Finset.add_sum_erase S
      (fun z ↦ if q z = 0 then 0 else size z) hv
    have haddSize := Finset.add_sum_erase S size hv
    have hleErase :
        (∑ z ∈ S.erase v, if q z = 0 then 0 else size z) ≤
          ∑ z ∈ S.erase v, size z := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : q z = 0 <;> simp [hz]
    have huErase : (∑ x ∈ S.erase v, if q x = 0 then 0 else size x) = 22 := by
      rw [husedEq, hq0] at haddUsed
      simpa using haddUsed
    rw [hextSize] at haddSize
    have hv3 : 3 ≤ size v := hr v
    change 3 ≤ size v at hv3
    omega
  have huniv : (Finset.univ : Finset D.ConnectedComponent) = {w, t, u} := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hvw : v = w
    · exact Or.inl hvw
    right
    have hvS : v ∈ S := by simp [S, hvw]
    have hvpos := hqposAll v hvS
    rcases hclass v hvS with h0 | h1 | h2 | h3 | h4 | h5
    · omega
    · right
      have hvP : v ∈ P1 := Finset.mem_filter.mpr ⟨hvS, h1⟩
      rw [hu] at hvP
      simpa using hvP
    · have hvP : v ∈ S.filter (fun z ↦ size z = 22 ∧ q z = 2 ∧ r z = 1) :=
        Finset.mem_filter.mpr ⟨hvS, h2⟩
      have hz := Finset.card_eq_zero.mp hc.2.1
      exact absurd hvP (by simpa [hz])
    · have hvP : v ∈ S.filter (fun z ↦ size z = 11 ∧ q z = 2 ∧ r z = 2) :=
        Finset.mem_filter.mpr ⟨hvS, h3⟩
      have hz := Finset.card_eq_zero.mp hc.2.2.1
      exact absurd hvP (by simpa [hz])
    · left
      have hvP : v ∈ P4 := Finset.mem_filter.mpr ⟨hvS, h4⟩
      rw [ht] at hvP
      simpa using hvP
    · have hvP : v ∈ S.filter (fun z ↦ size z = 22 ∧ q z = 4 ∧ r z = 2) :=
        Finset.mem_filter.mpr ⟨hvS, h5⟩
      have hz := Finset.card_eq_zero.mp hc.2.2.2.2
      exact absurd hvP (by simpa [hz])
  have hrowt := hrow t
  have hrowu := hrow u
  obtain ⟨_, _, _, hsqt, _⟩ := degreeSix_diagonal_two_quotient_profile G hfree hmin hcard t
  obtain ⟨_, _, _, hsqu, _⟩ := degreeSix_diagonal_two_quotient_profile G hfree hmin hcard u
  change (∑ z, Q t z * Q z t) = size t + 3 at hsqt
  change (∑ z, Q u z * Q z u) = size u + 3 at hsqu
  rw [huniv] at hrowt hrowu hsqt hsqu
  simp [hwt, hwu, htu] at hrowt hrowu hsqt hsqu
  have hQtu : Q t u = Q u t := by
    have hb := hbal t u
    rw [htData.2.1, huData.2.1] at hb
    omega
  letI : NeZero t.supp.ncard := ⟨by
    change t.supp.ncard ≠ 0
    change size t ≠ 0
    rw [htData.2.1]
    norm_num⟩
  letI : NeZero u.supp.ncard := ⟨by
    change u.supp.ncard ≠ 0
    change size u ≠ 0
    rw [huData.2.1]
    norm_num⟩
  have hdicht := oddComponent_diagonalQuotient_eq_zero_or_two
    G hfree (d := 6) (r := t.supp.ncard) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (by
        change 3 ≤ size t; omega)
      (by change Odd (size t); rw [htData.2.1]; norm_num) t
        (coord t) (hcoord t)
        (hcoordRange t) (hcoordD t)
  have hdichu := oddComponent_diagonalQuotient_eq_zero_or_two
    G hfree (d := 6) (r := u.supp.ncard) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (by
        change 3 ≤ size u; omega)
      (by change Odd (size u); rw [huData.2.1]; norm_num) u
        (coord u) (hcoord u)
        (hcoordRange u) (hcoordD u)
  exact OddDiagonal.false_of_eleven_diag_two Q size w t u hwt hwu htu
    hsw htData.2.1 huData.2.1 htData.2.2.1 huData.2.2.1
    htData.2.2.2 huData.2.2.2 hQtu hdiagQ hdicht hdichu
    (by omega) (by omega) (by omega) (by omega)

/-! ## Order-fifteen discharge -/

theorem false_of_degreeSix_orderFifteen_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, 3 ≤ c.supp.ncard)
    (coord : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hcoord : ∀ c, Function.Injective (coord c))
    (hcoordRange : ∀ c, Set.range (coord c) = c.supp)
    (hcoordD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (coord c x) =
      {coord c (x - 1), coord c (x + 1)})
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw15 : w.supp.ncard = 15)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) : False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  let S : Finset D.ConnectedComponent := Finset.univ.erase w
  let q : D.ConnectedComponent → ℕ := fun t ↦ Q w t
  let r : D.ConnectedComponent → ℕ := fun t ↦ Q t w
  obtain ⟨htotal, hrow, hbal, hsq, hle⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  change ∀ c t, size c * Q c t = size t * Q t c at hbal
  change (∑ t, Q w t * Q t w) = size w + 3 at hsq
  change ∀ c t, Q c t ≤ 6 at hle
  have hsw : size w = 15 := hw15
  have hdiagQ : Q w w = 2 := hdiag
  have hextRow : (∑ t ∈ S, q t) = 4 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun t ↦ Q w t) (Finset.mem_univ w)
    have hwrow := hrow w
    change Q w w + (∑ t ∈ Finset.univ.erase w, Q w t) = ∑ t, Q w t at hadd
    change (∑ t ∈ Finset.univ.erase w, Q w t) = 4
    rw [hdiagQ] at hadd
    omega
  have hextSq : (∑ t ∈ S, q t * r t) = 14 := by
    have hadd := Finset.add_sum_erase Finset.univ
      (fun t ↦ Q w t * Q t w) (Finset.mem_univ w)
    change Q w w * Q w w + (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) =
      ∑ t, Q w t * Q t w at hadd
    change (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) = 14
    rw [hdiagQ] at hadd
    rw [hsw] at hsq
    omega
  have hextSize : (∑ t ∈ S, size t) = 18 := by
    have hadd := Finset.add_sum_erase Finset.univ size (Finset.mem_univ w)
    change size w + (∑ t ∈ Finset.univ.erase w, size t) = ∑ t, size t at hadd
    change (∑ t ∈ Finset.univ.erase w, size t) = 18
    rw [hsw, htotal] at hadd
    omega
  have hclass : ∀ t ∈ S, q t = 0 ∨
      (size t = 15 ∧ q t = 1 ∧ r t = 1) ∨
      (size t = 5 ∧ q t = 1 ∧ r t = 3) ∨
      (size t = 3 ∧ q t = 1 ∧ r t = 5) ∨
      (size t = 15 ∧ q t = 2 ∧ r t = 2) ∨
      (size t = 10 ∧ q t = 2 ∧ r t = 3) ∨
      (size t = 6 ∧ q t = 2 ∧ r t = 5) ∨
      (size t = 5 ∧ q t = 2 ∧ r t = 6) ∨
      (size t = 15 ∧ q t = 3 ∧ r t = 3) := by
    intro t ht
    rcases Nat.eq_zero_or_pos (q t) with hq0 | hqpos
    · exact Or.inl hq0
    right
    have htw : t ≠ w := by simpa [S] using ht
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal, hsw] at hpair
    have hst : size t ≤ 18 := by omega
    have hqle : q t ≤ 4 := by
      have hterm := Finset.single_le_sum (f := q) (fun _ _ ↦ Nat.zero_le _) ht
      rw [hextRow] at hterm
      exact hterm
    have hb := hbal w t
    rw [hsw] at hb
    change 15 * q t = size t * r t at hb
    have hrpos : 1 ≤ r t := by
      by_contra hn
      have hr0 : r t = 0 := by omega
      rw [hr0, mul_zero] at hb
      omega
    have hrle : r t ≤ 6 := hle t w
    have hprod : q t * r t ≤ 14 := by
      have hterm := Finset.single_le_sum (f := fun z ↦ q z * r z)
        (fun _ _ ↦ Nat.zero_le _) ht
      rw [hextSq] at hterm
      exact hterm
    exact OddDiagonalSmall.fifteen_partner_type hb hqpos hqle hrpos hrle hprod hst
  have hagg := OddDiagonalSmall.fifteen_contact_aggregate S size q r hclass
  have husedLe : (∑ t ∈ S, if q t = 0 then 0 else size t) ≤ 18 := by
    calc
      _ ≤ ∑ t ∈ S, size t := by
        apply Finset.sum_le_sum
        intro t _
        by_cases hqt : q t = 0 <;> simp [hqt]
      _ = 18 := hextSize
  rw [hextRow] at hagg
  rw [hextSq] at hagg
  rw [hagg.2.2] at husedLe
  have hc := OddDiagonalSmall.fifteen_pattern_counts hagg.1.symm hagg.2.1.symm husedLe
  let P3 := S.filter fun t ↦ size t = 3 ∧ q t = 1 ∧ r t = 5
  have hP3 : P3.card = 1 := by
    rcases hc with h | h | h <;> exact h.2.2.1
  have hn6 : (S.filter fun t ↦ size t = 6 ∧ q t = 2 ∧ r t = 5).card = 0 := by
    rcases hc with h | h | h <;> exact h.2.2.2.2.2.1
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hP3
  have heData := Finset.mem_filter.mp (show e ∈ P3 by rw [he]; simp)
  have hwe : w ≠ e := Ne.symm (by simpa [S] using heData.1)
  have husedEq : (∑ z ∈ S, if q z = 0 then 0 else size z) = 18 := by
    rw [hagg.2.2]
    rcases hc with h | h | h <;> omega
  have hqposAll : ∀ v ∈ S, 0 < q v := by
    intro v hv
    by_contra hn
    have hq0 : q v = 0 := by omega
    have haddUsed := Finset.add_sum_erase S
      (fun z ↦ if q z = 0 then 0 else size z) hv
    have haddSize := Finset.add_sum_erase S size hv
    have hleErase :
        (∑ z ∈ S.erase v, if q z = 0 then 0 else size z) ≤
          ∑ z ∈ S.erase v, size z := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : q z = 0 <;> simp [hz]
    have huErase : (∑ z ∈ S.erase v, if q z = 0 then 0 else size z) = 18 := by
      rw [husedEq, hq0] at haddUsed
      simpa using haddUsed
    rw [hextSize] at haddSize
    have hv3 : 3 ≤ size v := hr v
    change 3 ≤ size v at hv3
    omega
  have hcover : ∀ t, t = w ∨ t = e ∨ 5 ∣ size t := by
    intro t
    by_cases htw : t = w
    · exact Or.inl htw
    right
    have htS : t ∈ S := by simp [S, htw]
    have htpos := hqposAll t htS
    rcases hclass t htS with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · omega
    · right; rw [h1.1]; norm_num
    · right; rw [h2.1]
    · left
      have htP : t ∈ P3 := Finset.mem_filter.mpr ⟨htS, h3⟩
      rw [he] at htP
      simpa using htP
    · right; rw [h4.1]; norm_num
    · right; rw [h5.1]; norm_num
    · have htP : t ∈ S.filter (fun z ↦ size z = 6 ∧ q z = 2 ∧ r z = 5) :=
        Finset.mem_filter.mpr ⟨htS, h6⟩
      rw [Finset.card_eq_zero.mp hn6] at htP
      simp at htP
    · right; rw [h7.1]
    · right; rw [h8.1]; norm_num
  have hediag := degreeSix_orderThree_diagonal_zero G hfree hmin hcard
    coord hcoord hcoordRange hcoordD e (by
      change size e = 3
      exact heData.2.1)
  have herow := hrow e
  exact OddDiagonal.false_of_fifteen_pattern_common Q size w e hwe
    heData.2.1 heData.2.2.2 hediag herow (hbal e) hcover

/-- An order-thirteen component cannot have diagonal quotient two at the
degree-six boundary. -/
theorem false_of_degreeSix_orderThirteen_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw13 : w.supp.ncard = 13)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hsize : ∀ t, t ≠ w → size t ≤ 20 := by
    intro t htw
    have hle := two_distinct_terms_le_sum size htw
    rw [htotal] at hle
    dsimp [size] at hle ⊢
    rw [hw13] at hle
    omega
  have hrow (c : D.ConnectedComponent) : (∑ t, Q c t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6 := by
    intro t
    constructor
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ t)).trans_eq (hrow w)
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w)).trans_eq (hrow t)
  have hbal : ∀ t, size w * Q w t = size t * Q t w := by
    intro t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w t
  have hsq : (∑ t, Q w t * Q t w) = 16 := by
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w w
    simpa [Q, size, D, Matrix.mul_apply, hw13] using hs
  exact OddDiagonal.false_of_thirteen_diag_two
    Q size w hw13 hsize hrev hbal hdiag (hrow w) hsq

/-- A component of prime order at least seventeen cannot have diagonal
quotient two at the degree-six boundary. -/
theorem false_of_degreeSix_largePrime_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent) {o : ℕ}
    (hwo : w.supp.ncard = o) (hop : o.Prime) (ho17 : 17 ≤ o)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hsize : ∀ t, t ≠ w → size t ≤ 33 - o := by
    intro t htw
    have hle := two_distinct_terms_le_sum size htw
    rw [htotal] at hle
    dsimp [size] at hle ⊢
    rw [hwo] at hle
    omega
  have hrow (c : D.ConnectedComponent) : (∑ t, Q c t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6 := by
    intro t
    constructor
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ t)).trans_eq (hrow w)
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w)).trans_eq (hrow t)
  have hbal : ∀ t, size w * Q w t = size t * Q t w := by
    intro t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w t
  exact OddDiagonal.false_of_large_prime_diag_two
    Q size w hwo hop ho17 hsize hrev hbal hdiag (hrow w)

/-- Order twenty-seven has no admissible external quotient partner within
the remaining six vertices. -/
theorem false_of_degreeSix_orderTwentySeven_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw27 : w.supp.ncard = 27)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  obtain ⟨htotal, hrow, hbal, _, hle⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  change ∀ c t, size c * Q c t = size t * Q t c at hbal
  change ∀ c t, Q c t ≤ 6 at hle
  have hsw : size w = 27 := hw27
  have hdiagQ : Q w w = 2 := hdiag
  have hzero : ∀ t, t ≠ w → Q w t = 0 := by
    intro t htw
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal] at hpair
    have hst : size t ≤ 6 := by dsimp [size] at hpair ⊢; omega
    have hst3 : 3 ≤ size t := hr t
    have hb := hbal w t
    rw [hsw] at hb
    by_contra hq
    have hqpos : 0 < Q w t := Nat.pos_of_ne_zero hq
    have hrt := hle t w
    interval_cases (size t) <;> omega
  have hsum : (∑ t, Q w t) = Q w w := by
    rw [← Finset.sum_subset (Finset.subset_univ {w})]
    · simp
    · intro t _ ht
      exact hzero t (by simpa using ht)
  have hwrow := hrow w
  rw [hsum, hdiagQ] at hwrow
  omega

/-- For an order-twenty-five diagonal-two component, detailed balance
forces every external reverse quotient to be at most five.  The external
row mass four then contributes at most twenty to the square, short of the
required twenty-four. -/
theorem false_of_degreeSix_orderTwentyFive_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw25 : w.supp.ncard = 25)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  obtain ⟨htotal, hrow, hbal, hsq, hle⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  change ∀ c t, size c * Q c t = size t * Q t c at hbal
  change (∑ t, Q w t * Q t w) = size w + 3 at hsq
  change ∀ c t, Q c t ≤ 6 at hle
  have hsw : size w = 25 := hw25
  have hdiagQ : Q w w = 2 := hdiag
  have hrev5 : ∀ t, t ≠ w → Q t w ≤ 5 := by
    intro t htw
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal, hsw] at hpair
    have hst3 : 3 ≤ size t := hr t
    have hst8 : size t ≤ 8 := by omega
    have hb := hbal w t
    rw [hsw] at hb
    have hqt := hle w t
    have hrt := hle t w
    interval_cases (size t) <;> omega
  have hextRow : (∑ t ∈ Finset.univ.erase w, Q w t) = 4 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun t ↦ Q w t)
      (Finset.mem_univ w)
    have hwrow := hrow w
    change Q w w + (∑ t ∈ Finset.univ.erase w, Q w t) =
      ∑ t, Q w t at hadd
    rw [hdiagQ] at hadd
    omega
  have hextSqLe : (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) ≤ 20 := by
    calc
      (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) ≤
          ∑ t ∈ Finset.univ.erase w, Q w t * 5 := by
            apply Finset.sum_le_sum
            intro t ht
            exact Nat.mul_le_mul_left _ (hrev5 t (Finset.ne_of_mem_erase ht))
      _ = 5 * 4 := by rw [← Finset.sum_mul, hextRow]; omega
      _ = 20 := by omega
  have hextSq : (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) = 24 := by
    have hadd := Finset.add_sum_erase Finset.univ
      (fun t ↦ Q w t * Q t w) (Finset.mem_univ w)
    change Q w w * Q w w +
      (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) =
        ∑ t, Q w t * Q t w at hadd
    rw [hdiagQ] at hadd
    rw [hsw] at hsq
    omega
  omega

/-- An order-twenty-one diagonal-two component has external row mass four,
but its external carrier has total order twelve.  Detailed balance and the
reverse row bound six would require `21 * 4 ≤ 12 * 6`. -/
theorem false_of_degreeSix_orderTwentyOne_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw21 : w.supp.ncard = 21)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  obtain ⟨htotal, hrow, hbal, _, hle⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  change ∀ c t, size c * Q c t = size t * Q t c at hbal
  change ∀ c t, Q c t ≤ 6 at hle
  have hsw : size w = 21 := hw21
  have hdiagQ : Q w w = 2 := hdiag
  have hextRow : (∑ t ∈ Finset.univ.erase w, Q w t) = 4 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun t ↦ Q w t)
      (Finset.mem_univ w)
    have hwrow := hrow w
    change Q w w + (∑ t ∈ Finset.univ.erase w, Q w t) =
      ∑ t, Q w t at hadd
    rw [hdiagQ] at hadd
    omega
  have hextSize : (∑ t ∈ Finset.univ.erase w, size t) = 12 := by
    have hadd := Finset.add_sum_erase Finset.univ size (Finset.mem_univ w)
    change size w + (∑ t ∈ Finset.univ.erase w, size t) =
      ∑ t, size t at hadd
    rw [hsw, htotal] at hadd
    omega
  have hmass : 21 * 4 ≤ 12 * 6 := by
    calc
      21 * 4 = ∑ t ∈ Finset.univ.erase w, 21 * Q w t := by
        rw [← Finset.mul_sum, hextRow]
      _ = ∑ t ∈ Finset.univ.erase w, size t * Q t w := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← hbal w t, hsw]
      _ ≤ ∑ t ∈ Finset.univ.erase w, size t * 6 := by
        apply Finset.sum_le_sum
        intro t _
        exact Nat.mul_le_mul_left _ (hle t w)
      _ = 12 * 6 := by rw [← Finset.sum_mul, hextSize]
  omega

/-- An order-thirty-three component exhausts the carrier, so diagonal two
cannot supply the degree-six row. -/
theorem false_of_degreeSix_orderThirtyThree_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw33 : w.supp.ncard = 33)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  obtain ⟨htotal, hrow, _, _, _⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  have hsw : size w = 33 := hw33
  have hdiagQ : Q w w = 2 := hdiag
  have hall : ∀ t : D.ConnectedComponent, t = w := by
    intro t
    by_contra htw
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal] at hpair
    have hst3 : 3 ≤ size t := hr t
    rw [hsw] at hpair
    omega
  have huniv : (Finset.univ : Finset D.ConnectedComponent) = {w} := by
    ext t
    simp [hall t]
  have hwrow := hrow w
  rw [huniv] at hwrow
  simp at hwrow
  omega

/-- Once the empty-sector analysis supplies zero diagonal on every odd
component, the eight odd-to-even cover terminals give the boundary
contradiction immediately. -/
theorem false_of_degreeSix_of_odd_zero_diagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd0 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    False := by
  obtain ⟨o, hoOdd⟩ := degreeSix_exists_odd_order_component G hcard
  obtain ⟨e, heEven, _⟩ :=
    degreeSix_exists_even_carrier_of_odd_zero_diagonal
      G hfree hmin hcard hodd0
  have hzero3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3 →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
    intro c hc
    exact hodd0 c (by rw [hc]; norm_num)
  have hzero5 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 5 →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
    intro c hc
    exact hodd0 c (by rw [hc]; norm_num)
  obtain ⟨a, b, hba, h36 | h510 | h714 | h918 | h1122 | h312 | h520 | h318⟩ :=
    degreeSix_odd_to_even_cover_order_cases
      G hfree hmin hcard hr o e hoOdd heEven
  · exact false_of_degreeSix_oddEven_cover_three_six
      G hfree hmin hcard u hu huRange huD hr hzero3
        a b h36.1 h36.2 hba
  · exact false_of_degreeSix_oddEven_cover_five_ten
      G hfree hmin hcard hr hzero3 hzero5 a b h510.1 h510.2 hba
  · have haa := hodd0 a (by rw [h714.1]; norm_num)
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
    have hab : componentQuotientMatrix G (secondOrderDefectGraph G) a b = 2 := by
      rw [h714.1, h714.2, hba, mul_one] at hbal
      omega
    exact false_of_degreeSix_oddEven_cover_seven_fourteen
      G hfree hmin hcard hr a b h714.1 h714.2 haa hab
  · have haa := hodd0 a (by rw [h918.1]; norm_num)
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
    have hab : componentQuotientMatrix G (secondOrderDefectGraph G) a b = 2 := by
      rw [h918.1, h918.2, hba, mul_one] at hbal
      omega
    exact false_of_degreeSix_oddEven_cover_nine_eighteen
      G hfree hmin hcard hr a b h918.1 h918.2 haa hab
  · have haa := hodd0 a (by rw [h1122.1]; norm_num)
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
    have hab : componentQuotientMatrix G (secondOrderDefectGraph G) a b = 2 := by
      rw [h1122.1, h1122.2, hba, mul_one] at hbal
      omega
    exact false_of_degreeSix_oddEven_cover_eleven_twentyTwo
      G hfree hmin hcard hr a b h1122.1 h1122.2 haa hab
  · exact false_of_degreeSix_oddEven_cover_three_twelve
      G hfree hmin hcard u hu huRange huD hr hzero3
        a b h312.1 h312.2 hba
  · exact false_of_degreeSix_oddEven_cover_five_twenty
      G hfree hmin hcard hr hzero3 hzero5 a b h520.1 h520.2 hba
  · exact false_of_degreeSix_oddEven_cover_three_eighteen
      G hfree hmin hcard u hu huRange huD hr
        a b h318.1 h318.2 (hzero3 a h318.1) hba

/-- The full color-sector split reduces the degree-six boundary to the one
remaining empty-sector odd-diagonal theorem: the singleton branch is already
impossible, and the empty branch is consumed by the eight-cover assembly. -/
theorem false_of_degreeSix_boundary_of_empty_odd_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hemptyOdd0 : triangleFreeCycleSector G u = ∅ →
      ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        Odd c.supp.ncard →
          componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    False := by
  rcases degreeSix_triangleFreeCycleSector_empty_or_singleton
      G hfree hmin (by norm_num at hcard ⊢; exact hcard)
        u hu huRange huD hr with hempty | ⟨c, hsingleton, _⟩
  · exact false_of_degreeSix_of_odd_zero_diagonal
      G hfree hmin hcard u hu huRange huD hr (hemptyOdd0 hempty)
  · exact false_of_degreeSix_triangleFreeCycleSector_singleton
      G hfree hmin hcard u hu huRange huD hr c hsingleton

end

end Erdos85
