import Proofs.Erdos85FiveBoundaryNonsquare
import Proofs.Erdos85MixedSectorMassQuotient
import Proofs.Erdos85BoundaryQuotientDivisibility
import Proofs.Erdos85GlobalCycleFactorization

/-!
# Excluding the three-component partition at a five-prime boundary

When the component orders are `p, 2p, 2p`, unequal-cycle rigidity bounds the
two quotient entries from a long cycle to the short cycle by one.  The
nonsquare quotient trace makes their sum even, and the square equation makes
it nonzero.  Thus both entries are one; the remaining equations force the
tiny degrees `4` or `7`.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

set_option maxHeartbeats 800000 in
/-- The only possible three-component order partition of a five-prime
boundary is incompatible with the quotient equations. -/
theorem false_of_fivePrime_threeComponent_orders
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (hfive : d * (d - 1) + 3 = 5 * p)
    (e c f : (secondOrderDefectGraph G).ConnectedComponent)
    (hec : e ≠ c) (hef : e ≠ f) (hcf : c ≠ f)
    (huniv : (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent) = {e, c, f})
    (heLen : e.supp.ncard = p)
    (hcLen : c.supp.ncard = 2 * p)
    (hfLen : f.supp.ncard = 2 * p) : False := by
  classical
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hnonsquare : ¬ IsSquare (d - 3) :=
    not_isSquare_d_sub_three_of_boundary_eq_five_mul_prime
      hd heven hp hp7 hfive
  have htrace := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree hd heven hmin hcard hnonsquare
  change (∑ x, Q x x) = d at htrace
  rw [huniv] at htrace
  simp [hec, hef, hcf] at htrace
  have hrowe := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard e
  have hrowc := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard c
  have hrowf := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard f
  change (∑ x, Q e x) = d at hrowe
  change (∑ x, Q c x) = d at hrowc
  change (∑ x, Q f x) = d at hrowf
  rw [huniv] at hrowe hrowc hrowf
  simp [hec, hef, hcf] at hrowe hrowc hrowf
  have hnotCE : ¬ c.supp.ncard ∣ e.supp.ncard := by
    rw [hcLen, heLen]
    intro h
    have := Nat.le_of_dvd hp.pos h
    omega
  have hnotFE : ¬ f.supp.ncard ∣ e.supp.ncard := by
    rw [hfLen, heLen]
    intro h
    have := Nat.le_of_dvd hp.pos h
    omega
  have hxLe : Q c e ≤ 1 :=
    secondOrder_componentQuotientMatrix_le_one_of_not_dvd
      G hfree hd heven hmin hcard c e hnotCE
  have hyLe : Q f e ≤ 1 :=
    secondOrder_componentQuotientMatrix_le_one_of_not_dvd
      G hfree hd heven hmin hcard f e hnotFE
  have hbalEC := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard e c
  have hbalEF := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard e f
  have hbalCF := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c f
  change e.supp.ncard * Q e c = c.supp.ncard * Q c e at hbalEC
  change e.supp.ncard * Q e f = f.supp.ncard * Q f e at hbalEF
  change c.supp.ncard * Q c f = f.supp.ncard * Q f c at hbalCF
  rw [heLen, hcLen] at hbalEC
  rw [heLen, hfLen] at hbalEF
  rw [hcLen, hfLen] at hbalCF
  have hp0 : 0 < p := hp.pos
  have hEC : Q e c = 2 * Q c e := by
    apply Nat.eq_of_mul_eq_mul_left hp0
    nlinarith [hbalEC]
  have hEF : Q e f = 2 * Q f e := by
    apply Nat.eq_of_mul_eq_mul_left hp0
    nlinarith [hbalEF]
  have hCF : Q c f = Q f c := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 * p by omega)
    exact hbalCF
  have hxyEven : Even (Q c e + Q f e) := by
    refine ⟨d - Q c f - (Q c e + Q f e), ?_⟩
    omega
  have hxyEq : Q c e = Q f e := by
    obtain ⟨k, hk⟩ := hxyEven
    omega
  have hxyPos : 0 < Q c e + Q f e := by
    by_contra h
    have hx0 : Q c e = 0 := by omega
    have hy0 : Q f e = 0 := by omega
    have hsq := secondOrder_componentQuotientMatrix_sq_apply
      G hfree hd heven hmin hcard e c
    change (Q * Q) e c = (d - 3) * (if e = c then 1 else 0) +
      c.supp.ncard at hsq
    rw [Matrix.mul_apply, huniv, hcLen] at hsq
    simp [hec, hef, hcf] at hsq
    rw [hEC, hEF, hx0, hy0] at hsq
    simp at hsq
    omega
  have hx1 : Q c e = 1 := by omega
  have hy1 : Q f e = 1 := by omega
  have hQee : Q e e = d - 4 := by
    rw [hEC, hEF, hx1, hy1] at hrowe
    omega
  have hdiag := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard e e
  change (Q * Q) e e = (d - 3) * (if e = e then 1 else 0) +
    e.supp.ncard at hdiag
  rw [Matrix.mul_apply, huniv, heLen] at hdiag
  simp [hec, hef, hcf] at hdiag
  rw [hEC, hEF, hx1, hy1] at hdiag
  norm_num at hdiag
  have hpFormula : (d - 4) * (d - 4) + 4 = d - 3 + p := by
    simpa [hQee] using hdiag
  have hdle : d ≤ 7 := by
    by_contra h
    have hd8 : 8 ≤ d := by omega
    let a := d - 4
    have hdA : d = a + 4 := by dsimp [a]; omega
    have ha4 : 4 ≤ a := by omega
    rw [hdA] at hfive hpFormula
    norm_num at hfive hpFormula
    have hpFormulaA : a * a + 4 = a + 1 + p := by omega
    nlinarith only [hfive, hpFormulaA, ha4]
  obtain ⟨j, hj⟩ := heven
  interval_cases d <;> omega

set_option maxHeartbeats 800000 in
/-- **Large-prime seven-size bound.**  A prime above the degree occurring in
a defect-cycle order consumes at least seven prime-length units.  The only
new equality band after the `5p` theorem would have total order `5p`; oddness
of the global component count forces the partition `(p, 2p, 2p)`, which the
three-component terminal excludes. -/
theorem seven_mul_prime_le_boundary_of_largePrime_dvd_component_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [hfin : Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p) (hdp : d < p)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc₀ : p ∣ c₀.supp.ncard) :
    7 * p ≤ d * (d - 1) + 3 := by
  classical
  let D := secondOrderDefectGraph G
  let n := d * (d - 1) + 3
  have hfiveLower : 5 * p ≤ n :=
    five_mul_prime_le_boundary_of_largePrime_dvd_component_order
      G hfree hd heven hmin hcard hp hp7 hdp c₀ hpc₀
  by_contra hseven
  have hnlt : n < 7 * p := by omega
  have hpdvdn : p ∣ n := by
    have h := largePrime_dvd_card_of_dvd_component_order
      G hfree hd heven hmin hcard hp hdp c₀ hpc₀
    simpa [n, hcard] using h
  obtain ⟨k, hk⟩ := hpdvdn
  have hnOdd : Odd n := by
    dsimp [n]
    obtain ⟨j, hj⟩ := heven
    subst hj
    have h2 : (j + j) * (j + j - 1) =
        2 * (j * (j + j - 1)) := by rw [← two_mul, mul_assoc]
    rw [Nat.odd_iff, h2]
    omega
  have hk5 : k = 5 := by
    have hkBounds : 5 ≤ k ∧ k < 7 := by
      constructor
      · by_contra h
        have hk4 : k ≤ 4 := by omega
        rw [hk] at hfiveLower
        have := Nat.mul_le_mul_left p hk4
        omega
      · by_contra h
        have hk7 : 7 ≤ k := by omega
        rw [hk] at hnlt
        have := Nat.mul_le_mul_left p hk7
        omega
    have hk6 : k ≠ 6 := by
      intro h6
      subst k
      have hnEven : Even n := by
        refine ⟨3 * p, ?_⟩
        rw [hk]
        omega
      exact (Nat.not_even_iff_odd.mpr hnOdd) hnEven
    omega
  have hn5 : n = 5 * p := by rw [hk, hk5]; omega
  have hall := all_component_orders_dvd_of_largePrime_dvd_one
    G hfree hd heven hmin hcard hp hdp c₀ hpc₀
  obtain ⟨c, hcp, hcEven⟩ := exists_even_component_of_largePrime_dvd
    G hfree hd heven hmin hcard hp hp7 hdp c₀ hpc₀
  have hparts : (∑ x : D.ConnectedComponent, x.supp.ncard) = n := by
    rw [sum_connectedComponent_supp_ncard D, hcard]
  have hcountLe : Fintype.card D.ConnectedComponent ≤ 5 := by
    have hbound : p * Fintype.card D.ConnectedComponent ≤
        ∑ x : D.ConnectedComponent, x.supp.ncard := by
      calc
        p * Fintype.card D.ConnectedComponent =
            ∑ _x : D.ConnectedComponent, p := by
              simp [Finset.sum_const, Finset.card_univ, mul_comm]
        _ ≤ ∑ x : D.ConnectedComponent, x.supp.ncard := by
          apply Finset.sum_le_sum
          intro x hx
          exact Nat.le_of_dvd x.nonempty_supp.ncard_pos (hall x)
    rw [hparts, hn5] at hbound
    have hcancel : p * Fintype.card D.ConnectedComponent ≤ p * 5 := by
      simpa [mul_comm] using hbound
    exact Nat.le_of_mul_le_mul_left hcancel hp.pos
  have hcountRaw : Odd (@Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent
      (secondOrderDefectGraph G).instFintypeConnectedComponent) := by
    letI : Fintype (secondOrderDefectGraph G).ConnectedComponent :=
      (secondOrderDefectGraph G).instFintypeConnectedComponent
    exact secondOrderDefect_component_count_odd G hfree hd heven hmin hcard
  have hcardInstances : @Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent hfin =
      @Fintype.card (secondOrderDefectGraph G).ConnectedComponent
        (secondOrderDefectGraph G).instFintypeConnectedComponent :=
    @Fintype.card_congr _ _ hfin
      (secondOrderDefectGraph G).instFintypeConnectedComponent (Equiv.refl _)
  have hcountOdd : Odd (Fintype.card D.ConnectedComponent) := by
    change Odd (@Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent hfin)
    rw [hcardInstances]
    exact hcountRaw
  have hcountNeOne : Fintype.card D.ConnectedComponent ≠ 1 := by
    intro hcount1
    have hunivCard : (Finset.univ : Finset D.ConnectedComponent).card = 1 := by
      rw [Finset.card_univ, hcount1]
    obtain ⟨x, hunivX⟩ := Finset.card_eq_one.mp hunivCard
    have hcx : c = x := by
      have : c ∈ ({x} : Finset D.ConnectedComponent) := by
        rw [← hunivX]
        exact Finset.mem_univ c
      simpa using this
    subst x
    rw [hunivX] at hparts
    simp [hn5] at hparts
    have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
    have hn5Odd : Odd (5 * p) := (by decide : Odd 5).mul hpOdd
    exact (Nat.not_even_iff_odd.mpr hn5Odd) (hparts ▸ hcEven)
  have hcountNeFive : Fintype.card D.ConnectedComponent ≠ 5 := by
    intro hcount5
    have hsumSat : (∑ x : D.ConnectedComponent, x.supp.ncard) =
        p * Fintype.card D.ConnectedComponent := by
      rw [hparts, hn5, hcount5]
      simp [mul_comm]
    have hallEq := all_orders_eq_of_card_mul_eq_sum D hall hsumSat
    have hcEq : c.supp.ncard = p := hallEq c
    have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
    exact (Nat.not_even_iff_odd.mpr hpOdd) (hcEq ▸ hcEven)
  have hcount3 : Fintype.card D.ConnectedComponent = 3 := by
    obtain ⟨q, hq⟩ := hcountOdd
    omega
  have hcMem : c ∈ (Finset.univ : Finset D.ConnectedComponent) :=
    Finset.mem_univ c
  have heraseCard : ((Finset.univ : Finset D.ConnectedComponent).erase c).card = 2 := by
    rw [Finset.card_erase_of_mem hcMem, Finset.card_univ, hcount3]
  obtain ⟨e, f, hef, herase⟩ := Finset.card_eq_two.mp heraseCard
  have hec : e ≠ c := by
    have : e ∈ (Finset.univ : Finset D.ConnectedComponent).erase c := by
      rw [herase]
      simp
    exact (Finset.mem_erase.mp this).1
  have hfc : f ≠ c := by
    have : f ∈ (Finset.univ : Finset D.ConnectedComponent).erase c := by
      rw [herase]
      simp
    exact (Finset.mem_erase.mp this).1
  have huniv : (Finset.univ : Finset D.ConnectedComponent) = {c, e, f} := by
    rw [← Finset.insert_erase hcMem, herase]
  have hepos := e.nonempty_supp.ncard_pos
  have hfpos := f.nonempty_supp.ncard_pos
  obtain ⟨kc, hkc⟩ := hcp
  obtain ⟨ke, hke⟩ := hall e
  obtain ⟨kf, hkf⟩ := hall f
  have hkepos : 0 < ke := by
    by_contra h
    have : ke = 0 := Nat.eq_zero_of_not_pos h
    simp [hke, this] at hepos
  have hkfpos : 0 < kf := by
    by_contra h
    have : kf = 0 := Nat.eq_zero_of_not_pos h
    simp [hkf, this] at hfpos
  have hkcpos : 0 < kc := by
    have hcpos := c.nonempty_supp.ncard_pos
    by_contra h
    have : kc = 0 := Nat.eq_zero_of_not_pos h
    simp [hkc, this] at hcpos
  have hcoeff : kc + ke + kf = 5 := by
    rw [huniv] at hparts
    simp [Ne.symm hec, Ne.symm hfc, hef] at hparts
    rw [hkc, hke, hkf, hn5] at hparts
    have hp0 := hp.pos
    nlinarith
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hkc1 : kc ≠ 1 := by
    intro h1
    subst kc
    rw [mul_one] at hkc
    exact (Nat.not_even_iff_odd.mpr hpOdd) (hkc ▸ hcEven)
  have hkc3 : kc ≠ 3 := by
    intro h3
    subst kc
    have : Odd (p * 3) := hpOdd.mul (by decide)
    exact (Nat.not_even_iff_odd.mpr this) (hkc ▸ hcEven)
  have hkc2 : kc = 2 := by
    have hkcLe : kc ≤ 3 := by omega
    omega
  have hcLen : c.supp.ncard = 2 * p := by rw [hkc, hkc2, mul_comm]
  have hkef : ke + kf = 3 := by omega
  by_cases hke1 : ke = 1
  · have hkf2 : kf = 2 := by omega
    have heLen : e.supp.ncard = p := by rw [hke, hke1, mul_one]
    have hfLen : f.supp.ncard = 2 * p := by rw [hkf, hkf2, mul_comm]
    apply false_of_fivePrime_threeComponent_orders G hfree hd heven hmin
      hcard hp hp7 (by simpa [n] using hn5) e c f hec
      (hef) (Ne.symm hfc)
    · rw [huniv]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact heLen
    · exact hcLen
    · exact hfLen
  · have hke2eq : ke = 2 := by omega
    have hkf1 : kf = 1 := by omega
    have hfLen : f.supp.ncard = p := by rw [hkf, hkf1, mul_one]
    have heLen : e.supp.ncard = 2 * p := by rw [hke, hke2eq, mul_comm]
    apply false_of_fivePrime_threeComponent_orders G hfree hd heven hmin
      hcard hp hp7 (by simpa [n] using hn5) f c e hfc
      (Ne.symm hef) (Ne.symm hec)
    · rw [huniv]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact hfLen
    · exact hcLen
    · exact heLen

end

end Erdos85
