import Proofs.Erdos85LargePrimeEvenMember
import Proofs.Erdos85ResidueSignedCount

/-!
# A three-cycle-length bound for primes above the degree

At the exact even boundary, a prime `p > d` dividing one defect-cycle order
divides every defect-cycle order.  The selection obstruction supplies an even
`p`-divisible component.  Since the total boundary order is odd, that component
cannot be the only component.  It has order at least `2p`, while any other
component has order at least `p`; hence `3p` is at most the boundary order.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Large-prime triple-size bound.**  A prime above the degree which occurs
in a defect-component order consumes at least three prime-length units in the
defect-cycle partition. -/
theorem three_mul_prime_le_boundary_of_largePrime_dvd_component_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p) (hdp : d < p)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc : p ∣ c₀.supp.ncard) :
    3 * p ≤ d * (d - 1) + 3 := by
  classical
  let D := secondOrderDefectGraph G
  have hall := all_component_orders_dvd_of_largePrime_dvd_one
    G hfree hd heven hmin hcard hp hdp c₀ hpc
  obtain ⟨c, hcp, hcEven⟩ := exists_even_component_of_largePrime_dvd
    G hfree hd heven hmin hcard hp hp7 hdp c₀ hpc
  have hparts : (∑ e : D.ConnectedComponent, e.supp.ncard) =
      d * (d - 1) + 3 := by
    rw [sum_connectedComponent_supp_ncard D, hcard]
  have htotalOdd : Odd (d * (d - 1) + 3) := by
    obtain ⟨k, hk⟩ := heven
    subst hk
    have h2 : (k + k) * (k + k - 1) =
        2 * (k * (k + k - 1)) := by
      rw [← two_mul, mul_assoc]
    rw [Nat.odd_iff, h2]
    omega
  have hne : ∃ e : D.ConnectedComponent, e ≠ c := by
    by_contra h
    push_neg at h
    have huniv : (Finset.univ : Finset D.ConnectedComponent) = {c} := by
      ext e
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact h e
    have heq : c.supp.ncard = d * (d - 1) + 3 := by
      rw [← hparts, huniv]
      simp
    exact (Nat.not_even_iff_odd.mpr htotalOdd) (heq ▸ hcEven)
  obtain ⟨e, hec⟩ := hne
  have hcpos : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
  obtain ⟨kc, hkc⟩ := hcp
  have hkcpos : 0 < kc := by
    by_contra hk
    have : kc = 0 := Nat.eq_zero_of_not_pos hk
    simp [hkc, this] at hcpos
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hkcne : kc ≠ 1 := by
    intro hk
    subst kc
    rw [mul_one] at hkc
    exact (Nat.not_even_iff_odd.mpr hpOdd) (hkc ▸ hcEven)
  have hcLower : 2 * p ≤ c.supp.ncard := by
    rw [hkc]
    simpa [mul_comm] using Nat.mul_le_mul_left p (show 2 ≤ kc by omega)
  have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
  have heLower : p ≤ e.supp.ncard := Nat.le_of_dvd hepos (hall e)
  have hpair : c.supp.ncard + e.supp.ncard ≤
      ∑ a : D.ConnectedComponent, a.supp.ncard := by
    calc
      c.supp.ncard + e.supp.ncard =
          ∑ a ∈ ({c, e} : Finset D.ConnectedComponent), a.supp.ncard := by
            simp [Ne.symm hec]
      _ ≤ ∑ a ∈ (Finset.univ : Finset D.ConnectedComponent),
          a.supp.ncard := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ a : D.ConnectedComponent, a.supp.ncard := by simp
  omega

/-- **Large-prime five-size bound.**  The apparent equality case of the
`3p` bound would leave precisely two components of orders `2p` and `p`.
The two-by-two quotient square equation rules this out for `p ≥ 7`, so in
fact five prime-length units are required. -/
theorem five_mul_prime_le_boundary_of_largePrime_dvd_component_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p) (hdp : d < p)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc : p ∣ c₀.supp.ncard) :
    5 * p ≤ d * (d - 1) + 3 := by
  classical
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let n := d * (d - 1) + 3
  have hthree : 3 * p ≤ n :=
    three_mul_prime_le_boundary_of_largePrime_dvd_component_order
      G hfree hd heven hmin hcard hp hp7 hdp c₀ hpc
  by_contra hfive
  have hnlt : n < 5 * p := by omega
  have hpdvdn : p ∣ n := by
    have := largePrime_dvd_card_of_dvd_component_order
      G hfree hd heven hmin hcard hp hdp c₀ hpc
    simpa [n, hcard] using this
  obtain ⟨k, hk⟩ := hpdvdn
  have hnOdd : Odd n := by
    dsimp [n]
    obtain ⟨j, hj⟩ := heven
    subst hj
    have h2 : (j + j) * (j + j - 1) =
        2 * (j * (j + j - 1)) := by
      rw [← two_mul, mul_assoc]
    rw [Nat.odd_iff, h2]
    omega
  have hk3 : k = 3 := by
    have hkBounds : 3 ≤ k ∧ k < 5 := by
      constructor
      · by_contra h
        have : k ≤ 2 := by omega
        rw [hk] at hthree
        have := Nat.mul_le_mul_left p this
        omega
      · by_contra h
        have : 5 ≤ k := by omega
        rw [hk] at hnlt
        have := Nat.mul_le_mul_left p this
        omega
    have hk4 : k ≠ 4 := by
      intro h4
      subst k
      have hnEven : Even n := by
        refine ⟨2 * p, ?_⟩
        rw [hk]
        omega
      exact (Nat.not_even_iff_odd.mpr hnOdd) hnEven
    omega
  have hn3 : n = 3 * p := by rw [hk, hk3]; omega
  have hall := all_component_orders_dvd_of_largePrime_dvd_one
    G hfree hd heven hmin hcard hp hdp c₀ hpc
  obtain ⟨c, hcp, hcEven⟩ := exists_even_component_of_largePrime_dvd
    G hfree hd heven hmin hcard hp hp7 hdp c₀ hpc
  have hparts : (∑ x : D.ConnectedComponent, x.supp.ncard) = n := by
    rw [sum_connectedComponent_supp_ncard D, hcard]
  obtain ⟨kc, hkc⟩ := hcp
  have hkcpos : 0 < kc := by
    have hcpos := c.nonempty_supp.ncard_pos
    by_contra h
    have : kc = 0 := Nat.eq_zero_of_not_pos h
    simp [hkc, this] at hcpos
  have hcle : c.supp.ncard ≤ n := by
    rw [← hparts]
    exact Finset.single_le_sum (f := fun x : D.ConnectedComponent ↦
      x.supp.ncard) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ c)
  have hkcLe : kc ≤ 3 := by
    rw [hkc, hn3] at hcle
    have hcancel : p * kc ≤ p * 3 := by simpa [mul_comm] using hcle
    exact Nat.le_of_mul_le_mul_left hcancel hp.pos
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hkc1 : kc ≠ 1 := by
    intro h1
    subst kc
    rw [mul_one] at hkc
    exact (Nat.not_even_iff_odd.mpr hpOdd) (hkc ▸ hcEven)
  have hkc3ne : kc ≠ 3 := by
    intro h3
    subst kc
    have hodd3 : Odd (p * 3) := hpOdd.mul (by decide)
    exact (Nat.not_even_iff_odd.mpr hodd3) (hkc ▸ hcEven)
  have hkc2 : kc = 2 := by omega
  have hcLen : c.supp.ncard = 2 * p := by rw [hkc, hkc2, mul_comm]
  have hne : ∃ e : D.ConnectedComponent, e ≠ c := by
    by_contra h
    push_neg at h
    have huniv : (Finset.univ : Finset D.ConnectedComponent) = {c} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact h x
    rw [huniv] at hparts
    simp [hcLen, hn3] at hparts
    exact hp.ne_zero hparts
  obtain ⟨e, hec⟩ := hne
  have hepos := e.nonempty_supp.ncard_pos
  have hep : p ≤ e.supp.ncard := Nat.le_of_dvd hepos (hall e)
  have hpair : c.supp.ncard + e.supp.ncard ≤ n := by
    rw [← hparts]
    calc
      c.supp.ncard + e.supp.ncard =
          ∑ x ∈ ({c, e} : Finset D.ConnectedComponent), x.supp.ncard := by
            simp [Ne.symm hec]
      _ ≤ ∑ x ∈ (Finset.univ : Finset D.ConnectedComponent),
          x.supp.ncard := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ x : D.ConnectedComponent, x.supp.ncard := by simp
  have heLen : e.supp.ncard = p := by omega
  have huniv : (Finset.univ : Finset D.ConnectedComponent) = {c, e} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    by_contra hx
    push_neg at hx
    have hxpos := x.nonempty_supp.ncard_pos
    have hxp : p ≤ x.supp.ncard := Nat.le_of_dvd hxpos (hall x)
    have htriple : c.supp.ncard + e.supp.ncard + x.supp.ncard ≤ n := by
      rw [← hparts]
      calc
        c.supp.ncard + e.supp.ncard + x.supp.ncard =
            ∑ a ∈ ({c, e, x} : Finset D.ConnectedComponent),
              a.supp.ncard := by
                simp [Ne.symm hec, Ne.symm hx.1, Ne.symm hx.2]
                exact Nat.add_assoc _ _ _
        _ ≤ ∑ a ∈ (Finset.univ : Finset D.ConnectedComponent),
            a.supp.ncard := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = ∑ a : D.ConnectedComponent, a.supp.ncard := by simp
    omega
  have hrowc := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard c
  have hrowe := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard e
  change (∑ x, Q c x) = d at hrowc
  change (∑ x, Q e x) = d at hrowe
  rw [huniv] at hrowc hrowe
  simp [Ne.symm hec] at hrowc hrowe
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  change c.supp.ncard * Q c e = e.supp.ncard * Q e c at hbal
  rw [hcLen, heLen] at hbal
  have hp0 : 0 < p := hp.pos
  have hratio : 2 * Q c e = Q e c := by
    apply Nat.eq_of_mul_eq_mul_left hp0
    nlinarith [hbal]
  have hsq := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard c e
  change (Q * Q) c e = (d - 3) * (if c = e then 1 else 0) +
    e.supp.ncard at hsq
  rw [Matrix.mul_apply, huniv, heLen] at hsq
  simp [Ne.symm hec] at hsq
  have hprod : Q c e * (Q c c + Q e e) = p := by
    nlinarith
  have hbDvd : Q c e ∣ p := ⟨Q c c + Q e e, hprod.symm⟩
  rcases hp.eq_one_or_self_of_dvd (Q c e) hbDvd with hb1 | hbp
  · simp [hb1] at hprod
    have hpEq : p = 2 * d - 3 := by omega
    have hnEq : d * (d - 1) + 3 = 3 * p := by simpa [n] using hn3
    have hdPred : d - 1 + 1 = d := by omega
    have hpAdd : p + 3 = 2 * d := by omega
    have hdle : d ≤ 4 := by
      by_contra h
      have hd5 : 5 ≤ d := by omega
      nlinarith only [hnEq, hpAdd, hdPred, hd5]
    omega
  · have hbLe : Q c e ≤ d := by omega
    omega

end

end Erdos85
