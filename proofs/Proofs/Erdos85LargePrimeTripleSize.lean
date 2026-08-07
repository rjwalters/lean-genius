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

end

end Erdos85
