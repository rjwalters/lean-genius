import Proofs.Erdos85MixedSquareTerminal
import Proofs.Erdos85AllSelectedSqueeze

/-!
# Primes above the degree force an even defect component

If a prime `p > d` (with `p ≥ 7`) divides one defect-component order it
divides all of them (sector closure).  Were every component length odd,
the odd boundary order would make the selected count odd — but the
unconditional selection obstruction forbids exactly that combination.
Hence **some defect component has even order**: the large-prime regime
is handed directly to the even-cycle orientation machinery.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Large primes force an even component.**  At the exact even
boundary, if a prime `p ≥ 7` with `p > d` divides some defect-component
order, then some defect component has even order. -/
theorem exists_even_component_of_largePrime_dvd
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
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard ∧ Even c.supp.ncard := by
  classical
  have hall := all_component_orders_dvd_of_largePrime_dvd_one
    G hfree hd heven hmin hcard hp hdp c₀ hpc
  by_contra hnone
  push_neg at hnone
  have hallOdd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard := fun c ↦
    Nat.not_even_iff_odd.mp (hnone c (hall c))
  have hcardVodd : Odd (Fintype.card V) := by
    rw [hcard]
    obtain ⟨k, hk⟩ := heven
    subst hk
    have h2 : (k + k) * (k + k - 1) = 2 * (k * (k + k - 1)) := by
      rw [← two_mul, mul_assoc]
    rw [Nat.odd_iff, h2]
    omega
  have hcountOdd := countOdd_of_all_pDivisible
    (secondOrderDefectGraph G) hall hallOdd hcardVodd
  have hobs := secondOrder_componentOrders_selectionObstructed
    G hfree hd heven hmin hcard
  rcases hobs p hp hp7 with ⟨c, hcdvd, hceven⟩ | hcount
  · exact hnone c hcdvd hceven
  · exact (Nat.not_even_iff_odd.mpr hcountOdd) hcount

end

end Erdos85
