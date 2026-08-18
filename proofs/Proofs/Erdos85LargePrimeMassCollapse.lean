import Proofs.Erdos85ResidueSignedCount
import Proofs.Erdos85MixedDiagonalDichotomy

/-!
# Large primes collapse the sector-mass gap

The sector-mass gap says that under `hodd` a prime dividing the
`p`-divisible anchor mass forces `mass = 0` or `mass ≥ 2p`.  But the mass
is a sum of diagonal quotient entries `Q(c,c) ∈ {0,2}` over the sector,
so `mass ≤ 2·|Sₚ|`, and for `p² > d(d-1)+3` the sector has fewer than
`p` members.  The upper alternative is impossible: **for large primes,
divisibility of the mass means the mass vanishes identically.**

Composed with the nonresidue package
(`prime_dvd_pDivisibleAnchorMass_of_nonresidue`), every prime
`p > √(d(d-1)+3)` with `(d-3 | p) = -1` dividing some defect component
order has an entirely diagonal-free sector; the signed-count obstruction
(`Erdos85ResidueSignedCount`) shows the residue case with odd sector
count behaves in the opposite way — its mass is strictly positive.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Large-prime mass collapse.**  Under `hodd`, an odd prime `p` with
`p² > d(d-1)+3` dividing the selected anchor mass forces the mass to
vanish: the gap alternative `mass ≥ 2p` would need at least `p` diagonal
sector components of order at least `p` each, exceeding the vertex
count. -/
theorem pDivisibleAnchorMass_eq_zero_of_dvd_of_large_prime
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hpOdd : Odd p) (hbig : d * (d - 1) + 3 < p * p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (hdvdMass : p ∣ pDivisibleAnchorMass G u p) :
    pDivisibleAnchorMass G u p = 0 := by
  rcases pDivisibleAnchorMass_eq_zero_or_ge_two_mul G hfree hd heven hmin
    hcard hpOdd u hu huRange huD hℓ3 hodd hdvdMass with h0 | hge
  · exact h0
  · exfalso
    have hsmall := pDivisible_filter_card_lt_of_card_lt_sq
      (secondOrderDefectGraph G) (p := p) hcard hbig
    have hbound : pDivisibleAnchorMass G u p ≤
        2 * (Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard)).card := by
      rw [pDivisibleAnchorMass_eq_sum_diagonalQuotient G hfree hd heven
        hmin hcard u hu huRange]
      calc
        (∑ c ∈ Finset.univ.filter (fun c :
            (secondOrderDefectGraph G).ConnectedComponent ↦
              p ∣ c.supp.ncard),
            componentQuotientMatrix G (secondOrderDefectGraph G) c c) ≤
            ∑ _c ∈ Finset.univ.filter (fun c :
              (secondOrderDefectGraph G).ConnectedComponent ↦
                p ∣ c.supp.ncard), 2 := by
          apply Finset.sum_le_sum
          intro c hc
          rcases oddComponent_diagonalQuotient_eq_zero_or_two G hfree hd
            heven hmin hcard (hℓ3 c)
            (hodd c (Finset.mem_filter.mp hc).2) c (u c) (hu c)
            (huRange c) (huD c) with h | h <;> omega
        _ = 2 * (Finset.univ.filter (fun c :
            (secondOrderDefectGraph G).ConnectedComponent ↦
              p ∣ c.supp.ncard)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega

end

end Erdos85
