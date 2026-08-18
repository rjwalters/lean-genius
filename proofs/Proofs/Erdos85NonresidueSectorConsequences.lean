import Proofs.Erdos85CyclotomicSquareReduction
import Proofs.Erdos85MixedNonsquareMass
import Proofs.Erdos85QuotientSectorModP

/-!
# Consequences of a nonresidue prime sector

The cyclotomic reduction bridge and the quotient-sector determinant now use
the same quadratic character.  This file records the two graph-facing
consequences of `d-3` being a nonresidue modulo `p`: the selected component
count is even, while the frequency operator lies in its nonsquare branch and
forces divisibility of the selected anchor mass.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- At the exact second-order boundary, a nonresidue `d-3` modulo `p`
forces an even number of defect components whose orders are divisible by
`p`. -/
theorem even_pDivisible_filter_of_nonresidue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hnr : ¬IsSquare ((d - 3 : ℕ) : ZMod p)) :
    Even ((Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  exact hnr (isSquare_d_sub_three_mod_prime_of_odd_pDivisible_filter
    G hfree hd heven hmin hcard hp hodd)

variable {K : Type*} [Field K] [CharZero K]
variable {V C : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)]

/-- A nonresidue prime forces the cyclotomic nonsquare branch and hence
divides the total anchor mass of its divisible component sector. -/
theorem prime_dvd_pDivisibleAnchorMass_of_nonresidue
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d p : ℕ} (hd : 3 ≤ d)
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hodd : ∀ c : C, p ∣ ℓ c → Odd (ℓ c))
    (hp : p.Prime) (hp2 : 2 < p)
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hnr : ¬IsSquare ((d - 3 : ℕ) : ZMod p)) :
    p ∣ pDivisibleAnchorMass G u p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hns : ¬IsSquare ((d : K) - 1 - (ζ + ζ⁻¹)) :=
    not_isSquare_cyclotomic_frequencyScalar_of_nonresidue
      hζ (by omega) hd hnr
  exact prime_dvd_pDivisibleAnchorMass_of_nonsquare
    G D u hℓ3 hbij huD hcommZ hsqZ hodd hp hp2 hζ hns

end

end Erdos85
