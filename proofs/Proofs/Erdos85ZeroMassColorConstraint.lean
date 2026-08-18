import Proofs.Erdos85ForwardSupportClassification
import Proofs.Erdos85CycleCoverColorRigidity

/-!
# Zero oriented mass forbids triangle-free-colored sector components

A triangle-free-colored defect component carries its rim inside `G`, is
therefore forward-oriented, and has diagonal quotient exactly two.  Its
contribution to the oriented anchor mass is positive, so a sector with
vanishing oriented mass contains no such component at all: **every
`p`-divisible component of a zero-mass sector is antipodal-colored.**

Composed with the nonsquare/nonresidue mass machinery this pins the
large-prime nonresidue branch to monochromatically antipodal-colored
sectors, where the antipodal incidence identities live.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Zero-mass sectors have no rimmed components.**  If the canonical
oriented anchor mass of the `p`-divisible sector vanishes, no
`p`-divisible component can carry its defect rim inside `G`. -/
theorem no_pDivisible_rim_component_of_orientedAnchorMass_eq_zero
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
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hzero : orientedAnchorMass G u (forwardOriented G u) p = 0)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hdvd : p ∣ c.supp.ncard) (hr3 : 3 ≤ c.supp.ncard)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (huTri : ∀ x, G.Adj (u c x) (u c (x + 1))) : False := by
  classical
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hfwd := cycleBlock_forward_of_contains_cycle_edges hr3
    G (secondOrderDefectGraph G) (u c) (hu c) huD hcomm huTri hfree
  have h2 := triangleFreeCycleComponent_diagonalQuotient_eq_two
    G hfree hd heven hmin hcard hr3 c (u c) (hu c) (huRange c) huD huTri
  have hbridge := card_graphCycleBlockZeroSupport_eq_componentQuotient
    G hfree hd heven hmin hcard c c (u c) (u c) (hu c) (huRange c)
    (huRange c)
  have hmem : c ∈ Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard ∧ forwardOriented G u c) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hdvd, hfwd⟩
  have hterm := (Finset.sum_eq_zero_iff.mp hzero) c hmem
  rw [hbridge, h2] at hterm
  exact two_ne_zero hterm

end

end Erdos85
