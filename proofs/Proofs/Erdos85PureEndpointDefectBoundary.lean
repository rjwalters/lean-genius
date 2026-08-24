import Proofs.Erdos85PureEndpointFinalLayerPrivateMatching

/-!
# Exact defect boundary at the pure endpoint

At the saturated pure endpoint the exceptional centers contain no internal
second-order-defect edge.  Since the defect graph is `(q-1)`-regular, every
one of those defect edges exits the exceptional family.  This records the
result in the component-facing form used by the remaining B.3 analysis.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every pure-endpoint center has all `q-1` of its defect neighbors outside
the exceptional family, and the oriented defect boundary has mass
`q(q-1)`. -/
theorem c4Free_binarySquare_pureEndpoint_defectBoundary_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    (∀ i ∈ fullLineCenters G S q,
      ((secondOrderDefectGraph G).neighborFinset i ∩
        (fullLineCenters G S q)ᶜ).card = q - 1) ∧
    (∑ i ∈ fullLineCenters G S q,
      ((secondOrderDefectGraph G).neighborFinset i ∩
        (fullLineCenters G S q)ᶜ).card) = q * (q - 1) := by
  let C := fullLineCenters G S q
  let D := secondOrderDefectGraph G
  have hstructure :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_structure
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hindependent : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → ¬D.Adj i j := by
    simpa [C, D] using hstructure.1
  have hDdeg : ∀ i, D.degree i = q - 1 := by
    intro i
    exact binarySquare_regular_secondOrderDefect_degree_eq
      G hfree (by omega) hreg hcard i
  have hlocal : ∀ i ∈ C,
      (D.neighborFinset i ∩ Cᶜ).card = q - 1 := by
    intro i hi
    have hinternal : (D.neighborFinset i ∩ C).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨j, hj⟩
      have hji : j ≠ i := by
        intro hji
        subst j
        exact D.loopless.irrefl i
          ((D.mem_neighborFinset i i).mp (Finset.mem_inter.mp hj).1)
      exact hindependent i hi j (Finset.mem_inter.mp hj).2 hji.symm
        ((D.mem_neighborFinset i j).mp (Finset.mem_inter.mp hj).1)
    have hcomp := neighbor_inter_complement_card D C i
    rw [hDdeg i, hinternal, Nat.sub_zero] at hcomp
    exact hcomp
  constructor
  · simpa [C, D] using hlocal
  · change (∑ i ∈ C, (D.neighborFinset i ∩ Cᶜ).card) = _
    calc
      (∑ i ∈ C, (D.neighborFinset i ∩ Cᶜ).card) =
          ∑ _i ∈ C, (q - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hlocal i hi
      _ = C.card * (q - 1) := by simp
      _ = q * (q - 1) := by rw [show C.card = q by simpa [C] using hCcard]

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_defectBoundary_eq
