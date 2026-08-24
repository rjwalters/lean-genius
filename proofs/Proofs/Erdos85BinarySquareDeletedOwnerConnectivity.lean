import Proofs.Erdos85DeletedOwnerShoreClassification

/-!
# Uniform deleted-owner connectivity at regular square order

The graph-facing punctured-shore classifier supplies two positive boundary
budgets totaling `q-1`.  The parametric cut lower bound reduces to the
residue product `r(q-r)`, which makes such a split impossible.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In every regular C4-free graph of square order, deleting any vertex from
the connected second-order defect graph leaves it connected. -/
theorem binarySquare_regular_deletedOwner_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : V)
    (hconnected : (secondOrderDefectGraph G).Connected)
    (hpuncturedNonempty :
      ((Finset.univ : Finset V).erase owner).Nonempty) :
    ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V).erase owner) : Set V)).Connected := by
  classical
  by_contra hnot
  obtain ⟨S, T, deltaS, deltaT, _hS, _hT, hunion, hdisj,
      _hSclosed, _hTclosed, _hdeltaS, _hdeltaT,
      hdeltaSpos, hdeltaTpos, hdeltasum, hcutS, hcutT⟩ :=
    binarySquare_regular_exists_punctured_shores_with_cutLower_budget
      G hfree hq hreg hcard owner hconnected hpuncturedNonempty hnot
  have hcards : S.card + T.card = q * q - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ owner),
      Finset.card_univ, hcard]
  have hcutS' : regularSquareCutLower q S.card ≤ deltaS := by
    simpa [regularSquareCutLower, nearRegularCutLower] using hcutS
  have hcutT' : regularSquareCutLower q T.card ≤ deltaT := by
    simpa [regularSquareCutLower, nearRegularCutLower] using hcutT
  exact false_of_regularSquare_positive_punctured_cut_split_of_cards
    q S.card T.card deltaS deltaT (by omega) hcards
      hdeltaSpos hdeltaTpos hdeltasum hcutS' hcutT'

#print axioms Erdos85.binarySquare_regular_deletedOwner_connected

end

end Erdos85
