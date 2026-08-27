import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveThirdCubeSelectors

/-!
# Structural pruning for the adaptive `b1` third-level grid

The adaptive grid joins vertices `18` and `20` to members of the high-`1`
fiber `#[3,5,12,13,14,15,16,17]`.  Forty-eight of its 64 positive cubes
already contain a C4 using fixed support or pinned-matching edges.  This file
packages that finite calculation independently of any SAT solver.
-/

namespace Erdos85

/-- The graph vertices represented by each side of the adaptive grid. -/
def orderFortyNineThreeHighB1AdaptiveCandidates : Fin 8 → Fin 49
  | 0 => 3
  | 1 => 5
  | 2 => 12
  | 3 => 13
  | 4 => 14
  | 5 => 15
  | 6 => 16
  | 7 => 17

/-- Exactly the sixteen adaptive cubes not killed by a fixed C4. -/
def orderFortyNineThreeHighB1AdaptiveResidual (li ri : Fin 8) : Bool :=
  4 ≤ li.val && 2 ≤ ri.val && ri.val ≠ 3 && li ≠ ri

/-- Positive edges already forced by the support masks, the pinned `b1`
matchings, and the parent units.  Only the subset used by the C4 witnesses is
listed. -/
def orderFortyNineThreeHighB1AdaptiveFixedEdge (i j : Fin 49) : Bool :=
  let pairs : List (Nat × Nat) :=
    [(0, 3), (0, 4), (2, 3), (2, 4), (2, 5), (2, 13),
     (2, 18), (2, 19), (2, 20), (3, 4), (3, 12), (4, 18),
     (5, 13), (5, 19)]
  pairs.any fun ab =>
    (i.val = ab.1 && j.val = ab.2) ||
      (i.val = ab.2 && j.val = ab.1)

/-- Edges available in one adaptive positive cube: fixed edges plus its two
selector edges. -/
def orderFortyNineThreeHighB1AdaptiveAvailableEdge
    (li ri : Fin 8) (i j : Fin 49) : Bool :=
  orderFortyNineThreeHighB1AdaptiveFixedEdge i j ||
    ((i = 18 && j = orderFortyNineThreeHighB1AdaptiveCandidates li) ||
      (j = 18 && i = orderFortyNineThreeHighB1AdaptiveCandidates li)) ||
    ((i = 20 && j = orderFortyNineThreeHighB1AdaptiveCandidates ri) ||
      (j = 20 && i = orderFortyNineThreeHighB1AdaptiveCandidates ri))

abbrev OrderFortyNineAdaptiveC4Witness :=
  Fin 49 × Fin 49 × Fin 49 × Fin 49

/-- A concrete pair of endpoints and two distinct common neighbors for every
structurally dead cube. -/
def orderFortyNineThreeHighB1AdaptiveWitness
    (li ri : Fin 8) : Option OrderFortyNineAdaptiveC4Witness :=
  match li.val with
  | 0 => some (0, 18, 3, 4)
  | 1 => some (2, 5, 18, 19)
  | 2 => some (3, 18, 4, 12)
  | 3 => some (2, 13, 5, 18)
  | _ =>
    match ri.val with
    | 0 => some (2, 3, 4, 20)
    | 1 => some (2, 5, 19, 20)
    | 3 => some (2, 13, 5, 20)
    | _ => if li = ri then some (18, 20, 2,
        orderFortyNineThreeHighB1AdaptiveCandidates li) else none

set_option maxHeartbeats 2000000 in
/-- The witness table is complete and every returned quadruple consists of
two distinct endpoints, two distinct common neighbors, and four available
edges. -/
theorem orderFortyNineThreeHighB1AdaptiveWitness_complete
    (li ri : Fin 8)
    (hdead : orderFortyNineThreeHighB1AdaptiveResidual li ri = false) :
    ∃ i j w w',
      orderFortyNineThreeHighB1AdaptiveWitness li ri = some (i, j, w, w') ∧
      i ≠ j ∧ w ≠ w' ∧
      orderFortyNineThreeHighB1AdaptiveAvailableEdge li ri i w = true ∧
      orderFortyNineThreeHighB1AdaptiveAvailableEdge li ri j w = true ∧
      orderFortyNineThreeHighB1AdaptiveAvailableEdge li ri i w' = true ∧
      orderFortyNineThreeHighB1AdaptiveAvailableEdge li ri j w' = true := by
  fin_cases li <;> fin_cases ri
  all_goals simp [orderFortyNineThreeHighB1AdaptiveResidual] at hdead
  all_goals native_decide

/-- C4-freeness forces every realized adaptive cube into the explicit
sixteen-element residual set. -/
theorem orderFortyNineThreeHighB1AdaptiveResidual_of_c4Free
    (adj : Fin 49 → Fin 49 → Bool)
    (hcommon : ∀ i j : Fin 49, i ≠ j →
      (Finset.univ.filter fun k => adj i k && adj j k).card ≤ 1)
    (li ri : Fin 8)
    (hedges : ∀ i j,
      orderFortyNineThreeHighB1AdaptiveAvailableEdge li ri i j = true →
        adj i j = true) :
    orderFortyNineThreeHighB1AdaptiveResidual li ri = true := by
  by_contra hresidual
  have hdead : orderFortyNineThreeHighB1AdaptiveResidual li ri = false :=
    Bool.eq_false_of_not_eq_true hresidual
  obtain ⟨i, j, w, w', _, hij, hww', hiw, hjw, hiw', hjw'⟩ :=
    orderFortyNineThreeHighB1AdaptiveWitness_complete li ri hdead
  let common := Finset.univ.filter fun k => adj i k && adj j k
  have hw : w ∈ common := by simp [common, hedges i w hiw, hedges j w hjw]
  have hw' : w' ∈ common := by
    simp [common, hedges i w' hiw', hedges j w' hjw']
  exact hww' (Finset.card_le_one.mp (hcommon i j hij) w hw w' hw')

/-- Generator-facing count: structural pruning leaves exactly sixteen cubes. -/
theorem orderFortyNineThreeHighB1AdaptiveResidual_count :
    ((Finset.univ : Finset (Fin 8)).product Finset.univ |>.filter fun p =>
      orderFortyNineThreeHighB1AdaptiveResidual p.1 p.2).card = 16 := by
  native_decide

end Erdos85
