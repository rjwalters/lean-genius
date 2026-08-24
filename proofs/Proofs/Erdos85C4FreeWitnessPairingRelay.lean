import Proofs.Erdos85C4FreeCommonNeighborUnique
import Proofs.Erdos85WitnessPairingRelayGraph

/-!
# C4-free regular stars produce an Eulerian witness relay

This specializes the witness-indexed relay construction to the actual
geometric situation: witnesses and endpoints are vertices of one C4-free
regular graph, and the eligible fiber at `w` is its neighbor star.  C4
freeness supplies uniqueness of the witness label on every paired edge;
regularity supplies the exact relay degree.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Paired edges in neighbor stars of a C4-free graph have unique witness
labels. -/
theorem c4Free_neighborStar_mate_witness_unique
    {V : Type*} (A : SimpleGraph V)
    (hfree : ¬ containsC4 V A) (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v) :
    ∀ v w w', A.Adj w v → A.Adj w' v →
      mate w v = mate w' v → w = w' := by
  intro v w w' hwv hw'v hmate
  apply commonNeighbor_unique_of_c4Free hfree
    (hfixed w v hwv).symm
  · exact hwv.symm
  · exact hclosed w v hwv |>.symm
  · exact hw'v.symm
  · rw [hmate]
    exact hclosed w' v hw'v |>.symm

/-- The witness fiber through `v` is its ordinary neighbor finset, hence has
cardinality `degree A v`. -/
theorem neighborStar_witnessFiber_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (v : V) :
    (Finset.univ.filter fun w => A.Adj w v).card = A.degree v := by
  rw [← A.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborFinset, A.adj_comm]

/-- A fixed-point-free involution on every neighbor star of a C4-free
`q`-regular graph generates a `q`-regular relay graph. -/
theorem c4Free_neighborStar_relay_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (q : ℕ) (hreg : ∀ v, A.degree v = q) (v : V) :
    (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).degree v = q := by
  apply witnessPairingRelayGraph_degree_eq A.Adj mate hclosed hinvol hfixed
    (c4Free_neighborStar_mate_witness_unique A hfree mate hclosed hfixed) q
  intro u
  rw [neighborStar_witnessFiber_card, hreg]

/-- For even `q`, the actual neighbor-star relay graph is Eulerian. -/
theorem c4Free_neighborStar_relay_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (q : ℕ) (hreg : ∀ v, A.degree v = q) (hq : Even q) (v : V) :
    Even ((witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).degree v) := by
  rw [c4Free_neighborStar_relay_degree_eq A hfree mate hclosed hinvol hfixed q hreg]
  exact hq

end

end Erdos85

#print axioms Erdos85.c4Free_neighborStar_mate_witness_unique
#print axioms Erdos85.c4Free_neighborStar_relay_degree_eq
#print axioms Erdos85.c4Free_neighborStar_relay_even_degree
