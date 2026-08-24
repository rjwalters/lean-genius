import Proofs.Erdos85C4FreeWitnessPairingRelay
import Proofs.Erdos85BinaryCutGraphTwoPoleRoute

/-!
# Boundary of the active-witness relay

Restricting the paired-star relay to active witnesses produces one incident
relay edge for every active witness adjacent to a vertex.  Thus its degree
syndrome is exactly adjacency applied to the active-witness indicator.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The paired-star relay using only witnesses in `active`. -/
def activeWitnessRelayGraph
    {V : Type*} (A : SimpleGraph V) (active : V → Prop)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v) : SimpleGraph V :=
  witnessPairingRelayGraph
    (fun w v => active w ∧ A.Adj w v) mate
    (fun w v h => ⟨h.1, hclosed w v h.2⟩)
    (fun w v h => hinvol w v h.2)
    (fun w v h => hfixed w v h.2)

instance activeWitnessRelayGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v) :
    DecidableRel (activeWitnessRelayGraph A active mate
      hclosed hinvol hfixed).Adj := by
  dsimp only [activeWitnessRelayGraph]
  infer_instance

/-- Exact active-relay degree: the number of active witnesses adjacent to the
given endpoint. -/
theorem activeWitnessRelayGraph_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v) (v : V) :
    (activeWitnessRelayGraph A active mate hclosed hinvol hfixed).degree v =
      (Finset.univ.filter fun w => active w ∧ A.Adj w v).card := by
  apply witnessPairingRelayGraph_degree_eq_fiberCount
  intro u w w' hw hw' heq
  exact c4Free_neighborStar_mate_witness_unique A hfree mate hclosed hfixed
    u w w' hw.2 hw'.2 heq

/-- F2 form of the active-relay boundary identity `(73rnz_cjibbh)`: the
degree syndrome of the active relay is `A x`. -/
theorem activeWitnessRelayGraph_degree_cast_eq_adjMatrix_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (x : V → ZMod 2)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v) (v : V) :
    ((activeWitnessRelayGraph A (fun w => x w = 1) mate
      hclosed hinvol hfixed).degree v : ZMod 2) =
      (A.adjMatrix (ZMod 2)).mulVec x v := by
  rw [activeWitnessRelayGraph_degree_eq A hfree (fun w => x w = 1)
    mate hclosed hinvol hfixed v]
  rw [← f2Potential_neighborSupport_card_cast A x v]
  apply congrArg (fun s : Finset V => (s.card : ZMod 2))
  ext w
  simp [f2PotentialSupport, SimpleGraph.mem_neighborFinset, A.adj_comm,
    and_comm]

/-- The audit's broken-only relay `R_s`: only active witnesses and endpoints
joined to them by triangle-free edges participate. -/
def activeBrokenWitnessRelayGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (active : V → Prop) (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) : SimpleGraph V :=
  activeWitnessRelayGraph (triangleFreeEdgeGraph A) active mate
    hclosed hinvol hfixed

instance activeBrokenWitnessRelayGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) :
    DecidableRel (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).Adj := by
  dsimp only [activeBrokenWitnessRelayGraph]
  infer_instance

/-- Exact broken-relay degree: the number of active triangle-free witnesses
incident to the endpoint. -/
theorem activeBrokenWitnessRelayGraph_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) (v : V) :
    (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).degree v =
      (Finset.univ.filter fun w =>
        active w ∧ (triangleFreeEdgeGraph A).Adj w v).card := by
  have hsub : triangleFreeEdgeGraph A ≤ A := by
    intro u w huw
    exact ((mem_triangleFreeNeighbors A u w).mp huw).1
  have hfreeT : ¬ containsC4 V (triangleFreeEdgeGraph A) := by
    intro hc
    exact hfree (containsC4_mono hsub hc)
  exact activeWitnessRelayGraph_degree_eq (triangleFreeEdgeGraph A)
    hfreeT active mate hclosed hinvol hfixed v

/-- Correct broken-only form of `(73rnz_cjibbh)`: the F2 degree syndrome of
`R_s` is the triangle-free-edge adjacency action `T x`. -/
theorem activeBrokenWitnessRelayGraph_degree_cast_eq_adjMatrix_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (x : V → ZMod 2)
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) (v : V) :
    ((activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
      hclosed hinvol hfixed).degree v : ZMod 2) =
      ((triangleFreeEdgeGraph A).adjMatrix (ZMod 2)).mulVec x v := by
  have hsub : triangleFreeEdgeGraph A ≤ A := by
    intro u w huw
    exact ((mem_triangleFreeNeighbors A u w).mp huw).1
  have hfreeT : ¬ containsC4 V (triangleFreeEdgeGraph A) := by
    intro hc
    exact hfree (containsC4_mono hsub hc)
  exact activeWitnessRelayGraph_degree_cast_eq_adjMatrix_mulVec
    (triangleFreeEdgeGraph A) hfreeT x mate hclosed hinvol hfixed v

end

end Erdos85

#print axioms Erdos85.activeWitnessRelayGraph_degree_eq
#print axioms Erdos85.activeWitnessRelayGraph_degree_cast_eq_adjMatrix_mulVec
#print axioms Erdos85.activeBrokenWitnessRelayGraph_degree_eq
#print axioms Erdos85.activeBrokenWitnessRelayGraph_degree_cast_eq_adjMatrix_mulVec
