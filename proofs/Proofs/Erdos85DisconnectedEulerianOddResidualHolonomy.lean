import Proofs.Erdos85EulerianOddResidualHolonomy

/-!
# Odd residual holonomy without a global connectivity assumption

The active relay graph need not be connected.  Potentials can nevertheless
be integrated independently on every connected component, so the Eulerian
odd-price terminal is intrinsically componentwise.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A canonical (choice-based) root in the component of `v`. -/
def graphComponentRoot {V : Type*} (P : SimpleGraph V) (v : V) : V :=
  (P.connectedComponentMk v).out

theorem graphComponentRoot_mem {V : Type*} (P : SimpleGraph V) (v : V) :
    graphComponentRoot P v ∈ (P.connectedComponentMk v).supp :=
  (P.connectedComponentMk v).out_eq

/-- A chosen root-to-vertex walk within the component of `v`. -/
def chosenComponentWalk {V : Type*} (P : SimpleGraph V) (v : V) :
    P.Walk (graphComponentRoot P v) v := by
  apply Classical.choice
  apply ConnectedComponent.exact
  exact (P.connectedComponentMk v).out_eq

/-- If a symmetric F₂ edge price vanishes on every closed walk, it is a
vertex coboundary on an arbitrary graph, component by component. -/
theorem exists_vertexPotential_of_f2WalkWeight_closed_eq_zero_global
    {V : Type*} {P : SimpleGraph V} (k : V → V → ZMod 2)
    (hsymm : ∀ u v, k u v = k v u)
    (hclosed : ∀ {u} (p : P.Walk u u), f2WalkWeight k p = 0) :
    ∃ lam : V → ZMod 2, ∀ {u v}, P.Adj u v →
      k u v = lam u + lam v := by
  let lam : V → ZMod 2 := fun v => f2WalkWeight k (chosenComponentWalk P v)
  refine ⟨lam, ?_⟩
  intro u v huv
  have hcomp : P.connectedComponentMk u = P.connectedComponentMk v :=
    ConnectedComponent.connectedComponentMk_eq_of_adj huv
  have hroot : graphComponentRoot P u = graphComponentRoot P v := by
    simp only [graphComponentRoot]
    rw [hcomp]
  let p := chosenComponentWalk P u
  let q := (chosenComponentWalk P v).copy hroot.symm rfl
  have hq : f2WalkWeight k q = f2WalkWeight k p + k u v := by
    have h := f2WalkWeight_pathIndependent_of_closed_eq_zero
      k hsymm hclosed q (p.append huv.toWalk)
    simpa [q, p, f2WalkWeight_append] using h
  have hlu : lam u = f2WalkWeight k p := rfl
  have hlv : lam v = f2WalkWeight k q := by
    simp [lam, q, f2WalkWeight]
  have hadd := congrArg (fun z : ZMod 2 => f2WalkWeight k p + z) hq
  have hchar : (2 : ZMod 2) = 0 := by decide
  rw [← add_assoc, ← two_mul, hchar, zero_mul, zero_add] at hadd
  rw [hlu, hlv]
  exact hadd.symm

/-- Odd K-price in a finite even-valent graph forces odd holonomy, with no
connectivity hypothesis. -/
theorem exists_closedWalk_odd_graphEdgeIndicator_of_even_degree_of_odd_inf_global
    {V : Type*} [Fintype V] [DecidableEq V]
    (P K : SimpleGraph V) [DecidableRel P.Adj] [DecidableRel K.Adj]
    (heven : ∀ v, Even (P.degree v))
    (hodd : Odd ((P ⊓ K).edgeFinset.card)) :
    ∃ (u : V) (p : P.Walk u u),
      f2WalkWeight (graphEdgeIndicator K) p = 1 := by
  by_contra hno
  push_neg at hno
  have hzero : ∀ {u} (p : P.Walk u u),
      f2WalkWeight (graphEdgeIndicator K) p = 0 := by
    intro u p
    have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact (hbinary _).resolve_right (hno u p)
  obtain ⟨lam, hpotential⟩ :=
    exists_vertexPotential_of_f2WalkWeight_closed_eq_zero_global
      (graphEdgeIndicator K) (graphEdgeIndicator_symm K) hzero
  exact Nat.not_even_iff_odd.mpr hodd
    (even_card_inf_of_even_degree_of_graphEdgeIndicator_potential
      P K heven lam hpotential)

/-- Parity-free active-broken specialization with the artificial global
connectivity hypothesis removed. -/
theorem activeBrokenRelay_exists_closedWalk_odd_residual_global
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (x : V → ZMod 2)
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (hodd : Odd (((graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))) ⊓
      binaryTransportResidualGraph A hq hreg).edgeFinset.card)) :
    ∃ (u : V) (p : (graphF2SymmetricDifference
        (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed)
        (binaryVertexCutGraph (triangleFreeEdgeGraph A)
          (f2PotentialSupport x))).Walk u u),
      f2WalkWeight (graphEdgeIndicator
        (binaryTransportResidualGraph A hq hreg)) p = 1 := by
  apply exists_closedWalk_odd_graphEdgeIndicator_of_even_degree_of_odd_inf_global
  · exact activeBrokenRelay_cut_symmDiff_even_degree_of_evenRegular
      A hfree q hreg hq x mate hclosed hinvol hfixed
  · exact hodd

end

end Erdos85

#print axioms Erdos85.exists_vertexPotential_of_f2WalkWeight_closed_eq_zero_global
#print axioms Erdos85.exists_closedWalk_odd_graphEdgeIndicator_of_even_degree_of_odd_inf_global
#print axioms Erdos85.activeBrokenRelay_exists_closedWalk_odd_residual_global
