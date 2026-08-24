import Proofs.Erdos85ActiveBrokenRelayResidualPrice

/-!
# Canonical witness labels on active broken-relay edges

Pointwise uniqueness promotes to an honest label function on the finite edge
set of `R_s`.  This is the API needed to partition residual-price sums into
the local witness contributions `Theta_w`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Predicate saying that `w` is the active broken-star witness of the
unordered relay edge `e`. -/
def IsActiveBrokenRelayEdgeWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (active : V → Prop) (w : V) (e : Sym2 V) : Prop :=
  active w ∧ ∀ v ∈ e.toFinset, (triangleFreeEdgeGraph A).Adj w v

/-- Every finite active broken-relay edge has a unique unordered witness
label. -/
theorem activeBrokenRelay_edge_existsUnique_witness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (e : (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).edgeFinset) :
    ∃! w, IsActiveBrokenRelayEdgeWitness A active w e.1 := by
  generalize heq : e.1 = z
  induction z using Sym2.inductionOn with
  | _ x y =>
      have hR : (activeBrokenWitnessRelayGraph A active mate
          hclosed hinvol hfixed).Adj x y := by
        have he : s(x, y) ∈ (activeBrokenWitnessRelayGraph A active mate
            hclosed hinvol hfixed).edgeSet := by
          have he' : e.1 ∈ (activeBrokenWitnessRelayGraph A active mate
              hclosed hinvol hfixed).edgeSet := by
            simpa only [SimpleGraph.mem_edgeFinset] using e.2
          rw [← heq]
          exact he'
        simpa only [SimpleGraph.mem_edgeSet] using he
      obtain ⟨w, hw, _⟩ := activeBrokenWitnessRelayGraph_existsUnique_witness
        A hfree active mate hclosed hinvol hfixed hR
      have hwy : (triangleFreeEdgeGraph A).Adj w y := by
        rw [← hw.2.2]
        exact hclosed w x hw.2.1
      refine ⟨w, ?_, ?_⟩
      · refine ⟨hw.1, ?_⟩
        intro v hv
        rw [Sym2.toFinset_mk_eq] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hw.2.1
        · exact hwy
      · intro w' hw'
        have hne : x ≠ y :=
          (activeBrokenWitnessRelayGraph A active mate
            hclosed hinvol hfixed).ne_of_adj hR
        have hw'x : (triangleFreeEdgeGraph A).Adj w' x := by
          apply hw'.2 x
          simp [Sym2.toFinset_mk_eq]
        have hw'y : (triangleFreeEdgeGraph A).Adj w' y := by
          apply hw'.2 y
          simp [Sym2.toFinset_mk_eq]
        have hsub : ∀ {u v}, (triangleFreeEdgeGraph A).Adj u v → A.Adj u v := by
          intro u v huv
          exact ((mem_triangleFreeNeighbors A u v).mp huv).1
        exact commonNeighbor_unique_of_c4Free hfree hne
          (hsub hw'x).symm (hsub hw'y).symm
          (hsub hw.2.1).symm (hsub hwy).symm

/-- Canonical active witness label of a relay edge. -/
def activeBrokenRelayEdgeWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (e : (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).edgeFinset) : V :=
  Classical.choose (activeBrokenRelay_edge_existsUnique_witness
    A hfree active mate hclosed hinvol hfixed e)

theorem activeBrokenRelayEdgeWitness_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    (e : (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).edgeFinset) :
    IsActiveBrokenRelayEdgeWitness A active
      (activeBrokenRelayEdgeWitness A hfree active mate
        hclosed hinvol hfixed e) e.1 :=
  Classical.choose_spec (activeBrokenRelay_edge_existsUnique_witness
    A hfree active mate hclosed hinvol hfixed e) |>.1

/-- The relay edge set is exactly partitioned by its canonical active
witness labels. -/
theorem activeBrokenRelayEdgeWitness_sum_fiber_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) :
    (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).edgeFinset.card =
      ∑ w : V, ((Finset.univ : Finset
        (activeBrokenWitnessRelayGraph A active mate
          hclosed hinvol hfixed).edgeFinset).filter fun e =>
          activeBrokenRelayEdgeWitness A hfree active mate
            hclosed hinvol hfixed e = w).card := by
  rw [← Fintype.card_coe]
  apply Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
  intro e _
  exact Finset.mem_univ _

end

end Erdos85

#print axioms Erdos85.activeBrokenRelay_edge_existsUnique_witness
#print axioms Erdos85.activeBrokenRelayEdgeWitness_spec
#print axioms Erdos85.activeBrokenRelayEdgeWitness_sum_fiber_card
