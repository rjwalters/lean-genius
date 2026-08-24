import Proofs.Erdos85C4FreeWitnessPairingRelay

/-!
# Canonical witness labels on full neighbor-star relay edges

The global paired-star relay is a simple graph, so its witness labels are not
stored in its edge type.  C4-freeness recovers a unique ambient witness for
every relay edge.  This supplies the concrete label map needed by the
labeled-involution boundary handshake `(73rnz_cjibkzj)--(73rnz_cjibkzk)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A vertex is the ambient star witness of an unordered relay edge. -/
def IsFullRelayEdgeWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (w : V) (e : Sym2 V) : Prop :=
  ∀ v ∈ e.toFinset, A.Adj w v

/-- Every edge of a C4-free full neighbor-star relay has a unique ambient
star witness. -/
theorem fullRelay_edge_existsUnique_witness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (e : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).edgeFinset) :
    ∃! w, IsFullRelayEdgeWitness A w e.1 := by
  generalize heq : e.1 = z
  induction z using Sym2.inductionOn with
  | _ x y =>
      have hP : (witnessPairingRelayGraph A.Adj mate
          hclosed hinvol hfixed).Adj x y := by
        have he : s(x, y) ∈ (witnessPairingRelayGraph A.Adj mate
            hclosed hinvol hfixed).edgeSet := by
          have he' : e.1 ∈ (witnessPairingRelayGraph A.Adj mate
              hclosed hinvol hfixed).edgeSet := by
            simpa only [SimpleGraph.mem_edgeFinset] using e.2
          rw [← heq]
          exact he'
        simpa only [SimpleGraph.mem_edgeSet] using he
      have hne : x ≠ y :=
        (witnessPairingRelayGraph A.Adj mate
          hclosed hinvol hfixed).ne_of_adj hP
      change ∃ w, A.Adj w x ∧ mate w x = y at hP
      obtain ⟨w, hwx, hm⟩ := hP
      have hwy : A.Adj w y := by
        rw [← hm]
        exact hclosed w x hwx
      refine ⟨w, ?_, ?_⟩
      · intro v hv
        rw [Sym2.toFinset_mk_eq] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hwx
        · exact hwy
      · intro w' hw'
        have hw'x : A.Adj w' x := by
          apply hw' x
          simp [Sym2.toFinset_mk_eq]
        have hw'y : A.Adj w' y := by
          apply hw' y
          simp [Sym2.toFinset_mk_eq]
        exact commonNeighbor_unique_of_c4Free hfree hne
          hw'x.symm hw'y.symm hwx.symm hwy.symm

/-- Canonical ambient witness label of a full relay edge. -/
def fullRelayEdgeWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (e : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).edgeFinset) : V :=
  Classical.choose (fullRelay_edge_existsUnique_witness
    A hfree mate hclosed hinvol hfixed e)

/-- The canonical label is adjacent in `A` to both endpoints of its relay
edge. -/
theorem fullRelayEdgeWitness_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (e : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).edgeFinset) :
    IsFullRelayEdgeWitness A
      (fullRelayEdgeWitness A hfree mate hclosed hinvol hfixed e) e.1 :=
  Classical.choose_spec (fullRelay_edge_existsUnique_witness
    A hfree mate hclosed hinvol hfixed e) |>.1

end

end Erdos85

#print axioms Erdos85.fullRelay_edge_existsUnique_witness
#print axioms Erdos85.fullRelayEdgeWitness_spec
