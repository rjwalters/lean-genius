import Proofs.Erdos85CubicResidualFiberHistogram

/-!
# The global graph of marked cubic-value-five pairs

The sharp cross-row census produces a symmetric relation on the twenty-four
cross-type residual edges, with exactly two marked partners at every edge.
This file records the finite graph consequence independently of the later
coordinate classification: the marked relation is two-regular and has exactly
twenty-four undirected pairs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Reversing a length-three walk proves that the cubic residual walk count is
symmetric in its two edge arguments. -/
theorem residualFiberCubicWalkCount_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a b : R.edgeFinset) :
    residualFiberCubicWalkCount R Cedge a b =
      residualFiberCubicWalkCount R Cedge b a := by
  unfold residualFiberCubicWalkCount
  apply Fintype.card_congr
  exact
    { toFun := fun p ↦ ⟨p.1.reverse, by
        change p.1.reverse.length = 3
        rw [SimpleGraph.Walk.length_reverse]
        exact p.2⟩
      invFun := fun p ↦ ⟨p.1.reverse, by
        change p.1.reverse.length = 3
        rw [SimpleGraph.Walk.length_reverse]
        exact p.2⟩
      left_inv := by intro p; apply Subtype.ext; simp
      right_inv := by intro p; apply Subtype.ext; simp }

/-- The simple graph associated to a symmetric predicate.  The explicit
inequality makes this construction useful even when no irreflexivity theorem
for the predicate has yet been supplied. -/
def symmetricMarkedGraph {α : Type*} (P : α → α → Prop)
    (hsymm : ∀ ⦃a b⦄, P a b → P b a) : SimpleGraph α where
  Adj a b := a ≠ b ∧ P a b
  symm := ⟨by
    intro a b hab
    exact ⟨Ne.symm hab.1, hsymm hab.2⟩⟩
  loopless := ⟨by simp⟩

@[simp]
theorem symmetricMarkedGraph_adj {α : Type*} (P : α → α → Prop)
    (hsymm : ∀ ⦃a b⦄, P a b → P b a) (a b : α) :
    (symmetricMarkedGraph P hsymm).Adj a b ↔ a ≠ b ∧ P a b :=
  Iff.rfl

/-- The finite set of unordered pairs in a symmetric marked relation. -/
noncomputable def symmetricMarkedEdgeFinset {α : Type*} [Fintype α]
    (P : α → α → Prop) (hsymm : ∀ ⦃a b⦄, P a b → P b a) :
    Finset (Sym2 α) := by
  classical
  exact (symmetricMarkedGraph P hsymm).edgeFinset

/-- A symmetric marked relation of local valency two on twenty-four objects
has twenty-four undirected marked pairs.  This is the global handshaking
consequence needed by the sharp cross-cubic equality case. -/
theorem symmetricMarkedGraph_card_edges_eq_twentyFour
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → α → Prop) [DecidableRel P]
    (hsymm : ∀ ⦃a b⦄, P a b → P b a)
    (hcard : Fintype.card α = 24)
    (hdegree : ∀ a : α,
      (Finset.univ.filter (fun b : α ↦ a ≠ b ∧ P a b)).card = 2) :
    (symmetricMarkedEdgeFinset P hsymm).card = 24 := by
  classical
  let M := symmetricMarkedGraph P hsymm
  have hdeg : ∀ a : α, M.degree a = 2 := by
    intro a
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hn : M.neighborFinset a =
        Finset.univ.filter (fun b : α ↦ a ≠ b ∧ P a b) := by
      ext b
      simp [M, symmetricMarkedGraph]
    rw [hn]
    exact hdegree a
  have hhandshake := M.sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hhandshake
  simp [hcard] at hhandshake
  have hedge : M.edgeFinset.card = 24 := by omega
  exact hedge

/-- Finset-facing form of the marked-graph count.  It is the convenient
socket for the set of cross-type residual edges: symmetry is ambient, while
the local hypothesis counts only partners that remain in `S`. -/
theorem restricted_symmetricMarkedGraph_card_edges_eq_twentyFour
    {α : Type*} [DecidableEq α]
    (S : Finset α) (P : α → α → Prop) [DecidableRel P]
    (hsymm : ∀ ⦃a b⦄, P a b → P b a)
    (hcard : S.card = 24)
    (hdegree : ∀ a ∈ S,
      (S.filter (fun b : α ↦ a ≠ b ∧ P a b)).card = 2) :
    (symmetricMarkedEdgeFinset
      (fun a b : S ↦ P a.1 b.1)
      (by intro a b hab; exact hsymm hab)).card = 24 := by
  classical
  apply symmetricMarkedGraph_card_edges_eq_twentyFour
  · simpa using hcard
  · intro a
    have hsubtypeFilter :
        (Finset.univ.filter
          (fun b : S ↦ a ≠ b ∧ P a.1 b.1)).card =
        (S.filter (fun b : α ↦ a.1 ≠ b ∧ P a.1 b)).card := by
      let e : S ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
      have hmap :
          (Finset.univ.filter
            (fun b : S ↦ a ≠ b ∧ P a.1 b.1)).map e =
          S.filter (fun b : α ↦ a.1 ≠ b ∧ P a.1 b) := by
        ext b
        constructor
        · intro hb
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hb
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨x.2, fun hax ↦
            hx'.2.1 (Subtype.ext hax), hx'.2.2⟩
        · intro hb
          have hb' := Finset.mem_filter.mp hb
          let x : S := ⟨b, hb'.1⟩
          apply Finset.mem_map.mpr
          refine ⟨x, ?_, rfl⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ x, ?_, hb'.2.2⟩
          intro hax
          exact hb'.2.1 (congrArg Subtype.val hax)
      rw [← hmap, Finset.card_map]
    rw [hsubtypeFilter]
    exact hdegree a.1 a.2

/-- Graph-facing socket for the global sharp cross-row equality case.  Once
`S` is identified with the twenty-four cross-type residual edges, local sharp
equality supplies the two-partner hypothesis.  Symmetry of cubic walk counts
then turns the twenty-four local matchings into exactly twenty-four unordered
value-five pairs. -/
theorem cubicValueFive_markedPairs_card_twentyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset R.edgeFinset)
    (hcard : S.card = 24)
    (hsharp : ∀ a ∈ S,
      (S.filter (fun b : R.edgeFinset ↦ a ≠ b ∧
        residualFiberCubicWalkCount R Cedge a b = 5)).card = 2) :
    (symmetricMarkedEdgeFinset
      (fun a b : S ↦
        residualFiberCubicWalkCount R Cedge a.1 b.1 = 5)
      (by
        intro a b hab
        rwa [residualFiberCubicWalkCount_comm R Cedge] at hab)).card = 24 := by
  exact restricted_symmetricMarkedGraph_card_edges_eq_twentyFour
    S (fun a b ↦ residualFiberCubicWalkCount R Cedge a b = 5)
      (by
        intro a b hab
        rwa [residualFiberCubicWalkCount_comm R Cedge] at hab)
      hcard hsharp

end

end Erdos85

#print axioms Erdos85.residualFiberCubicWalkCount_comm
#print axioms Erdos85.cubicValueFive_markedPairs_card_twentyFour
