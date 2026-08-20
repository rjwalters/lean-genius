import Proofs.Erdos85CubicResidualFiberHistogram
import Proofs.Erdos85CubicFiberHistogramMinima

/-! # Marked-edge matching forced by cubic equality -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If every vertex of a four-set lies on exactly one marked edge, and every
marked edge has both endpoints in that set, then there are exactly two marked
edges.  This is the incidence-counting core of the cubic-fiber equality case:
the four exceptional coordinates must be paired by two value-five edges. -/
theorem four_vertices_unique_markedEdge_card_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (X : Finset V) (M : Finset R.edgeFinset)
    (hX : X.card = 4)
    (hinside : ∀ e ∈ M, e.1.toFinset ⊆ X)
    (hunique : ∀ x ∈ X, ∃! e : R.edgeFinset,
      e ∈ M ∧ x ∈ e.1.toFinset) :
    M.card = 2 := by
  classical
  let I : ℕ := ∑ x ∈ X, ∑ e ∈ M,
    if x ∈ e.1.toFinset then 1 else 0
  have hIvertex : I = 4 := by
    calc
      I = ∑ _x ∈ X, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨e, ⟨heM, hxe⟩, heuniq⟩ := hunique x hx
        rw [Finset.sum_boole]
        apply Finset.card_eq_one.mpr
        refine ⟨e, ?_⟩
        ext f
        simp only [Finset.mem_filter]
        constructor
        · intro hf
          exact Finset.mem_singleton.mpr (heuniq f ⟨hf.1, hf.2⟩)
        · intro hf
          have hfe : f = e := Finset.mem_singleton.mp hf
          subst f
          exact ⟨heM, hxe⟩
      _ = 4 := by simp [hX]
  have hIedge : I = 2 * M.card := by
    calc
      I = ∑ e ∈ M, ∑ x ∈ X,
          if x ∈ e.1.toFinset then 1 else 0 := by
            simp only [I]
            rw [Finset.sum_comm]
      _ = ∑ _e ∈ M, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_boole]
        have hinter : X.filter (· ∈ e.1.toFinset) = e.1.toFinset := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · exact fun hx => hx.2
          · intro hx
            exact ⟨hinside e he hx, hx⟩
        rw [hinter]
        norm_num [R.card_toFinset_mem_edgeFinset e]
      _ = 2 * M.card := by simp [mul_comm]
  omega

def cubicValueFiveEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) : Finset R.edgeFinset :=
  Finset.univ.filter fun b =>
    residualFiberCubicWalkCount R Cedge a b = 5

/-- Graph-facing equality consumer.  If the four exceptional residual fibers
attain the sharp six-value/sum-25 square minimum, while every other vertex has
no residual value five, then the value-five entries are exactly two exterior
edges pairing those four vertices. -/
theorem cubicResidual_sharp_fourFibers_valueFiveEdge_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    (a : R.edgeFinset) (X : Finset V)
    (hX : X.card = 4)
    (hsharp : ∀ x ∈ X,
      let c := cubicResidualFiberHistogram R Cedge x a
      (∑ t ∈ Finset.range 7, c t) = 6 ∧
        (∑ t ∈ Finset.range 7, t * c t) = 25 ∧
        (∑ t ∈ Finset.range 7, t ^ 2 * c t) ≤ 105)
    (houtside : ∀ x ∉ X,
      cubicResidualFiberHistogram R Cedge x a 5 = 0) :
    let M := cubicValueFiveEdgeFinset R Cedge a
    M.card = 2 ∧
      (∀ b ∈ M, b.1.toFinset ⊆ X) ∧
      ∀ x ∈ X, ∃! b : R.edgeFinset, b ∈ M ∧ x ∈ b.1.toFinset := by
  classical
  dsimp only
  let M := cubicValueFiveEdgeFinset R Cedge a
  have hnotadj {b : R.edgeFinset}
      (hb5 : residualFiberCubicWalkCount R Cedge a b = 5) :
      ¬ Cedge.Adj b a := by
    intro hba
    have h11 := sixRegular_c4Free_residualFiberCubicWalkCount_of_adj
      R Cedge hfree hreg hba
    omega
  have hinside : ∀ b ∈ M, b.1.toFinset ⊆ X := by
    intro b hb y hy
    by_contra hyX
    have hout := houtside y hyX
    change ((cubicResidualFiber R Cedge y a).filter fun e =>
      residualFiberCubicWalkCount R Cedge a e = 5).card = 0 at hout
    have hb5 : residualFiberCubicWalkCount R Cedge a b = 5 :=
      (Finset.mem_filter.mp hb).2
    have hbmem : b ∈ (cubicResidualFiber R Cedge y a).filter fun e =>
        residualFiberCubicWalkCount R Cedge a e = 5 := by
      refine Finset.mem_filter.mpr ⟨?_, hb5⟩
      refine Finset.mem_filter.mpr ⟨?_, hnotadj hb5⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    exact (Finset.card_ne_zero.mpr ⟨b, hbmem⟩) hout
  have hunique : ∀ x ∈ X, ∃! b : R.edgeFinset,
      b ∈ M ∧ x ∈ b.1.toFinset := by
    intro x hx
    let c := cubicResidualFiberHistogram R Cedge x a
    have hs := hsharp x hx
    dsimp only at hs
    have hh := six_cubicValues_sum_twentyFive_eq_minimum c
      hs.1 hs.2.1 hs.2.2
    have hc5 : c 5 = 1 := hh.2.2.2.2.2.1
    let F := (cubicResidualFiber R Cedge x a).filter fun b =>
      residualFiberCubicWalkCount R Cedge a b = 5
    have hF : F.card = 1 := by
      simpa [F, c, cubicResidualFiberHistogram, boundedHistogram]
        using hc5
    obtain ⟨b, hbF⟩ := Finset.card_eq_one.mp hF
    refine ⟨b, ?_, ?_⟩
    · have hb : b ∈ F := by rw [hbF]; simp
      have hb' := Finset.mem_filter.mp hb
      have hinc := (Finset.mem_filter.mp hb'.1).1
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.2⟩,
        (Finset.mem_filter.mp hinc).2⟩
    · intro d hd
      have hd5 : residualFiberCubicWalkCount R Cedge a d = 5 :=
        (Finset.mem_filter.mp hd.1).2
      have hdF : d ∈ F := by
        refine Finset.mem_filter.mpr ⟨?_, hd5⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.2⟩,
            hnotadj hd5⟩
      rw [hbF] at hdF
      exact Finset.mem_singleton.mp hdF
  exact ⟨four_vertices_unique_markedEdge_card_two
    R X M hX hinside hunique, hinside, hunique⟩

/-- Cardinality projection of the full matching package. -/
theorem cubicResidual_sharp_fourFibers_valueFiveEdge_card_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    (a : R.edgeFinset) (X : Finset V)
    (hX : X.card = 4)
    (hsharp : ∀ x ∈ X,
      let c := cubicResidualFiberHistogram R Cedge x a
      (∑ t ∈ Finset.range 7, c t) = 6 ∧
        (∑ t ∈ Finset.range 7, t * c t) = 25 ∧
        (∑ t ∈ Finset.range 7, t ^ 2 * c t) ≤ 105)
    (houtside : ∀ x ∉ X,
      cubicResidualFiberHistogram R Cedge x a 5 = 0) :
    (cubicValueFiveEdgeFinset R Cedge a).card = 2 :=
  (cubicResidual_sharp_fourFibers_valueFiveEdge_matching
    R Cedge hfree hreg a X hX hsharp houtside).1

end

end Erdos85

#print axioms Erdos85.four_vertices_unique_markedEdge_card_two
#print axioms
  Erdos85.cubicResidual_sharp_fourFibers_valueFiveEdge_matching
#print axioms
  Erdos85.cubicResidual_sharp_fourFibers_valueFiveEdge_card_two
