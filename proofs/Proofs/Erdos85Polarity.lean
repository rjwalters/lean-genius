import Proofs.Erdos85TightWitness
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Finite-field polarity witnesses for Erdős Problem 85

The orthogonal polarity of the projective plane over a finite field gives a
`C₄`-free graph on `q² + q + 1` vertices with minimum degree at least `q`.
This module isolates that classical construction behind the witness interface
used by `Erdos85TightWitness`.
-/

open SimpleGraph Finset
open scoped LinearAlgebra.Projectivization

namespace Erdos85

namespace Polarity

/-- The orthogonal-polarity graph of `PG(2,K)`.  Isotropic points would give
loops in the raw orthogonality relation; `SimpleGraph.fromRel` removes them. -/
noncomputable def graph (K : Type*) [Field K] : SimpleGraph (ℙ K (Fin 3 → K)) :=
  SimpleGraph.fromRel (Projectivization.orthogonal (F := K) (m := Fin 3))

noncomputable instance pointFintype (K : Type*) [Field K] [Finite K] :
    Fintype (ℙ K (Fin 3 → K)) :=
  Fintype.ofFinite _

noncomputable instance pointDecidableEq (K : Type*) [Field K] :
    DecidableEq (ℙ K (Fin 3 → K)) :=
  Classical.decEq _

noncomputable instance graphDecidableAdj (K : Type*) [Field K] :
    DecidableRel (graph K).Adj :=
  Classical.decRel _

theorem graph_adj_iff {K : Type*} [Field K] (x y : ℙ K (Fin 3 → K)) :
    (graph K).Adj x y ↔ x ≠ y ∧ Projectivization.orthogonal x y := by
  simp only [graph, SimpleGraph.fromRel_adj]
  rw [Projectivization.orthogonal_comm (v := y) (w := x)]
  tauto

/-- Two distinct projective points have at most one common neighbor in the
polarity graph.  This is exactly uniqueness of the intersection of two lines
in the projective plane. -/
theorem commonNeighbors_le_one {K : Type*} [Field K] [Finite K]
    (x y : ℙ K (Fin 3 → K)) (hxy : x ≠ y) :
    ((graph K).neighborFinset x ∩ (graph K).neighborFinset y).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro z w hz hw
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz hw
  have hzx : z ∈ x := (Configuration.ofField.mem_iff z x).2
    (Projectivization.orthogonal_comm.mp ((graph_adj_iff x z).mp hz.1 |>.2))
  have hzy : z ∈ y := (Configuration.ofField.mem_iff z y).2
    (Projectivization.orthogonal_comm.mp ((graph_adj_iff y z).mp hz.2 |>.2))
  have hwx : w ∈ x := (Configuration.ofField.mem_iff w x).2
    (Projectivization.orthogonal_comm.mp ((graph_adj_iff x w).mp hw.1 |>.2))
  have hwy : w ∈ y := (Configuration.ofField.mem_iff w y).2
    (Projectivization.orthogonal_comm.mp ((graph_adj_iff y w).mp hw.2 |>.2))
  exact (Configuration.Nondegenerate.eq_or_eq hzx hwx hzy hwy).resolve_right hxy

/-- The finite-field polarity graph contains no four-cycle. -/
theorem graph_not_containsC4 {K : Type*} [Field K] [Finite K] :
    ¬ containsC4 (ℙ K (Fin 3 → K)) (graph K) := by
  classical
  exact not_containsC4_of_forall_common_le_one
    (fun x y hxy ↦ commonNeighbors_le_one x y hxy)

end Polarity

end Erdos85
