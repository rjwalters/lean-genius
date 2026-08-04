import Proofs.Erdos85Problem

/-!
# Relabeling finite witnesses for Erdős problem 85

The threshold `minDegreeForC4` is stated for graphs on `Fin n`, while natural
constructions often live on a more convenient finite vertex type.  This file
packages the routine transport across a finite equivalence.
-/

open SimpleGraph

namespace Erdos85

/-- Containing a four-cycle is invariant under graph isomorphism. -/
theorem containsC4_iff_of_iso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) :
    containsC4 V G ↔ containsC4 W H := by
  constructor
  · rintro ⟨f, hf, hadj⟩
    exact ⟨e ∘ f, e.injective.comp hf, fun i j hij ↦ e.map_rel_iff.mpr (hadj i j hij)⟩
  · rintro ⟨f, hf, hadj⟩
    exact ⟨e.symm ∘ f, e.symm.injective.comp hf,
      fun i j hij ↦ e.symm.map_rel_iff.mpr (hadj i j hij)⟩

/-- A finite `C₄`-free minimum-degree graph can be relabeled onto `Fin n`.

This is the bridge from graph constructions on convenient finite types (such
as projective points or quotient types) to `C4FreeMinDegreeWitness`, whose
vertex type is fixed to `Fin n` by the definition of the extremal function.
-/
theorem c4FreeMinDegreeWitness_of_card_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n d : ℕ}
    (hcard : Fintype.card V = n) (hmin : d ≤ G.minDegree)
    (hfree : ¬ containsC4 V G) :
    C4FreeMinDegreeWitness n d := by
  let H : SimpleGraph (Fin n) := G.overFin hcard
  let e : G ≃g H := G.overFinIso hcard
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨H, inferInstance, ?_, ?_⟩
  · simpa [e] using hmin.trans_eq e.minDegree_eq
  · intro hC4
    exact hfree ((containsC4_iff_of_iso e).mpr hC4)

end Erdos85
