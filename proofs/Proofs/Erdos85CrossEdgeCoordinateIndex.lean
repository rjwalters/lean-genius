import Proofs.Erdos85CrossEdgeCoordinateRepresentation

/-! # A canonical first-shore coordinate for every cross edge -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The first-shore coordinate of a canonical type-one edge. -/
noncomputable def shoreTypeOneEdgeFirstCoordinate
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1) : ZMod 8 :=
  Classical.choose
    (shoreTypeOneEdge_exists_crossCoordinates R u v hcover a.1 a.2)

/-- The chosen first coordinate participates in an actual cross-coordinate
support representation. -/
theorem shoreTypeOneEdgeFirstCoordinate_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1) :
    ∃ j : ZMod 8, a.1.1.toFinset =
      {u (shoreTypeOneEdgeFirstCoordinate R u v hcover a), v j} := by
  let hex := shoreTypeOneEdge_exists_crossCoordinates
    R u v hcover a.1 a.2
  exact ⟨Classical.choose hex.choose_spec,
    Classical.choose_spec hex.choose_spec⟩

/-- Injective disjoint shore coordinates make the chosen first coordinate
equal to the first coordinate in any displayed support representation. -/
theorem shoreTypeOneEdgeFirstCoordinate_eq_of_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1)
    (i j : ZMod 8) (ha : a.1.1.toFinset = {u i, v j}) :
    shoreTypeOneEdgeFirstCoordinate R u v hcover a = i := by
  obtain ⟨k, hk⟩ :=
    shoreTypeOneEdgeFirstCoordinate_support R u v hcover a
  have hui : u i ∈ a.1.1.toFinset := by rw [ha]; simp
  rw [hk] at hui
  rcases Finset.mem_insert.mp hui with hui | hui
  · exact (huinj hui).symm
  · have huiv : u i = v k := Finset.mem_singleton.mp hui
    exact False.elim (hdisj i k huiv)

end

end Erdos85

#print axioms Erdos85.shoreTypeOneEdgeFirstCoordinate_support
#print axioms Erdos85.shoreTypeOneEdgeFirstCoordinate_eq_of_support
