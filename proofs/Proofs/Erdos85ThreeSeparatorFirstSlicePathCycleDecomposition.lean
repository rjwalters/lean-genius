import Proofs.Erdos85ThreeSeparatorFirstSliceInternalProfile
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! # Cycle half of the first-slice path-cycle decomposition -/

open Finset SimpleGraph

namespace Erdos85

/-- A finite graph with maximum degree two and no nonisolated degree-one
vertex is a union of cycles in Mathlib's `IsCycles` sense. -/
theorem isCycles_of_degree_le_two_of_no_degree_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : ∀ v, G.degree v ≤ 2)
    (hnoOne : ∀ v, G.degree v ≠ 1) :
    G.IsCycles := by
  intro v hv
  have hpos : 0 < G.degree v := G.degree_pos_iff_nonempty.mpr hv
  have hdeg : G.degree v = 2 := by
    have hle := hmax v
    have hne := hnoOne v
    omega
  calc
    (G.neighborSet v).ncard = (G.neighborSet v).toFinite.toFinset.card :=
      Set.ncard_eq_toFinset_card _
    _ = (G.neighborFinset v).card := by
      congr 1
      ext z
      simp [SimpleGraph.mem_neighborFinset]
    _ = 2 := hdeg

/-- A component/restriction of the a=1 profile containing no K-point is
therefore a cycle component.  The remaining components are the path half of
B22 and require the separate maximal-path argument. -/
theorem isCycles_of_firstSlice_profile_of_empty_K
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset V) (hK : K = ∅)
    (hprofile : ∀ v, G.degree v + (if v ∈ K then 1 else 0) = 2) :
    G.IsCycles := by
  apply isCycles_of_degree_le_two_of_no_degree_one G
  · intro v
    have := hprofile v
    omega
  · intro v
    have := hprofile v
    simp [hK] at this
    omega

#print axioms isCycles_of_degree_le_two_of_no_degree_one
#print axioms isCycles_of_firstSlice_profile_of_empty_K

end Erdos85
