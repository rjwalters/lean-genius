import Proofs.Erdos85MinimalWitness
import Proofs.Erdos85OneDefectCore

/-!
# A canonical tight almost-core at every order
-/

open SimpleGraph

namespace Erdos85

/-- At the top admissible degree, star deletion gives an exact-size safe
selector and satisfies every intrinsic one-defect-core condition away from
one isolated center. -/
theorem exists_top_starDeleted_almostIntrinsic {n : ℕ} (hn : 4 ≤ n) :
    let d := minDegreeForC4 n - 1
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (x : Fin n),
      let H := G.deleteIncidenceSet x
      let S := G.neighborFinset x
      S.card = d ∧
      ¬ containsC4 (Fin n) H ∧
      CommonNeighborIndependent H S ∧
      H.degree x = 0 ∧
      (∀ y, y ≠ x → d - 1 ≤ H.degree y) ∧
      ∀ y, y ≠ x → H.degree y = d - 1 → y ∈ S := by
  dsimp
  obtain ⟨G, hdec, x, hmin, hx, hfree⟩ := exists_top_tight_vertex hn
  letI : DecidableRel G.Adj := hdec
  have hd : 1 ≤ minDegreeForC4 n - 1 := by
    have htwo : 2 ≤ minDegreeForC4 n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact two_le_minDegreeForC4 (by omega)
    omega
  have hall := exists_starDeleted_almostIntrinsic G x hd hmin.ge hfree
  rcases hall with ⟨hcorefree, hsafe, _, hcenter, hdegrees, htight⟩
  refine ⟨G, hdec, x, ?_, hcorefree, hsafe, hcenter, hdegrees, htight⟩
  simpa [SimpleGraph.card_neighborFinset_eq_degree] using hx

/-- Reattaching the canonical star-deletion selector does not repair its
exceptional center: the center is not in its own old neighbourhood, so it
remains isolated.  This records the precise gap between the canonical
almost-intrinsic core and a genuine `OneDefectCore`. -/
theorem starDeleted_attach_neighborFinset_degree_center_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (attachVertex (G.deleteIncidenceSet x) (G.neighborFinset x)).degree
        (some x) = 0 := by
  rw [attachVertex_degree_some_eq]
  have hcenter : (G.deleteIncidenceSet x).degree x = 0 := by
    rw [degree]
    have hfin : (G.deleteIncidenceSet x).neighborFinset x = ∅ := by
      ext y
      simp [SimpleGraph.deleteIncidenceSet_adj]
    rw [hfin]
    simp
  rw [hcenter]
  simp

/-- Consequently, at every positive target degree the canonical star-deleted
graph and its old-neighbourhood selector fail the old-vertex degree clause of
`OneDefectCore`, specifically at the deleted center. -/
theorem starDeleted_neighborFinset_not_oldDegreeCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {d : ℕ}
    (hd : 1 ≤ d) :
    ¬ ∀ v, d ≤
      (attachVertex (G.deleteIncidenceSet x) (G.neighborFinset x)).degree
        (some v) := by
  intro hcover
  have hx := hcover x
  rw [starDeleted_attach_neighborFinset_degree_center_eq_zero G x] at hx
  omega

end Erdos85
