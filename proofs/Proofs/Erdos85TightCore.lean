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

end Erdos85
