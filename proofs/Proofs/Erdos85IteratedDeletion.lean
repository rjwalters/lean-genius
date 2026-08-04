import Proofs.Erdos85VertexDeletion

/-!
# Iterated vertex deletion for C4-free witnesses

Deleting k vertices from a witness costs at most k units of certified minimum
degree.  This packages the one-vertex deletion theorem into a reusable global
construction tool.
-/

namespace Erdos85

/-- Iterating arbitrary vertex deletion k times turns an order n+k,
minimum-degree-d witness into an order n, minimum-degree-(d-k) witness. -/
theorem C4FreeMinDegreeWitness.delete_vertices
    {n d k : ℕ} (hn : 1 ≤ n)
    (hw : C4FreeMinDegreeWitness (n + k) d) :
    C4FreeMinDegreeWitness n (d - k) := by
  induction k generalizing d with
  | zero =>
      simpa using hw
  | succ k ih =>
      rcases hw with ⟨G, hdec, hmin, hfree⟩
      letI : DecidableRel G.Adj := hdec
      have horder : n + (k + 1) = (n + k) + 1 := by omega
      have hcard : Fintype.card (Fin (n + (k + 1))) = (n + k) + 1 := by
        simp [horder]
      let x : Fin (n + (k + 1)) := ⟨0, by omega⟩
      have hdel : C4FreeMinDegreeWitness (n + k) (d - 1) :=
        c4FreeMinDegreeWitness_delete_vertex G x hcard (by omega) hmin hfree
      have hiter := ih (d := d - 1) hdel
      have hdegree : (d - 1) - k = d - (k + 1) := by omega
      simpa [hdegree] using hiter

/-- Equivalent subtraction-indexed form: deleting k vertices from an order N
witness yields order N-k whenever the subtraction is exact. -/
theorem C4FreeMinDegreeWitness.delete_vertices_sub
    {N d k : ℕ} (hk : k ≤ N) (hremain : 1 ≤ N - k)
    (hw : C4FreeMinDegreeWitness N d) :
    C4FreeMinDegreeWitness (N - k) (d - k) := by
  apply C4FreeMinDegreeWitness.delete_vertices hremain
  simpa [Nat.sub_add_cancel hk] using hw

/-- A deleted witness gives a threshold lower bound at the smaller order. -/
theorem minDegreeForC4_lower_of_witness_delete_vertices
    {N d k : ℕ} (hk : k ≤ N) (hremain : 4 ≤ N - k)
    (hw : C4FreeMinDegreeWitness N d) :
    d - k < minDegreeForC4 (N - k) := by
  exact (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hremain).1
    (hw.delete_vertices_sub hk (by omega))

end Erdos85
