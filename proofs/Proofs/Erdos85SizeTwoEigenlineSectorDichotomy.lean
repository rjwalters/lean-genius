import Proofs.Erdos85SizeTwoEigenlineSectorRefinement
import Proofs.Erdos85SizeTwoEigenlineTriangleFreeSector

/-!
# Complete sector dichotomy for a connected size-two eigenline component

The local sector correction and its connected propagation combine with the
all-triangle K-law classification.  Uniformly in even `q`, the missing-cell
relation is always reflection-circulant.  Its parameter is zero in the
triangle-free sector and is nonzero in the all-triangle sector.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Sector-refined reflection-circulant classification.**  For a connected
normalized size-two component, either a triangle-free internal edge exists
and the holes are the internal shifts `{0,-1}`, or no such edge exists and
the all-triangle K-law theorem supplies `{t,-1-t}` with `t ∉ {0,-1}`.
In both cases the unified conclusion below holds. -/
theorem eigenline_hole_reflectionCirculant_of_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hconn : (G.induce c.supp).Connected)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (coord : SizeTwoCycleGridCoordinates G c.supp s q) :
    ∃ t : ZMod q, t ≠ -1 ∧
      ∀ x y : ZMod q,
        (¬ ∃ u, IsGridWitness G c coord.pval coord.nval u x y) ↔
          y - x = t ∨ y - x = -1 - t := by
  classical
  by_cases hseed : ∃ x y : ZMod q,
      (triangleFreeEdgeGraph G).Adj (coord.pval x) (coord.nval y)
  · refine ⟨0, ?_, ?_⟩
    · have hq2 : 2 ∣ q := even_iff_two_dvd.mp hqEven
      intro h
      have hz := congrArg (ZMod.castHom hq2 (ZMod 2)) h
      simp only [map_zero, map_neg, map_one] at hz
      exact absurd hz (by decide)
    · intro x y
      rw [eigenline_hole_eq_internal_of_connected_exists_triangleFreeEdge
        G hfree hq hqEven hreg hcard c hc hconn s hs_in hs_out hsum hA_in
          hDs coord hseed]
      constructor
      · rintro (rfl | h)
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [h]; ring)
      · rintro (h | h)
        · left
          have hz := congrArg (fun z : ZMod q => z + x) h
          simpa using hz
        · right
          have hz := congrArg (fun z : ZMod q => z + x) h
          simpa [sub_eq_add_neg, add_comm] using hz
  · have hTri : ∀ x : ZMod q,
        (∃ u, IsGridWitness G c coord.pval coord.nval u x x) ∧
          (∃ u, IsGridWitness G c coord.pval coord.nval u x (x - 1)) := by
      intro x
      constructor
      · by_contra hhole
        apply hseed
        refine ⟨x, x, ?_⟩
        exact (eigenline_gridHole_iff_triangleFreeEdge G hfree (by omega)
          hreg hcard c hc s hs_in hs_out hA_in coord.pval coord.nval
          coord.p_mem_sign coord.n_mem_sign x x
          ((coord.adj_iff x x).mpr (Or.inl rfl))).mp hhole
      · by_contra hhole
        apply hseed
        refine ⟨x, x - 1, ?_⟩
        exact (eigenline_gridHole_iff_triangleFreeEdge G hfree (by omega)
          hreg hcard c hc s hs_in hs_out hA_in coord.pval coord.nval
          coord.p_mem_sign coord.n_mem_sign x (x - 1)
          ((coord.adj_iff x (x - 1)).mpr (Or.inr rfl))).mp hhole
    have hq2 : 2 ∣ q := even_iff_two_dvd.mp hqEven
    obtain ⟨t, ht0, htm1, ht⟩ := eigenline_hole_reflectionCirculant
      G c s coord.pval coord.nval hfree hq hq2 hreg hcard hc hs_in hs_out
        hsum hA_in hDs coord.p_mem_sign coord.n_mem_sign coord.p_injective
        coord.n_injective coord.p_surjective coord.n_surjective coord.adj_iff hTri
    exact ⟨t, htm1, ht⟩

end

end Erdos85

#print axioms Erdos85.eigenline_hole_reflectionCirculant_of_connected
