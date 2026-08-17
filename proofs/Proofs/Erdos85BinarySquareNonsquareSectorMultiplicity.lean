import Proofs.Erdos85QuadraticDimensionField
import Proofs.Erdos85BinarySquareComponentFrequencyPair

/-!
# Multiplicity forced by a nonsquare component sector

A component eigenvector extends by zero to a nonzero vector in the global
defect eigenspace.  In the nonsquare branch that global eigenspace has even
dimension, hence any occurring eigenvalue has multiplicity at least two.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Nonsquare sector occurrence forces multiplicity at least two.** -/
theorem binarySquare_nonsquare_componentEigenvalue_even_global_multiplicity
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → K) (μ : K)
    (hv : (((secondOrderDefectGraph G).induce c.supp).adjMatrix K).mulVec v =
      μ • v) (hv0 : v ≠ 0)
    (hμ : μ ≠ ((q - 1 : ℕ) : K))
    (hnonsquare : ¬ IsSquare ((q : K) - 1 - μ)) :
    Even (Module.finrank K
        (defectEigenspace ((secondOrderDefectGraph G).adjMatrix K) μ)) ∧
      2 ≤ Module.finrank K
        (defectEigenspace ((secondOrderDefectGraph G).adjMatrix K) μ) := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x, D.degree x = (q - 3) + 2 := by
    intro x
    exact secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
  have hprincipal : (((q - 3) + 2 : ℕ) : K) = ((q - 1 : ℕ) : K) := by
    congr 1
    omega
  have hμ' : μ ≠ (((q - 3) + 2 : ℕ) : K) := by
    rw [hprincipal]
    exact hμ
  have heven : Even (Module.finrank K
      (defectEigenspace (D.adjMatrix K) μ)) :=
    graph_even_finrank_defectEigenspace_of_regular_excess_field
      G hfree hreg hDreg hμ' hnonsquare
  let u := connectedComponentExtend D c v
  have hu0 : u ≠ 0 := connectedComponentExtend_ne_zero D c v hv0
  have hDu : (D.adjMatrix K).mulVec u = μ • u :=
    global_adjMatrix_eigenvector_of_component_adjMatrix_eigenvector
      D c v μ hv
  have huMem : u ∈ defectEigenspace (D.adjMatrix K) μ :=
    mem_defectEigenspace_iff.mpr hDu
  have hnontrivial : Nontrivial (defectEigenspace (D.adjMatrix K) μ) := by
    refine ⟨⟨⟨u, huMem⟩, 0, ?_⟩⟩
    intro heq
    apply hu0
    exact congrArg Subtype.val heq
  have hpos : 0 < Module.finrank K
      (defectEigenspace (D.adjMatrix K) μ) :=
    Module.finrank_pos_iff.mpr hnontrivial
  refine ⟨heven, ?_⟩
  obtain ⟨k, hk⟩ := heven
  rw [hk] at hpos ⊢
  omega

end

end Erdos85
