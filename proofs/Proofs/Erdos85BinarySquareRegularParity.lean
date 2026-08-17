import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# Characteristic-two parity for regular square-order cores

The mod-two defect-kernel argument is not peculiar to the order-64 endpoint
or to the excess-one order.  On any even square order, an even-regular
`C₄`-free graph has a second adjacency-kernel vector, hence a nonconstant
kernel vector of `I + J + D`.  This is the uniform parity input for the
regular binary square-order branch.
-/

open SimpleGraph

namespace Erdos85

/-- **Uniform binary-square defect kernel.**  Let `G` be an even-regular
`C₄`-free graph on `q²` vertices, with `q > 0`.  Over `𝔽₂`, the matrix
`I + J + D` has a kernel vector distinct from both zero and the all-ones
vector.

The proof uses only that `q²` is even.  Thus every hypothetical regular core
in the characteristic-two square-order branch carries this extra parity
structure, independently of any finite component census. -/
theorem binarySquare_regular_exists_nontrivial_defect_kernel_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q) (heven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∃ w : V → ZMod 2, w ≠ 0 ∧ w ≠ (fun _ => 1) ∧
      ((1 : Matrix V V (ZMod 2)) + Matrix.of (fun _ _ => (1 : ZMod 2)) +
        (secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w = 0 := by
  haveI : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    positivity
  have hnEven : Even (Fintype.card V) := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k * q, ?_⟩
    rw [hcard, hk]
    ring
  have hsymm : ∀ x y : V,
      G.adjMatrix (ZMod 2) x y = G.adjMatrix (ZMod 2) y x := by
    intro x y
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hdiag : ∀ x : V, G.adjMatrix (ZMod 2) x x = 0 := by
    intro x
    rw [SimpleGraph.adjMatrix_apply, if_neg (G.loopless.irrefl x)]
  have hones := adjMatrix_zmodTwo_mulVec_ones_eq_zero G heven hreg
  obtain ⟨w, hker, hw0, hw1⟩ := exists_kernel_vector_ne_zero_ne_ones
    hnEven (G.adjMatrix (ZMod 2)) hsymm hdiag hones
  refine ⟨w, hw0, hw1, ?_⟩
  rw [← adjMatrix_sq_eq_defect_mod_two_of_even_regular G hfree heven hreg,
    ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]

end Erdos85
