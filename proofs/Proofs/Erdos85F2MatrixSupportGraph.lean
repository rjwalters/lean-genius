import Proofs.Erdos85BinaryCutGraphTwoPoleRoute

/-!
# Support graph of a binary matrix

A symmetric zero-diagonal matrix over F₂ is exactly the adjacency matrix of
a simple graph.  This file packages that representation and transfers a
zero row-sum into Eulerian degree parity.  It is the representation bridge
needed for the Baer transport matrices `H` and `K`.
-/

open SimpleGraph

namespace Erdos85

/-- The simple graph supported by the one-entries of a symmetric binary
matrix. -/
def f2MatrixSupportGraph
    {V : Type*} (M : Matrix V V (ZMod 2))
    (hsymm : ∀ x y, M x y = M y x)
    (hdiag : ∀ x, M x x = 0) : SimpleGraph V where
  Adj x y := M x y = 1
  symm := by
    constructor
    intro x y hxy
    rw [← hsymm]
    exact hxy
  loopless := by
    constructor
    intro x hx
    rw [hdiag] at hx
    exact zero_ne_one hx

instance f2MatrixSupportGraph_decidableAdj
    {V : Type*} (M : Matrix V V (ZMod 2))
    (hsymm : ∀ x y, M x y = M y x)
    (hdiag : ∀ x, M x x = 0) :
    DecidableRel (f2MatrixSupportGraph M hsymm hdiag).Adj := by
  intro x y
  change Decidable (M x y = 1)
  infer_instance

/-- Recover the original matrix as the F₂ adjacency matrix of its support
graph. -/
theorem f2MatrixSupportGraph_adjMatrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V (ZMod 2))
    (hsymm : ∀ x y, M x y = M y x)
    (hdiag : ∀ x, M x x = 0) :
    (f2MatrixSupportGraph M hsymm hdiag).adjMatrix (ZMod 2) = M := by
  ext x y
  simp only [SimpleGraph.adjMatrix_apply, f2MatrixSupportGraph]
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbinary (M x y) with hzero | hone
  · have hne : ¬ M x y = 1 := by
      intro h
      rw [hzero] at h
      exact zero_ne_one h
    rw [if_neg hne, hzero]
  · rw [if_pos hone, hone]

/-- If the binary matrix kills the all-ones vector, its support graph has
even degree at every vertex. -/
theorem f2MatrixSupportGraph_even_degree_of_mulVec_one_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V (ZMod 2))
    (hsymm : ∀ x y, M x y = M y x)
    (hdiag : ∀ x, M x x = 0)
    (hzero : M.mulVec (fun _ => 1) = 0) (v : V) :
    Even ((f2MatrixSupportGraph M hsymm hdiag).degree v) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  let H := f2MatrixSupportGraph M hsymm hdiag
  have hsupport : f2PotentialSupport (fun _ : V => (1 : ZMod 2)) = Finset.univ := by
    ext x
    simp [f2PotentialSupport]
  calc
    (((H.degree v : ℕ) : ZMod 2)) =
        ((H.neighborFinset v ∩ f2PotentialSupport
          (fun _ : V => (1 : ZMod 2))).card : ZMod 2) := by
      rw [hsupport, Finset.inter_univ, H.card_neighborFinset_eq_degree]
    _ = (H.adjMatrix (ZMod 2)).mulVec (fun _ => 1) v :=
      f2Potential_neighborSupport_card_cast H (fun _ => 1) v
    _ = M.mulVec (fun _ => 1) v := by
      rw [f2MatrixSupportGraph_adjMatrix_eq]
    _ = 0 := by rw [hzero]; rfl

end Erdos85

#print axioms Erdos85.f2MatrixSupportGraph_adjMatrix_eq
#print axioms Erdos85.f2MatrixSupportGraph_even_degree_of_mulVec_one_eq_zero
