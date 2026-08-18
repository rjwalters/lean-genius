import Proofs.Erdos85CommutingSignedNegativeEigenline

/-!
# Bipartite regular graphs carry the signed negative-degree eigenvector

A proper Boolean colouring of a regular graph gives the alternating vector
with values `+1` and `-1`.  Every neighbour has the opposite sign, so this vector belongs to
the negative-degree eigenspace.  For a connected graph, any commuting graph
operator therefore acts on it by an integral scalar.
-/

open SimpleGraph Matrix

namespace Erdos85

/-- The integer sign attached to a Boolean colour. -/
def boolColorSign (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem boolColorSign_eq_one_or_neg_one (b : Bool) :
    boolColorSign b = -1 ∨ boolColorSign b = 1 := by
  cases b <;> simp [boolColorSign]

theorem boolColorSign_eq_neg_of_ne {a b : Bool} (h : a ≠ b) :
    boolColorSign a = -boolColorSign b := by
  cases a <;> cases b <;> simp_all [boolColorSign]

/-- A proper Boolean colouring of a `k`-regular graph supplies its signed
negative-degree eigenvector. -/
theorem bipartiteRegular_boolColorSign_negativeDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (k : ℕ) (hreg : ∀ x, H.degree x = k)
    (col : V → Bool) (hcol : ∀ x y, H.Adj x y → col x ≠ col y) :
    ∀ x, ∑ y ∈ H.neighborFinset x, boolColorSign (col y) =
      -(k : ℤ) * boolColorSign (col x) := by
  intro x
  calc
    ∑ y ∈ H.neighborFinset x, boolColorSign (col y) =
        ∑ _y ∈ H.neighborFinset x, -boolColorSign (col x) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact boolColorSign_eq_neg_of_ne
        (hcol y x ((H.mem_neighborFinset x y).mp hy).symm)
    _ = ((H.neighborFinset x).card : ℤ) * -boolColorSign (col x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = -(k : ℤ) * boolColorSign (col x) := by
      rw [H.card_neighborFinset_eq_degree, hreg]
      ring

/-- A commuting adjacency operator acts integrally on the alternating line
of a connected bipartite regular graph. -/
theorem commutingGraph_exists_eigenvalue_on_bipartiteRegular_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (H D : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel D.Adj]
    (hconn : H.Connected) (k : ℕ) (hreg : ∀ x, H.degree x = k)
    (col : V → Bool) (hcol : ∀ x y, H.Adj x y → col x ≠ col y)
    (hcomm : D.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∃ mu : ℤ,
      (D.adjMatrix ℤ).mulVec (fun x => boolColorSign (col x)) =
        mu • (fun x => boolColorSign (col x)) := by
  exact commutingGraph_exists_eigenvalue_on_signed_negativeDegree_line
    H D hconn k hreg (fun x => boolColorSign (col x))
    (fun x => boolColorSign_eq_one_or_neg_one (col x))
    (bipartiteRegular_boolColorSign_negativeDegree H k hreg col hcol) hcomm

end Erdos85

#print axioms Erdos85.bipartiteRegular_boolColorSign_negativeDegree
#print axioms Erdos85.commutingGraph_exists_eigenvalue_on_bipartiteRegular_sign
