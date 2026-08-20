import Proofs.Erdos85SquareOrderSectorProfile
import Proofs.Erdos85SquareOrderNonexistenceReduction

/-! # Odd square order has no regular horn

Node: B.3 / GAP B-CLASSIFY.  At order `d^2`, a `d`-regular graph has odd
total degree when `d` is odd, contradicting the handshake lemma.  Thus the
uniform square-order regular/nonregular split collapses to the nonregular
sector, whose high-vertex count is itself odd.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A graph of odd order `d^2` cannot be `d`-regular when `d` is odd. -/
theorem odd_squareOrder_not_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hodd : Odd d) (hcard : Fintype.card V = d * d)
    (hreg : ∀ x : V, G.degree x = d) : False := by
  have hsum : (∑ x : V, G.degree x) = d * d * d := by
    simp_rw [hreg]
    simp [hcard]
  have hhand := G.sum_degrees_eq_twice_card_edges
  have heven : Even (d * d * d) := by
    refine ⟨G.edgeFinset.card, ?_⟩
    rw [← hsum]
    simpa [two_mul] using hhand
  have hoddCube : Odd (d * d * d) := (hodd.mul hodd).mul hodd
  exact (Nat.not_even_iff_odd.mpr hoddCube) heven

/-- For odd `d`, every normalized square-order core belongs to the
nonregular sector; the regular alternative is arithmetically impossible. -/
theorem odd_squareOrder_nonregularSectorProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hodd : Odd d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    SquareOrderNonregularSectorProfile G d := by
  rcases squareOrder_regular_or_nonregularSectorProfile
    G hfree hd hmin hcover hcard with hreg | hprofile
  · exact (odd_squareOrder_not_regular G hodd hcard hreg).elim
  · exact hprofile

/-- The high sector of an odd square-order normalized core has odd
cardinality (and hence is automatically nonempty). -/
theorem odd_squareOrder_high_card_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hodd : Odd d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    Odd (squareOrderHighVertices G d).card := by
  have hparity := (odd_squareOrder_nonregularSectorProfile
    G hfree hd hodd hmin hcover hcard).high_parity
  rw [← Nat.not_even_iff_odd]
  intro hhighEven
  have hoddCube : Odd (d * d * d) := (hodd.mul hodd).mul hodd
  have hsumOdd := hoddCube.add_even hhighEven
  exact (Nat.not_even_iff_odd.mpr hsumOdd) hparity

/-- Tight-minimizer packaging of the odd-parameter reduction. -/
theorem SquareOrderTightMinimizer.exists_odd_nonregularSectorProfile
    {d : ℕ} (hd : 2 ≤ d) (hodd : Odd d)
    (hminimizer : SquareOrderTightMinimizer d) :
    ∃ (G : SimpleGraph (Fin (d * d))) (_ : DecidableRel G.Adj),
      SquareOrderNonregularSectorProfile G d ∧
        Odd (squareOrderHighVertices G d).card := by
  classical
  rcases hminimizer with ⟨G, hdec, hfree, hmin, _hminimal, hcover⟩
  letI : DecidableRel G.Adj := hdec
  have hmindeg : ∀ x : Fin (d * d), d ≤ G.degree x := fun x =>
    hmin.trans (G.minDegree_le_degree x)
  have hprofile := odd_squareOrder_nonregularSectorProfile
    G hfree hd hodd hmindeg (@hcover) (by simp)
  refine ⟨G, hdec, hprofile, ?_⟩
  exact odd_squareOrder_high_card_odd
    G hfree hd hodd hmindeg (@hcover) (by simp)

end

end Erdos85

#print axioms Erdos85.odd_squareOrder_not_regular
#print axioms Erdos85.odd_squareOrder_nonregularSectorProfile
#print axioms Erdos85.odd_squareOrder_high_card_odd
#print axioms
  Erdos85.SquareOrderTightMinimizer.exists_odd_nonregularSectorProfile
