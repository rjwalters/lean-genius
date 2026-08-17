import Proofs.Erdos85AlternatingParity
import Mathlib

/-!
# Adjacency characteristic polynomials in characteristic two

On an even vertex set, the characteristic polynomial over `𝔽₂` of a simple
graph adjacency matrix is a square.  The key point is that every odd-order
principal adjacency minor is alternating and hence singular in characteristic
two.  Consequently every odd-degree characteristic coefficient vanishes.

This is the first half of the proposed uniform binary regular-sector
obstruction: the square-order defect identity can transport this square
polynomial constraint to the defect graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On an even vertex type, every odd-degree coefficient of the mod-two
adjacency characteristic polynomial vanishes. -/
theorem adjMatrix_charpoly_odd_coeff_eq_zero_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Even (Fintype.card V)) {j : ℕ} (hj : Odd j) :
    (G.adjMatrix (ZMod 2)).charpoly.coeff j = 0 := by
  classical
  by_cases hjle : j ≤ Fintype.card V
  · let k := Fintype.card V - j
    have hk : k ≤ Fintype.card V := Nat.sub_le _ _
    have hjrepr : Fintype.card V - k = j := by
      simp only [k]
      omega
    have hkodd : Odd k := by
      obtain ⟨a, ha⟩ := hcard
      obtain ⟨b, hb⟩ := hj
      refine ⟨a - b - 1, ?_⟩
      simp only [k, ha, hb]
      omega
    rw [← hjrepr,
      Matrix.charpoly_coeff_eq_sum_minors (G.adjMatrix (ZMod 2)) k hk]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro s hs
    have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
    apply det_eq_zero_of_symm_diag_zero_of_odd_card
    · simpa [Fintype.card_coe, hscard] using hkodd
    · intro x y
      simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
      by_cases h : G.Adj x.1 y.1
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    · intro x
      simp [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply,
        G.loopless.irrefl]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa using (lt_of_not_ge hjle))

/-- The derivative of an even-order mod-two adjacency characteristic
polynomial is zero. -/
theorem adjMatrix_charpoly_derivative_eq_zero_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Even (Fintype.card V)) :
    (G.adjMatrix (ZMod 2)).charpoly.derivative = 0 := by
  ext j
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero]
  by_cases hj : Odd (j + 1)
  · simp [adjMatrix_charpoly_odd_coeff_eq_zero_zmodTwo G hcard hj]
  · have heven : Even (j + 1) := Nat.not_odd_iff_even.mp hj
    obtain ⟨k, hk⟩ := heven
    have hscalar : (j : ZMod 2) + 1 = 0 := by
      calc
        (j : ZMod 2) + 1 = ((j + 1 : ℕ) : ZMod 2) := by push_cast; rfl
        _ = ((k + k : ℕ) : ZMod 2) := by rw [hk]
        _ = 0 := by
          push_cast
          have hadd : ∀ x : ZMod 2, x + x = 0 := by decide
          exact hadd _
    rw [hscalar, mul_zero]

/-- On an even vertex type, the mod-two adjacency characteristic polynomial
is a polynomial square. -/
theorem adjMatrix_charpoly_isSquare_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Even (Fintype.card V)) :
    ∃ p : Polynomial (ZMod 2),
      (G.adjMatrix (ZMod 2)).charpoly = p ^ 2 := by
  let f := (G.adjMatrix (ZMod 2)).charpoly
  let p := Polynomial.contract 2 f
  refine ⟨p, ?_⟩
  have hexpand : Polynomial.expand (ZMod 2) 2 p = f :=
    Polynomial.expand_contract' 2
      (adjMatrix_charpoly_derivative_eq_zero_zmodTwo G hcard)
  have hfrob := Polynomial.map_frobenius_expand (R := ZMod 2) 2 p
  rw [hexpand] at hfrob
  simpa [f, p, frobenius_def] using hfrob

end

end Erdos85
