/-
  Cyclic Vector ⟹ Nonderogatory: The Converse (OQ-02)

  The gallery proof `nonderogatory_has_cyclic_vector` shows that every
  nonderogatory matrix (minpoly = charpoly) over any field admits a cyclic
  vector. This file proves the CONVERSE, completing the textbook equivalence:

      M has a cyclic vector  ⟺  M is nonderogatory.

  ## The Converse Argument

  Suppose v is a cyclic vector for M, i.e. no nonzero polynomial of degree < n
  annihilates v. We show minpoly K M = charpoly M.

  1. **minpoly has full degree.** The minimal polynomial annihilates M, hence
     `(aeval M (minpoly K M)).mulVec v = 0`. If `deg(minpoly) < n`, the cyclic
     property forces `minpoly K M = 0`, contradicting monicity. So
     `n ≤ deg(minpoly K M)`.

  2. **minpoly = charpoly.** Cayley–Hamilton gives `minpoly K M ∣ charpoly M`,
     and `deg(charpoly) = n`. Writing `charpoly = minpoly * c`, the degree count
     `n = deg(minpoly) + deg(c)` together with `deg(minpoly) ≥ n` forces
     `deg(c) = 0`; since c is monic (quotient of monics) it equals 1, so
     `charpoly = minpoly`.

  Combined with the forward direction this yields the equivalence
  `nonderogatory_iff_exists_cyclic_vector`.

  ## Status: 0 axioms, 0 sorries
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFields

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFieldsOQ02

open Matrix Polynomial CayleyHamiltonCyclicVectorAllFields

/-- **Converse (OQ-02)**: if `v` is a cyclic vector for `M`, then `M` is
    nonderogatory, i.e. its minimal polynomial equals its characteristic
    polynomial (equivalently, `minpoly` has full degree `n`). -/
theorem cyclic_vector_implies_nonderogatory
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) {v : Fin n → K}
    (hv : IsCyclicVector M v) :
    IsNonderogatory M := by
  -- Cayley–Hamilton: minpoly divides charpoly.
  have hdvd : minpoly K M ∣ M.charpoly := minpoly.dvd K M (Matrix.aeval_self_charpoly M)
  have hμ_monic : (minpoly K M).Monic := minpoly.monic (Matrix.isIntegral M)
  have hchar_monic : M.charpoly.Monic := Matrix.charpoly_monic M
  have hchar_deg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Step 1: the minimal polynomial has degree at least n.
  have hμ_deg_ge : n ≤ (minpoly K M).natDegree := by
    by_contra h
    push_neg at h
    have hmulvec : (aeval M (minpoly K M)).mulVec v = 0 := by
      rw [minpoly.aeval K M]; simp
    exact hμ_monic.ne_zero (hv (minpoly K M) h hmulvec)
  -- Step 2: charpoly = minpoly * c with deg c = 0, so c = 1.
  obtain ⟨c, hc⟩ := hdvd
  have hμ_ne : minpoly K M ≠ 0 := hμ_monic.ne_zero
  have hc_ne : c ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc; exact hchar_monic.ne_zero hc
  have hdeg_sum : M.charpoly.natDegree = (minpoly K M).natDegree + c.natDegree := by
    rw [hc, Polynomial.natDegree_mul hμ_ne hc_ne]
  have hc_deg : c.natDegree = 0 := by omega
  have hc_monic : c.Monic := Polynomial.Monic.of_mul_monic_left hμ_monic (hc ▸ hchar_monic)
  have hc_one : c = 1 := Polynomial.eq_one_of_monic_natDegree_zero hc_monic hc_deg
  show minpoly K M = M.charpoly
  rw [hc, hc_one, mul_one]

/-- **Equivalence**: over any field, `M` is nonderogatory iff it has a cyclic
    vector. The forward direction is `nonderogatory_has_cyclic_vector`; the
    converse is `cyclic_vector_implies_nonderogatory`. -/
theorem nonderogatory_iff_exists_cyclic_vector
    {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    IsNonderogatory M ↔ ∃ v, IsCyclicVector M v := by
  constructor
  · exact nonderogatory_has_cyclic_vector M
  · rintro ⟨v, hv⟩
    exact cyclic_vector_implies_nonderogatory M hv

end CayleyHamiltonCyclicVectorAllFieldsOQ02

end
