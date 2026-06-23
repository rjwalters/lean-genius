/-
  Cyclic Vector Theorem — Full Biconditional (Converse Direction)
  (cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01)

  The parent theorem (CayleyHamiltonCyclicVectorAllFields.lean) proves:
    IsNonderogatory M → ∃ v, IsCyclicVector M v

  This file proves the CONVERSE:
    IsCyclicVector M v → IsNonderogatory M

  Combined, this gives the full biconditional:
    IsNonderogatory M ↔ ∃ v, IsCyclicVector M v

  ## Proof of the Converse

  Given a cyclic vector v for M (n×n matrix over field K), we show minpoly K M = M.charpoly:

  1. minpoly K M ∣ M.charpoly  (Cayley-Hamilton via minpoly.dvd)
  2. deg(minpoly) ≤ n          (from divisibility and deg(charpoly) = n)
  3. deg(minpoly) ≥ n          (the cyclic condition forces this:
     if deg(minpoly) < n then hcyc gives minpoly = 0, contradicting ne_zero)
  4. deg(minpoly) = n, both monic, minpoly | charpoly → minpoly = charpoly
     (extract quotient r, show r monic of degree 0, hence r = 1)

  ## Status: 0 sorries, 0 axioms
-/
import Mathlib
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04
import Proofs.CayleyHamiltonCyclicVectorAllFields

noncomputable section

namespace CyclicVectorBiconditional

open Matrix Polynomial GeneralCyclicVector

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Main Converse: Cyclic Vector Implies Nonderogatory -/

/-- If M has a cyclic vector then M is nonderogatory: minpoly K M = M.charpoly.

    Key insight: a cyclic vector forces deg(minpoly) ≥ n, since if deg(minpoly) < n
    the cyclic condition would require minpoly = 0, contradicting nonvanishing. -/
theorem cyclic_implies_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) :
    IsNonderogatory M := by
  -- IsNonderogatory M := minpoly K M = M.charpoly
  unfold IsNonderogatory
  -- Step 1: minpoly | charpoly via Cayley-Hamilton
  have hdvd : minpoly K M ∣ M.charpoly :=
    minpoly.dvd K M (Matrix.aeval_self_charpoly M)
  -- Step 2: charpoly facts
  have hchar_monic : M.charpoly.Monic := Matrix.charpoly_monic M
  have hchar_ne : M.charpoly ≠ 0 := hchar_monic.ne_zero
  have hchar_deg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Step 3: deg(minpoly) ≤ n (from divisibility)
  have hle : (minpoly K M).natDegree ≤ n := by
    have h := Polynomial.natDegree_le_of_dvd hdvd hchar_ne
    linarith [hchar_deg]
  -- Step 4: deg(minpoly) ≥ n using the cyclic vector
  -- minpoly(M) sends every vector to 0 (it annihilates M as an algebra element)
  have hann : (aeval M (minpoly K M)).mulVec v = 0 := by
    have h : aeval M (minpoly K M) = 0 := minpoly.aeval K M
    rw [h]; exact Matrix.zero_mulVec v
  -- If deg < n, cyclic condition forces minpoly = 0 — contradiction
  have hge : n ≤ (minpoly K M).natDegree := by
    by_contra hlt
    push_neg at hlt
    exact absurd (hcyc (minpoly K M) hlt hann) (minpoly.ne_zero (Matrix.isIntegral M))
  -- Step 5: degrees are equal
  have hdeg : (minpoly K M).natDegree = n := Nat.le_antisymm hle hge
  -- Step 6: Both monic of degree n with minpoly | charpoly → minpoly = charpoly
  -- Extract quotient r with M.charpoly = minpoly K M * r
  obtain ⟨r, hr⟩ := hdvd
  -- r is monic (quotient of two monic polynomials)
  have hr_monic : r.Monic :=
    Polynomial.Monic.of_mul_monic_left (minpoly.monic (Matrix.isIntegral M)) (hr ▸ hchar_monic)
  -- r has degree 0 (degrees sum to n, minpoly already has degree n)
  have hr_natdeg : r.natDegree = 0 := by
    have hmul : (minpoly K M * r).natDegree = (minpoly K M).natDegree + r.natDegree :=
      Polynomial.natDegree_mul (minpoly.ne_zero (Matrix.isIntegral M)) hr_monic.ne_zero
    have hprod_deg : (minpoly K M * r).natDegree = n := by rw [← hr, hchar_deg]
    linarith [hdeg]
  -- r = 1 (monic constant polynomial)
  have hr_eq : r = 1 := by
    have h0 := Polynomial.eq_C_of_natDegree_eq_zero hr_natdeg
    have h1 : r.coeff 0 = 1 := by
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hr_natdeg] at hr_monic
      exact hr_monic
    rw [h0, h1, map_one]
  -- Conclude: minpoly K M = M.charpoly
  rw [hr, hr_eq, mul_one]

/-! ## Full Biconditional -/

/-- **Full Biconditional**: A matrix over any field is nonderogatory
    if and only if it has a cyclic vector.

    This combines the parent theorem (nonderogatory → cyclic vector, proved in
    CayleyHamiltonCyclicVectorAllFields.lean using primary decomposition) with
    the converse (cyclic vector → nonderogatory, proved above). -/
theorem nonderogatory_iff_has_cyclic_vector
    (M : Matrix (Fin n) (Fin n) K) :
    IsNonderogatory M ↔ ∃ v, IsCyclicVector M v := by
  constructor
  · intro h
    exact CayleyHamiltonCyclicVectorAllFields.nonderogatory_has_cyclic_vector M h
  · rintro ⟨v, hcyc⟩
    exact cyclic_implies_nonderogatory M v hcyc

/-! ## Corollary: Derogatory Matrices Have No Cyclic Vector -/

/-- A derogatory matrix (minpoly ≠ charpoly) has no cyclic vector. -/
theorem derogatory_has_no_cyclic_vector
    (M : Matrix (Fin n) (Fin n) K)
    (hder : ¬IsNonderogatory M) :
    ∀ v, ¬IsCyclicVector M v :=
  fun v hcyc => hder (cyclic_implies_nonderogatory M v hcyc)

/-! ## Degree Characterization -/

/-- The minimal polynomial of a matrix with a cyclic vector has degree n. -/
theorem minpoly_natDegree_of_cyclic
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) :
    (minpoly K M).natDegree = n := by
  have hnd := cyclic_implies_nonderogatory M v hcyc
  unfold IsNonderogatory at hnd
  rw [hnd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

end CyclicVectorBiconditional

end
