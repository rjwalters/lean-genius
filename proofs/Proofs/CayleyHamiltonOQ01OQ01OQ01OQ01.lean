/-
# Cyclic Vector ⟺ Non-Derogatory: The Full Equivalence

## Source
Completes the cyclic-vector characterisation begun in
`cayley-hamilton-oq-01-oq-01` (the easy direction) and
`cayley-hamilton-oq-01-oq-01-oq-01` (the converse existence statement).

## What This Proves

For an `n × n` matrix `M` over a field `K`, viewing `Kⁿ` as a `K[X]`-module via
`M` (the parent's `Module.AEval'` framework), a vector `v` is **cyclic** when no
nonzero polynomial of degree `< n` annihilates it (parent's `IsCyclicVector`).

The grandparent proved the **converse existence** direction:
`minpoly K M = M.charpoly → ∃ v, IsCyclicVector M v`
(`cayley-hamilton-oq-01-oq-01-oq-01`).  This entry supplies the missing
**forward** direction and assembles the full equivalence.

**Main results:**
- `minpoly_natDegree_eq_of_isCyclicVector`:
    `IsCyclicVector M v → (minpoly K M).natDegree = n`.
- `minpoly_eq_charpoly_of_isCyclicVector`:
    `IsCyclicVector M v → minpoly K M = M.charpoly`.
- `exists_cyclicVector_iff_minpoly_eq_charpoly`:
    `(∃ v, IsCyclicVector M v) ↔ minpoly K M = M.charpoly`.
- `exists_cyclicVector_iff_minpoly_natDegree_eq`:
    `(∃ v, IsCyclicVector M v) ↔ (minpoly K M).natDegree = n`.

## Structure of the Argument

The forward direction is a clean degree squeeze, true because a cyclic vector
witnesses that nothing of small degree kills the whole orbit:

* **`deg(minpoly) ≤ n`** always: `minpoly K M ∣ M.charpoly` (Cayley–Hamilton)
  and `deg(charpoly) = n`.
* **`deg(minpoly) ≥ n`** from cyclicity: the minimal polynomial annihilates
  every vector, in particular the cyclic `v`; were its degree `< n`, the cyclic
  property would force `minpoly K M = 0`, contradicting that the minimal
  polynomial of an integral element is nonzero.

So `deg(minpoly) = n`.  Both `minpoly K M` and `M.charpoly` are monic with
`minpoly ∣ charpoly` and equal degree, hence equal
(`Polynomial.eq_of_monic_of_dvd_of_natDegree_le`).  Pairing this with the
grandparent's reverse direction yields the equivalence.

The whole development is fully machine-checked (no `sorry`, no extra axioms),
reusing the grandparent's `aeval_eq_zero_iff_mem_vecAnnIdeal` bridge and the
parent's `minpoly_mem_vecAnnIdeal`.

## Depends on
`Proofs.CayleyHamiltonOQ01OQ01OQ01` (the bridge + reverse direction) and, through
it, `Proofs.CayleyHamiltonOQ01OQ01` (the `vecAnnIdeal` / `IsCyclicVector`
framework).
-/

import Proofs.CayleyHamiltonOQ01OQ01OQ01

open Matrix Polynomial Module BigOperators
open CayleyHamiltonOQ01OQ01 CayleyHamiltonOQ01OQ01OQ01

namespace CayleyHamiltonOQ01OQ01OQ01OQ01

variable {K : Type*} [Field K] {n : ℕ}

/-! ## I. Forward direction: a cyclic vector forces a full-degree minimal polynomial -/

/-- If `M` has a cyclic vector `v`, then `(minpoly K M).natDegree = n`.

`deg(minpoly) ≤ n` because `minpoly ∣ charpoly` and `deg(charpoly) = n`;
`deg(minpoly) ≥ n` because the (nonzero) minimal polynomial annihilates `v`, so a
degree `< n` would force it to vanish by cyclicity. -/
theorem minpoly_natDegree_eq_of_isCyclicVector (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hv : IsCyclicVector M v) : (minpoly K M).natDegree = n := by
  have hM_int : IsIntegral K M :=
    ⟨M.charpoly, Matrix.charpoly_monic M, Matrix.aeval_self_charpoly M⟩
  -- deg(minpoly) ≤ n
  have hdvd : minpoly K M ∣ M.charpoly := minpoly.dvd K M (Matrix.aeval_self_charpoly M)
  have hcharne : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hle : (minpoly K M).natDegree ≤ n := by
    have h := Polynomial.natDegree_le_of_dvd hdvd hcharne
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  -- minpoly annihilates the cyclic vector v
  have hannih : aeval M.mulVecLin (minpoly K M) v = 0 :=
    (aeval_eq_zero_iff_mem_vecAnnIdeal M v (minpoly K M)).mpr (minpoly_mem_vecAnnIdeal M v)
  -- deg(minpoly) ≥ n
  have hge : n ≤ (minpoly K M).natDegree := by
    by_contra hlt
    push_neg at hlt
    exact minpoly.ne_zero hM_int (hv (minpoly K M) hlt hannih)
  exact le_antisymm hle hge

/-! ## II. Forward direction: a cyclic vector forces `minpoly = charpoly` -/

/-- If `M` has a cyclic vector, its minimal and characteristic polynomials
coincide — the forward direction of the non-derogatory characterisation. -/
theorem minpoly_eq_charpoly_of_isCyclicVector (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hv : IsCyclicVector M v) : minpoly K M = M.charpoly := by
  have hM_int : IsIntegral K M :=
    ⟨M.charpoly, Matrix.charpoly_monic M, Matrix.aeval_self_charpoly M⟩
  have hMonic : (minpoly K M).Monic := minpoly.monic hM_int
  have hdvd : minpoly K M ∣ M.charpoly := minpoly.dvd K M (Matrix.aeval_self_charpoly M)
  have hdeg : (minpoly K M).natDegree = n := minpoly_natDegree_eq_of_isCyclicVector M v hv
  have hle : M.charpoly.natDegree ≤ (minpoly K M).natDegree := by
    rw [hdeg, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hMonic (Matrix.charpoly_monic M)
    hdvd hle).symm

/-! ## III. The full equivalences -/

/-- **Cyclic vector ⟺ non-derogatory.** `M` admits a cyclic vector iff its
minimal and characteristic polynomials coincide. The forward direction is
`minpoly_eq_charpoly_of_isCyclicVector`; the reverse is the grandparent's
`exists_cyclicVector_of_minpoly_eq_charpoly`. -/
theorem exists_cyclicVector_iff_minpoly_eq_charpoly (M : Matrix (Fin n) (Fin n) K) :
    (∃ v : Fin n → K, IsCyclicVector M v) ↔ minpoly K M = M.charpoly := by
  constructor
  · rintro ⟨v, hv⟩
    exact minpoly_eq_charpoly_of_isCyclicVector M v hv
  · intro h
    exact exists_cyclicVector_of_minpoly_eq_charpoly M h

/-- **Degree form of the equivalence.** `M` admits a cyclic vector iff its
minimal polynomial has full degree `n`. -/
theorem exists_cyclicVector_iff_minpoly_natDegree_eq (M : Matrix (Fin n) (Fin n) K) :
    (∃ v : Fin n → K, IsCyclicVector M v) ↔ (minpoly K M).natDegree = n := by
  constructor
  · rintro ⟨v, hv⟩
    exact minpoly_natDegree_eq_of_isCyclicVector M v hv
  · intro h
    exact exists_cyclicVector_of_minpoly_natDegree_eq M h

end CayleyHamiltonOQ01OQ01OQ01OQ01
