/-
# Existence of a Cyclic Vector in the Non-Derogatory Case

## Source
Open question from `cayley-hamilton-oq-01-oq-01` (OQ[0]):
> Prove existence of a cyclic vector when the minimal and characteristic
> polynomials coincide (the non-derogatory case).

## What This Proves

For an `n × n` matrix `M` over a field `K`, viewing `Kⁿ` as a `K[X]`-module via
`M` (the parent's `Module.AEval'` framework), a vector `v` is **cyclic** when no
nonzero polynomial of degree `< n` annihilates it (parent's `IsCyclicVector`).

The non-derogatory hypothesis is `minpoly K M = M.charpoly`, equivalently
`(minpoly K M).natDegree = n` (since `M.charpoly.natDegree = n`).

**Main results:**
- `exists_cyclicVector_of_minpoly_natDegree_eq`:
    `(minpoly K M).natDegree = n → ∃ v, IsCyclicVector M v`.
- `exists_cyclicVector_of_minpoly_eq_charpoly`:
    `minpoly K M = M.charpoly → ∃ v, IsCyclicVector M v`.

## Structure of the Argument

The whole statement reduces to a single **general** module-theoretic fact
(true for *every* `M`, derogatory or not):

  `exists_vecAnnIdeal_eq_minpoly`:
    `∃ v, vecAnnIdeal M v = Ideal.span {minpoly K M}`.

This is the classical *existence of a vector of maximal order* — a vector whose
annihilator ideal is exactly the minimal polynomial (the module's exponent). It
holds in any finitely generated module over the PID `K[X]`, and is supplied by
Mathlib's `Module.exists_ker_toSpanSingleton_eq_annihilator` (a corollary of the
PID structure theorem) applied to the finite `K[X]`-module `Module.AEval' M.mulVecLin`.

Given such a `v`, the reduction is elementary: if a polynomial `p` with
`p.natDegree < n` kills `v`, then `p ∈ vecAnnIdeal M v = span {minpoly K M}`, so
`minpoly K M ∣ p`; but `(minpoly K M).natDegree = n > p.natDegree` forces `p = 0`.
Hence `v` is cyclic.

The whole development is fully machine-checked (no `sorry`, no extra axioms) against
the parent's annihilator infrastructure.

## Depends on
`Proofs.CayleyHamiltonOQ01OQ01` (the `vecAnnIdeal` / `IsCyclicVector` framework) and
Mathlib's `Module.exists_ker_toSpanSingleton_eq_annihilator` (PID structure theorem).
-/

import Proofs.CayleyHamiltonOQ01OQ01
import Mathlib.Algebra.Module.PID

open Matrix Polynomial Module BigOperators
open CayleyHamiltonOQ01OQ01

namespace CayleyHamiltonOQ01OQ01OQ01

variable {K : Type*} [Field K] {n : ℕ}

/-! ## I. Bridging aeval-annihilation and the vector annihilator ideal -/

/-- A polynomial `p` annihilates `v` under the `M`-action (`p(M)·v = 0`) iff it
lies in the vector annihilator ideal `vecAnnIdeal M v`.  Mirrors the parent's
membership/aeval translation through the `Module.AEval'` equivalence. -/
theorem aeval_eq_zero_iff_mem_vecAnnIdeal (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (p : K[X]) : aeval M.mulVecLin p v = 0 ↔ p ∈ vecAnnIdeal M v := by
  rw [mem_vecAnnIdeal_iff]
  constructor
  · intro h
    apply (Module.AEval'.of M.mulVecLin).symm.injective
    simp only [LinearEquiv.map_zero, Module.AEval.of_symm_smul, LinearEquiv.symm_apply_apply]
    exact h
  · intro h
    have h2 := congr_arg (Module.AEval'.of M.mulVecLin).symm h
    simpa only [LinearEquiv.map_zero, Module.AEval.of_symm_smul,
                LinearEquiv.symm_apply_apply] using h2

/-! ## II. The reduction: a maximal-order vector is cyclic -/

/-- If `v` realizes the minimal polynomial as its order
(`vecAnnIdeal M v = span {minpoly K M}`) and the minimal polynomial has full
degree `n`, then `v` is a cyclic vector.

Proof: a degree-`< n` polynomial `p` killing `v` lies in `span {minpoly K M}`, so
`minpoly K M ∣ p`; a nonzero such `p` would have degree `≥ n`, contradiction. -/
theorem isCyclicVector_of_vecAnnIdeal_eq_minpoly (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hv : vecAnnIdeal M v = Ideal.span {minpoly K M})
    (hM : (minpoly K M).natDegree = n) : IsCyclicVector M v := by
  intro p hp hpv
  have hmem : p ∈ vecAnnIdeal M v := (aeval_eq_zero_iff_mem_vecAnnIdeal M v p).mp hpv
  rw [hv, Ideal.mem_span_singleton] at hmem
  by_contra hpne
  have hle : (minpoly K M).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd hmem hpne
  rw [hM] at hle
  exact absurd hp (not_lt.mpr hle)

/-! ## III. Existence of a vector of maximal order -/

/-- **Existence of a vector of maximal order.** For every `M`, some vector `v`
has annihilator ideal exactly `Ideal.span {minpoly K M}` — i.e. its order is the
minimal polynomial.  This is the classical structure-theoretic fact that a
finitely generated `K[X]`-module contains an element whose order equals the
module exponent.

Proof: Mathlib's `Module.exists_ker_toSpanSingleton_eq_annihilator` (the PID
structure theorem applied to the finite `K[X]`-module `Module.AEval' M.mulVecLin`)
hands us a single `x` whose cyclic-submodule annihilator equals the whole module's
annihilator.  The parent's `kn_module_annihilator_eq_minpoly` identifies that module
annihilator with `Ideal.span {minpoly K M}`; transporting `x` back along the
`Module.AEval'.of` equivalence and unwinding `vecAnnIdeal` (= the annihilator of the
cyclic submodule, both characterised by `r • x = 0`) closes the goal. -/
theorem exists_vecAnnIdeal_eq_minpoly (M : Matrix (Fin n) (Fin n) K) :
    ∃ v : Fin n → K, vecAnnIdeal M v = Ideal.span {minpoly K M} := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator
    (R := K[X]) (M := Module.AEval' M.mulVecLin)
  refine ⟨(Module.AEval'.of M.mulVecLin).symm x, ?_⟩
  rw [kn_module_annihilator_eq_minpoly M, ← hx]
  ext r
  rw [mem_vecAnnIdeal_iff, LinearEquiv.apply_symm_apply, LinearMap.mem_ker]
  rfl

/-! ## IV. Main theorems -/

/-- **Cyclic vector in the non-derogatory case (degree form).**
If `(minpoly K M).natDegree = n`, then `M` admits a cyclic vector. -/
theorem exists_cyclicVector_of_minpoly_natDegree_eq (M : Matrix (Fin n) (Fin n) K)
    (hM : (minpoly K M).natDegree = n) : ∃ v : Fin n → K, IsCyclicVector M v := by
  obtain ⟨v, hv⟩ := exists_vecAnnIdeal_eq_minpoly M
  exact ⟨v, isCyclicVector_of_vecAnnIdeal_eq_minpoly M v hv hM⟩

/-- **Cyclic vector in the non-derogatory case.**
If the minimal and characteristic polynomials coincide, then `M` admits a cyclic
vector — the converse direction of the cyclic-vector ⟺ `μ = χ` equivalence. -/
theorem exists_cyclicVector_of_minpoly_eq_charpoly (M : Matrix (Fin n) (Fin n) K)
    (hM : minpoly K M = M.charpoly) : ∃ v : Fin n → K, IsCyclicVector M v := by
  apply exists_cyclicVector_of_minpoly_natDegree_eq
  rw [hM, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

end CayleyHamiltonOQ01OQ01OQ01
