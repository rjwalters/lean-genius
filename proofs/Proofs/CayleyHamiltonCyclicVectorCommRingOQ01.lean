/-
Backward direction of the Cayley-Hamilton cyclic-vector ↔ nonderogatory
biconditional, **extended from `[Field K]` to `[CommRing R] [Nontrivial R]`**.

This file does NOT modify the parent
`proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean` or its sibling
`GeneralCyclicVector` namespace (which is `Field`-locked at
`CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean:54`). Instead, it introduces
a new sibling namespace `GeneralCyclicVectorRing` over a nontrivial
commutative ring, with predicate definitions that mirror the field
versions modulo the typeclass.

The forward direction (`IsNonderogatory M → ∃ v, IsCyclicVector M v`)
**fails** over `ZMod 4` (concrete counterexample
`M = !![0, 2; 0, 0]` worked out in this slug's `knowledge.md`); the
counterexample formalisation lives in a separate companion file owned by
the S3 ACT picker.

Bearer pins (Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
- `Polynomial.minpoly.unique'`
  (`FieldTheory/Minpoly/Basic.lean:139`, in `section Ring` with `[CommRing A]`)
- `Polynomial.minpoly.monic`
  (`FieldTheory/Minpoly/Basic.lean:54`, `[CommRing A]`)
- `Polynomial.natDegree_lt_natDegree`
  (`Algebra/Polynomial/Degree/Operations.lean:73`, `[Semiring]`)
- `Matrix.charpoly_monic`
  (`LinearAlgebra/Matrix/Charpoly/Coeff.lean:117`, `[CommRing R]`)
- `Matrix.charpoly_natDegree_eq_dim`
  (`LinearAlgebra/Matrix/Charpoly/Coeff.lean:113`, `[CommRing R] [Nontrivial R]`)
- `Matrix.aeval_self_charpoly`
  (`LinearAlgebra/Matrix/Charpoly/Basic.lean`, `[CommRing R]`)
- `Matrix.zero_mulVec`
  (`Data/Matrix/Mul.lean:729`, `@[simp]`)

Note: the standard `minpoly.dvd` lemma is `Field`-only at this pin
(`FieldTheory/Minpoly/Field.lean:31` declares `variable (A) [Field A]`),
and `Polynomial.natDegree_le_of_dvd` requires `[NoZeroDivisors R]`
(`Algebra/Polynomial/Degree/Domain.lean:33`). This file therefore avoids
both and proves the backward direction directly via `minpoly.unique'`,
which holds over any `[CommRing A]`.
-/

import Mathlib

noncomputable section

open Matrix Polynomial

namespace GeneralCyclicVectorRing

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- A vector `v : Fin n → R` is cyclic for `M : Matrix (Fin n) (Fin n) R`
if every `R`-polynomial `p` of `natDegree < n` whose evaluation at `M`
sends `v` to zero must itself be the zero polynomial. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Prop :=
  ∀ p : R[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- A matrix is nonderogatory if its minimal polynomial equals its
characteristic polynomial. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) R) : Prop :=
  minpoly R M = M.charpoly

end GeneralCyclicVectorRing

namespace CayleyHamiltonCyclicVectorCommRingOQ01

open GeneralCyclicVectorRing

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- Backward direction over a nontrivial commutative ring: the existence
of a cyclic vector for `M` forces the minimal polynomial of `M` to equal
its characteristic polynomial. -/
theorem cyclic_implies_nonderogatory_commring
    (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
    (hcyc : IsCyclicVector M v) :
    IsNonderogatory M := by
  unfold IsNonderogatory
  have hchar_monic : M.charpoly.Monic := M.charpoly_monic
  have hchar_aeval : aeval M M.charpoly = 0 := M.aeval_self_charpoly
  have hchar_deg : M.charpoly.natDegree = n := by
    rw [M.charpoly_natDegree_eq_dim, Fintype.card_fin]
  refine (minpoly.unique' R M hchar_monic hchar_aeval ?_).symm
  intro q hqdeg
  by_cases hq : q = 0
  · exact Or.inl hq
  · refine Or.inr (fun hae => hq ?_)
    have hndlt : q.natDegree < n := by
      have := Polynomial.natDegree_lt_natDegree hq hqdeg
      simpa [hchar_deg] using this
    apply hcyc q hndlt
    rw [hae]
    exact Matrix.zero_mulVec v

end CayleyHamiltonCyclicVectorCommRingOQ01
