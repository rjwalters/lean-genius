import Proofs.CayleyHamiltonMinpolyOQ04BackwardIncomplete01
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-
# Cyclic Vectors for Irreducible Minimal Polynomial: Full Characterization and Count

## Research Problem: cayley-hamilton-minpoly-oq-04-backward-incomplete-01-oq-01

The parent file `CayleyHamiltonMinpolyOQ04BackwardIncomplete01` proves the *one-directional*
result that if `minpoly K M` is irreducible of degree `n`, then **every nonzero** vector is a
cyclic vector for `M`. This file closes the characterization into an iff and draws the obvious
but previously unstated enumerative consequence.

## Main results

* `zero_not_cyclic` — the zero vector is never cyclic (when `n > 0`): the nonzero constant
  polynomial `1` has degree `0 < n` and annihilates `0`.
* `cyclic_iff_ne_zero` — for irreducible `minpoly K M` of degree `n` (with `n > 0`), a vector is
  cyclic **iff** it is nonzero. This sharpens the parent's one-directional theorem into a complete
  characterization.
* `setOf_cyclic_eq_compl_zero` — the set of cyclic vectors is exactly `{0}ᶜ`.
* `ncard_cyclic_vectors` — over a **finite** field `K` with `q = #K`, the number of cyclic
  vectors is exactly `qⁿ − 1` (every nonzero vector, and no others).

The characterization is sharp: combined with the parent, it says that a matrix with irreducible
minimal polynomial of full degree is "uniformly cyclic" — the cyclic-vector locus is the entire
punctured space `Kⁿ ∖ {0}`, the largest it could possibly be.

## Status (0 axioms, 0 sorries)
-/

namespace CayleyHamiltonMinpolyOQ04BackwardInc01

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- **The zero vector is never cyclic** (for `n > 0`). The constant polynomial `1` is nonzero,
has degree `0 < n`, and annihilates `0` (since `(aeval M 1).mulVec 0 = 0`), so it witnesses the
failure of the cyclic-vector condition at `v = 0`. -/
theorem zero_not_cyclic (M : Matrix (Fin n) (Fin n) K) (hn : 0 < n) :
    ¬ IsCyclicVector M (0 : Fin n → K) := by
  intro h
  have h1 : (1 : K[X]).natDegree < n := by rw [natDegree_one]; exact hn
  have hann : (aeval M (1 : K[X])).mulVec (0 : Fin n → K) = 0 := by simp
  exact one_ne_zero (h 1 h1 hann)

/-- **Full characterization (irreducible minimal polynomial of full degree).**
A vector is cyclic for `M` iff it is nonzero. The forward direction is `zero_not_cyclic`
(contrapositive); the backward direction is the parent's `cyclic_of_irreducible_minpoly`. -/
theorem cyclic_iff_ne_zero [DecidableEq K[X]] (M : Matrix (Fin n) (Fin n) K)
    (hirr : Irreducible (minpoly K M)) (hdeg : (minpoly K M).natDegree = n) (hn : 0 < n)
    (v : Fin n → K) : IsCyclicVector M v ↔ v ≠ 0 := by
  constructor
  · intro h hv0
    exact zero_not_cyclic M hn (hv0 ▸ h)
  · intro hv
    exact cyclic_of_irreducible_minpoly M hirr hdeg hv

/-- The set of cyclic vectors is exactly the complement of `{0}` — the punctured space. -/
theorem setOf_cyclic_eq_compl_zero [DecidableEq K[X]] (M : Matrix (Fin n) (Fin n) K)
    (hirr : Irreducible (minpoly K M)) (hdeg : (minpoly K M).natDegree = n) (hn : 0 < n) :
    {v : Fin n → K | IsCyclicVector M v} = ({0} : Set (Fin n → K))ᶜ := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact cyclic_iff_ne_zero M hirr hdeg hn v

/-- **Count over a finite field.** If `K` is finite with `q = #K` and `minpoly K M` is irreducible
of degree `n > 0`, the number of cyclic vectors is exactly `qⁿ − 1`: every one of the `qⁿ` vectors
is cyclic except the zero vector. -/
theorem ncard_cyclic_vectors [Fintype K] [DecidableEq K[X]] (M : Matrix (Fin n) (Fin n) K)
    (hirr : Irreducible (minpoly K M)) (hdeg : (minpoly K M).natDegree = n) (hn : 0 < n) :
    {v : Fin n → K | IsCyclicVector M v}.ncard = Fintype.card K ^ n - 1 := by
  classical
  rw [setOf_cyclic_eq_compl_zero M hirr hdeg hn, Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_compl, Set.toFinset_singleton, Finset.card_compl,
    Finset.card_singleton]
  rw [Fintype.card_fun, Fintype.card_fin]

end CayleyHamiltonMinpolyOQ04BackwardInc01

#print axioms CayleyHamiltonMinpolyOQ04BackwardInc01.cyclic_iff_ne_zero
#print axioms CayleyHamiltonMinpolyOQ04BackwardInc01.setOf_cyclic_eq_compl_zero
#print axioms CayleyHamiltonMinpolyOQ04BackwardInc01.ncard_cyclic_vectors
