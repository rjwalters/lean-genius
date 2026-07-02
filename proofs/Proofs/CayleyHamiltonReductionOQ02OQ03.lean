import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Proofs.CayleyHamiltonReductionOQ02OQ01
import Mathlib.Tactic

/-
# Cyclic vectors and non-derogatory matrices

The parent entry `cayley-hamilton-reduction-oq-02` establishes the
**non-derogatory criterion**: an `n × n` matrix `M` satisfies
`minpoly M = charpoly M` exactly when its minimal polynomial attains the maximal
degree `n`.  Its sibling `oq-02-oq-01` builds the **companion matrix** `C(p)` of a
monic polynomial and proves `minpoly (C p) = charpoly (C p) = p`, i.e. companion
matrices are the archetypal non-derogatory matrices.

This entry connects that criterion to **cyclic vectors**.  A vector `v` is *cyclic*
for `M` when its Krylov orbit `{v, M v, M² v, …, Mⁿ⁻¹ v}` is linearly independent
— equivalently (being `n` vectors in the `n`-dimensional space `Fin n → F`) when it
spans the whole space.  The classical fact is:

  `M` has a cyclic vector  ⟺  `M` is non-derogatory.

## What is proved here

* `eq_zero_of_aeval_mulVec_eq_zero` — the engine: if `v` is cyclic then no nonzero
  polynomial of degree `< n` can send `v` to `0` under `p(M)`.  This is exactly the
  statement that the Krylov orbit is linearly independent, read polynomially.
* `isNonDerogatory_of_hasCyclicVector` — **the forward implication in full
  generality**: a cyclic vector forces `minpoly M = charpoly M`.  The minimal
  polynomial annihilates `v`, so by the engine it cannot have degree `< n`; combined
  with `deg (minpoly) ≤ deg (charpoly) = n` this pins the degree at `n`, whence the
  two monic polynomials coincide.
* `span_eq_top_of_isCyclicVector` — the Krylov orbit of a cyclic vector spans the
  whole space, matching the textbook "spanning" phrasing.
* `companionMatrix_isCyclicVector` — **the reverse implication on the normal-form
  representatives**: the standard basis vector `e₀` is an explicit cyclic vector for
  every companion matrix `C(p)`, because `C(p)ᵏ · e₀ = eₖ` (from `oq-02-oq-01`'s
  `companionMatrix_pow_basis`).
* `companionMatrix_isNonDerogatory` — the two combine: `C(p)` is non-derogatory,
  re-derived through its cyclic vector (consistent with the direct
  `minpoly = charpoly = p`).

## Scope

The forward direction (`cyclic ⇒ non-derogatory`) is proved for an arbitrary matrix.
The reverse direction (`non-derogatory ⇒ cyclic`) is proved here for the companion
(rational canonical form) representatives.  Upgrading the reverse to an *arbitrary*
non-derogatory matrix requires the rational canonical form — that every such matrix
is *similar* to a single companion block — which is not yet available in Mathlib and
is left as the remaining step.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open Matrix Polynomial BigOperators
open CayleyHamiltonReductionOQ02OQ01

namespace CayleyHamiltonReductionOQ02OQ03

variable {F : Type*} [Field F]

/-- The **Krylov orbit** of a matrix `M` at a vector `v`: the family `k ↦ Mᵏ v`
indexed by `k : Fin n`.  These are the `n` vectors `v, M v, …, Mⁿ⁻¹ v`. -/
def krylov {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F) : Fin n → (Fin n → F) :=
  fun k => (M ^ (k : ℕ)) *ᵥ v

/-- `v` is a **cyclic vector** for `M` when its Krylov orbit is linearly independent.
Since there are `n` vectors in the `n`-dimensional space `Fin n → F`, this is
equivalent to the orbit spanning the whole space (`span_eq_top_of_isCyclicVector`). -/
def IsCyclicVector {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F) : Prop :=
  LinearIndependent F (krylov M v)

/-- `M` **has a cyclic vector** when some `v` is cyclic for it. -/
def HasCyclicVector {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∃ v, IsCyclicVector M v

/-- `M` is **non-derogatory**: its minimal polynomial equals its characteristic
polynomial (equivalently `deg (minpoly M) = n`). -/
def IsNonDerogatory {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Prop :=
  minpoly F M = M.charpoly

/-- `mulVec` distributes over a finite sum of matrices. -/
private theorem sum_mulVec {n : ℕ} (s : Finset ℕ)
    (f : ℕ → Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    (∑ i ∈ s, f i) *ᵥ v = ∑ i ∈ s, f i *ᵥ v := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' has ih =>
      rw [Finset.sum_insert has, Matrix.add_mulVec, ih, Finset.sum_insert has]

/-- **The engine.** If `v` is a cyclic vector for `M`, then a polynomial of degree
`< n` whose evaluation `p(M)` annihilates `v` must be the zero polynomial.

Equivalently: linear independence of `{v, M v, …, Mⁿ⁻¹ v}` says that the only
`F`-combination `∑ cₖ Mᵏ v` equal to `0` is the trivial one — and `p(M) v` is
exactly such a combination with `cₖ = p.coeff k`. -/
theorem eq_zero_of_aeval_mulVec_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    {v : Fin n → F} (hv : IsCyclicVector M v) {p : F[X]} (hdeg : p.natDegree < n)
    (hp : (aeval M p) *ᵥ v = 0) : p = 0 := by
  -- Expand `p(M) v` as an `F`-combination of the Krylov orbit.
  have hexp : (aeval M p) *ᵥ v = ∑ k : Fin n, p.coeff (k : ℕ) • krylov M v k := by
    rw [Polynomial.aeval_eq_sum_range' (n := n) hdeg M, sum_mulVec,
      ← Fin.sum_univ_eq_sum_range (fun k => (p.coeff k • M ^ k) *ᵥ v) n]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [krylov, Matrix.smul_mulVec]
  have hsum : ∑ k : Fin n, p.coeff (k : ℕ) • krylov M v k = 0 := hexp ▸ hp
  -- Linear independence forces every coefficient (up to index `n`) to vanish.
  have hcoeff : ∀ k : Fin n, p.coeff (k : ℕ) = 0 :=
    Fintype.linearIndependent_iff.mp hv (fun k => p.coeff (k : ℕ)) hsum
  apply Polynomial.ext
  intro m
  rw [Polynomial.coeff_zero]
  by_cases hm : m < n
  · exact hcoeff ⟨m, hm⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Forward implication (general).** If `M` has a cyclic vector, then `M` is
non-derogatory: `minpoly M = charpoly M`.

The minimal polynomial `μ` annihilates `M`, hence annihilates `v`; by the engine it
cannot have degree `< n`, so `n ≤ deg μ`.  Since `μ ∣ charpoly` and
`deg (charpoly) = n`, also `deg μ ≤ n`, so `deg μ = n`; two monic polynomials with
`μ ∣ charpoly` and equal degree are equal. -/
theorem isNonDerogatory_of_hasCyclicVector {n : ℕ} [NeZero n]
    {M : Matrix (Fin n) (Fin n) F} (h : HasCyclicVector M) : IsNonDerogatory M := by
  obtain ⟨v, hv⟩ := h
  have hint : IsIntegral F M := Matrix.isIntegral M
  set μ := minpoly F M with hμ
  have hμmonic : μ.Monic := minpoly.monic hint
  have hμ0 : μ ≠ 0 := hμmonic.ne_zero
  have hkill : (aeval M μ) *ᵥ v = 0 := by rw [minpoly.aeval F M]; exact Matrix.zero_mulVec v
  -- degree ≥ n
  have hge : n ≤ μ.natDegree := by
    by_contra hlt
    push_neg at hlt
    exact hμ0 (eq_zero_of_aeval_mulVec_eq_zero hv hlt hkill)
  -- degree ≤ n via minpoly ∣ charpoly, deg charpoly = n
  have hdvd : μ ∣ M.charpoly := Matrix.minpoly_dvd_charpoly M
  have hcharmonic : M.charpoly.Monic := Matrix.charpoly_monic M
  have hchardeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim]; exact Fintype.card_fin n
  have hle : μ.natDegree ≤ n :=
    hchardeg ▸ Polynomial.natDegree_le_of_dvd hdvd hcharmonic.ne_zero
  have hdegeq : μ.natDegree = n := le_antisymm hle hge
  -- μ = charpoly: same monic, μ ∣ charpoly, equal degrees ⇒ cofactor is 1
  obtain ⟨q, hq⟩ := hdvd
  have hqmonic : q.Monic := Polynomial.Monic.of_mul_monic_left hμmonic (hq ▸ hcharmonic)
  have hqdeg : q.natDegree = 0 := by
    have hmul : M.charpoly.natDegree = μ.natDegree + q.natDegree := by
      rw [hq, Polynomial.natDegree_mul hμmonic.ne_zero hqmonic.ne_zero]
    omega
  have hq1 : q = 1 := by
    have h0 := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
    have h1 : q.coeff 0 = 1 := by
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hqdeg] at hqmonic; exact hqmonic
    rw [h0, h1, map_one]
  show μ = M.charpoly
  rw [hq, hq1, mul_one]

/-- The Krylov orbit of a cyclic vector **spans the whole space**.  This is the
textbook "spanning" form of cyclicity: `n` linearly independent vectors in the
`n`-dimensional space `Fin n → F` form a basis. -/
theorem span_eq_top_of_isCyclicVector {n : ℕ} [NeZero n]
    {M : Matrix (Fin n) (Fin n) F} {v : Fin n → F} (hv : IsCyclicVector M v) :
    Submodule.span F (Set.range (krylov M v)) = ⊤ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  refine hv.span_eq_top_of_card_eq_finrank ?_
  rw [Module.finrank_fintype_fun_eq_card]

/-- **Reverse implication on the normal forms.** For a monic polynomial `p` of
degree `d`, the standard basis vector `e₀` is a cyclic vector for the companion
matrix `C(p)`.

Indeed `C(p)ᵏ · e₀ = eₖ` for `k < d` (`companionMatrix_pow_basis`), so the Krylov
orbit is precisely the standard basis of `Fin d → F`, which is linearly
independent. -/
theorem companionMatrix_isCyclicVector {d : ℕ} [NeZero d] (p : F[X]) :
    IsCyclicVector (companionMatrix (d := d) p) (Pi.single (0 : Fin d) 1) := by
  -- the orbit family is the standard basis `k ↦ Pi.single k 1`
  have hfam : krylov (companionMatrix (d := d) p) (Pi.single (0 : Fin d) 1)
      = fun k : Fin d => (Pi.single k 1 : Fin d → F) := by
    funext k
    have := companionMatrix_pow_basis (F := F) p k.val k.isLt
    simp only [krylov]
    rw [this]
  rw [IsCyclicVector, hfam, Fintype.linearIndependent_iff]
  intro g hg k
  have hk := congr_fun hg k
  simpa [Finset.sum_apply, Pi.single_apply] using hk

/-- **The two directions combine on companion matrices.** `C(p)` is non-derogatory,
obtained here through its explicit cyclic vector `e₀`.  (This is consistent with the
direct computation `minpoly (C p) = charpoly (C p) = p` in `oq-02-oq-01`.) -/
theorem companionMatrix_isNonDerogatory {d : ℕ} [NeZero d] (p : F[X]) :
    IsNonDerogatory (companionMatrix (d := d) p) :=
  isNonDerogatory_of_hasCyclicVector ⟨_, companionMatrix_isCyclicVector p⟩

end CayleyHamiltonReductionOQ02OQ03
