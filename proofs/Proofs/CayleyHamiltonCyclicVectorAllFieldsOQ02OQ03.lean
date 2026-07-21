/-
  Commutant of a Cyclic Endomorphism is K[T]  (Module.End lift)
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-03)

  This file lifts the matrix commutant characterization
  (`CayleyHamiltonCyclicVectorAllFieldsOQ02.lean`,
   `CyclicCommutant.commuting_matrix_is_polynomial`) from concrete matrices
  `Matrix (Fin n) (Fin n) K` to the coordinate-free endomorphism setting
  `Module.End K V` over a finite-dimensional vector space `V`.

  ## Statement

  Let `V` be a finite-dimensional `K`-vector space and `T : Module.End K V`.
  A vector `v` is a **cyclic vector** for `T` if no nonzero polynomial of
  degree `< finrank K V` annihilates `v` (`IsEndCyclicVector`, the direct
  analogue of the matrix `GeneralCyclicVector.IsCyclicVector`).

    **If `T` has a cyclic vector then every endomorphism commuting with `T`
    is a polynomial in `T`.**

  Equivalently, the commutant (centralizer) of `T` inside `Module.End K V`
  coincides with the subalgebra `K[T]` and is therefore commutative.

  ## Proof

  The argument mirrors the parent matrix proof, replacing `Matrix.mulVec`
  by endomorphism application:

  1. The Krylov vectors `{Tᵏ·v}_{k<n}` (`n = finrank K V`) are linearly
     independent — a nontrivial linear relation would furnish a nonzero
     annihilating polynomial of degree `< n` (`endKrylov_linearIndependent`).
     They therefore form a basis `b` of `V`.
  2. Write `A·v` in the Krylov basis: `A·v = ∑_{k<n} cₖ (Tᵏ·v)`, with
     `cₖ = b.repr (A·v) k`; set `p = ∑ cₖ Xᵏ`. Then `p(T)·v = A·v`.
  3. `A` and `p(T)` agree on every basis vector `Tⁱ·v`:
       `A·(Tⁱ·v) = Tⁱ·(A·v) = Tⁱ·(p(T)·v) = p(T)·(Tⁱ·v)`,
     using that `A` and `p(T)` each commute with `Tⁱ`. Two linear maps that
     agree on a basis are equal (`Basis.ext`), so `A = p(T)`. This is where
     the endomorphism formulation is cleaner than the matrix parent: no
     column-by-column matrix recovery is needed.

  Status: 0 sorries, 0 axioms.
-/
import Mathlib

noncomputable section

namespace EndCyclicCommutant

open Polynomial Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

-- ============================================================
-- SECTION I: Cyclic vectors for an endomorphism
-- ============================================================

/-- A vector `v` is **cyclic** for the endomorphism `T` if no nonzero
    polynomial of degree `< finrank K V` annihilates `v`. This is the direct
    analogue, in the endomorphism setting, of the matrix definition
    `GeneralCyclicVector.IsCyclicVector`. -/
def IsEndCyclicVector (T : Module.End K V) (v : V) : Prop :=
  ∀ p : K[X], p.natDegree < finrank K V → (aeval T p) v = 0 → p = 0

variable [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- If `v` is a cyclic vector for `T`, the Krylov vectors `{Tᵏ·v}_{k<n}`
    (`n = finrank K V`) are linearly independent. Endomorphism analogue of
    `CyclicCommutant.krylov_linearIndependent`. -/
theorem endKrylov_linearIndependent
    (T : Module.End K V) (v : V) (hv : IsEndCyclicVector T v)
    (hn : 0 < finrank K V) :
    LinearIndependent K (fun k : Fin (finrank K V) => (T ^ (k : ℕ)) v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  set p := ∑ k : Fin (finrank K V), C (c k) * X ^ (k : ℕ) with hp_def
  have hp_aeval : aeval T p = ∑ k : Fin (finrank K V), c k • T ^ (k : ℕ) := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X,
               Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hp_ann : (aeval T p) v = 0 := by
    rw [hp_aeval]
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hc
  have hp_deg : p.natDegree < finrank K V := by
    apply lt_of_le_of_lt (natDegree_sum_le _ _)
    apply (Finset.sup_lt_iff hn).mpr
    intro k _; exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le (c k) ↑k) k.isLt
  have hp_zero : p = 0 := hv p hp_deg hp_ann
  have h_coeff := congr_arg (Polynomial.coeff · ↑i) hp_zero
  simp only [Polynomial.coeff_zero, p, C_mul_X_pow_eq_monomial,
             finsetSum_coeff, coeff_monomial] at h_coeff
  simpa [Fin.val_injective.eq_iff] using h_coeff

-- ============================================================
-- SECTION II: Polynomials in T commute with powers of T
-- ============================================================

omit [FiniteDimensional K V] in
/-- `p(T)` commutes with `Tʲ` (polynomials in `T` commute with powers of `T`).
    Endomorphism analogue of `CyclicCommutant.aeval_commute_pow`. -/
private lemma aeval_end_commute_pow (p : K[X]) (T : Module.End K V) (j : ℕ) :
    aeval T p * T ^ j = T ^ j * aeval T p := by
  have hcomm : Commute (aeval T p) T := by
    show aeval T p * T = T * aeval T p
    have h : aeval T p * aeval T (X : K[X]) = aeval T (X : K[X]) * aeval T p := by
      rw [← map_mul, ← map_mul, mul_comm p X]
    simpa [aeval_X] using h
  exact hcomm.pow_right j

-- ============================================================
-- SECTION III: Main theorem — commuting endomorphisms are polynomials in T
-- ============================================================

/-- **Commutant characterization (endomorphism form).** If `T : Module.End K V`
    has a cyclic vector `v` and `A` commutes with `T`, then `A` is a polynomial
    in `T`: there is `p` with `A = aeval T p`.

    Coordinate-free lift of `CyclicCommutant.commuting_matrix_is_polynomial`:
    a cyclic vector forces the centralizer of `T` inside `Module.End K V` to be
    exactly the subalgebra `K[T]`. -/
theorem commuting_end_is_polynomial
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v)
    (A : Module.End K V) (hA : A * T = T * A) :
    ∃ p : K[X], A = aeval T p := by
  -- Degenerate case `finrank = 0`: `V` is trivial, so `Module.End K V` is
  -- a subsingleton and every endomorphism equals `aeval T 0`.
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hn
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact ⟨0, Subsingleton.elim _ _⟩
  set n := finrank K V with hn_def
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hli : LinearIndependent K (fun k : Fin n => (T ^ (k : ℕ)) v) :=
    endKrylov_linearIndependent T v hcyc hn
  -- Krylov vectors form a basis of `V`.
  set b : Module.Basis (Fin n) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]) with hb_def
  have hb : ∀ i, b i = (T ^ (i : ℕ)) v := by
    intro i; rw [hb_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- The polynomial whose coordinates are those of `A·v` in the Krylov basis.
  refine ⟨∑ k : Fin n, C (b.repr (A v) k) * X ^ (k : ℕ), ?_⟩
  set p : K[X] := ∑ k : Fin n, C (b.repr (A v) k) * X ^ (k : ℕ) with hp_def
  have hp_aeval : aeval T p = ∑ k : Fin n, b.repr (A v) k • T ^ (k : ℕ) := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X,
               Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  -- `p(T)·v = A·v` (`Basis.sum_repr`).
  have hAv : (aeval T p) v = A v := by
    rw [hp_aeval]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [show (∑ k : Fin n, b.repr (A v) k • (T ^ (k : ℕ)) v) =
             ∑ k : Fin n, b.repr (A v) k • b k from
          Finset.sum_congr rfl (fun k _ => by rw [hb k])]
    exact b.sum_repr (A v)
  -- `A` and `p(T)` agree on every basis vector.
  have key : ∀ i : Fin n, A (b i) = (aeval T p) (b i) := by
    intro i
    have e1 : A ((T ^ (i : ℕ)) v) = (T ^ (i : ℕ)) (A v) := by
      have h : A * T ^ (i : ℕ) = T ^ (i : ℕ) * A :=
        (show Commute A T from hA).pow_right (i : ℕ)
      have := congrArg (fun f : Module.End K V => f v) h
      simpa only [Module.End.mul_apply] using this
    have e2 : (aeval T p) ((T ^ (i : ℕ)) v) = (T ^ (i : ℕ)) ((aeval T p) v) := by
      have h : aeval T p * T ^ (i : ℕ) = T ^ (i : ℕ) * aeval T p :=
        aeval_end_commute_pow p T i
      have := congrArg (fun f : Module.End K V => f v) h
      simpa only [Module.End.mul_apply] using this
    rw [hb i, e1, e2, hAv]
  -- Two linear maps agreeing on a basis are equal.
  exact b.ext key

-- ============================================================
-- SECTION IV: Consequences
-- ============================================================

/-- The centralizer of an endomorphism with a cyclic vector is **commutative**:
    any two endomorphisms commuting with `T` commute with each other, since
    both are polynomials in `T`. Endomorphism analogue of
    `CyclicCommutant.commutant_commutative`. -/
theorem end_commutant_commutative
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v)
    (A B : Module.End K V)
    (hA : A * T = T * A) (hB : B * T = T * B) :
    A * B = B * A := by
  obtain ⟨p, rfl⟩ := commuting_end_is_polynomial T v hcyc A hA
  obtain ⟨q, rfl⟩ := commuting_end_is_polynomial T v hcyc B hB
  rw [← map_mul, ← map_mul, mul_comm]

omit [FiniteDimensional K V] in
/-- Every polynomial in `T` commutes with `T` — the trivial inclusion
    `K[T] ⊆ centralizer(T)`. Together with `commuting_end_is_polynomial` this
    gives the full equality of the centralizer with `K[T]`. -/
theorem aeval_end_commute (T : Module.End K V) (p : K[X]) :
    aeval T p * T = T * aeval T p := by
  simpa using aeval_end_commute_pow p T 1

/-- **Centralizer = `K[T]` as subalgebras.** If `T : Module.End K V` has a cyclic
    vector, its centralizer inside `Module.End K V` coincides, *as a subalgebra*,
    with the subalgebra `K[T] = Algebra.adjoin K {T}` generated by `T`.

    This packages both inclusions into the single canonical statement:
    `commuting_end_is_polynomial` gives centralizer `⊆ K[T]` (needs the cyclic
    vector), and `aeval_end_commute` gives the trivial `K[T] ⊆ centralizer`.
    Consumers can use this directly instead of re-deriving the two directions. -/
theorem end_centralizer_eq_adjoin
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v) :
    Subalgebra.centralizer K ({T} : Set (Module.End K V)) =
      Algebra.adjoin K {T} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  apply le_antisymm
  · -- centralizer ⊆ range(aeval T): a commuting endo is a polynomial in `T`
    intro A hA
    rw [Subalgebra.mem_centralizer_iff] at hA
    have hAT : A * T = T * A := (hA T (Set.mem_singleton T)).symm
    obtain ⟨p, hp⟩ := commuting_end_is_polynomial T v hcyc A hAT
    exact AlgHom.mem_range.mpr ⟨p, hp.symm⟩
  · -- range(aeval T) ⊆ centralizer: every polynomial in `T` commutes with `T`
    rintro A ⟨p, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (aeval_end_commute T p).symm

end EndCyclicCommutant

end
