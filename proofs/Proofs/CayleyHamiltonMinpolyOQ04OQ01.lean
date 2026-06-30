/-
  Cayley–Hamilton / Minimal Polynomial, OQ-04 follow-up OQ-01:
  The constructive CONVERSE for the maximal-nilpotent case, over ANY field.

  Parent: Proofs/CayleyHamiltonMinpolyOQ04.lean
          ("Nonderogatory Matrices and Cyclic Vectors")
  Sibling: Proofs/CayleyHamiltonMinpolyOQ04Backward.lean
          (converse for INFINITE fields; final assembly left as 1 `sorry`)

  Background.
  A matrix M ∈ M_n(K) is *nonderogatory* when minpoly K M = charpoly M.  The
  parent entry proves the easy direction (a cyclic vector ⟹ nonderogatory) and
  *axiomatizes* the converse `nonderogatory_has_cyclic_vector`.  The Backward
  sibling discharges that axiom for infinite fields, but its main assembly is a
  `sorry` (a `normalizedFactors`/`DecidableEq` import clash).

  This file isolates the one case of the converse that needs neither an infinite
  field nor the rational-canonical-form / factorisation machinery: the
  **maximal-nilpotent** matrices `N` with `Nⁿ = 0` and `Nⁿ⁻¹ ≠ 0` (a single
  Jordan block at 0).  For these we CONSTRUCT a cyclic vector explicitly over an
  ARBITRARY field — including the finite fields the infinite-field theorem cannot
  reach.

  The three Krylov-independence helpers used here are mathematically those of the
  Backward sibling, but are reproved inline (self-contained) because the sibling's
  *downstream* assembly does not currently compile against Mathlib 4.26.0; the
  helpers themselves are clean (no `sorry`, no `axiom`).

  We also characterise this case arithmetically: for `0 < n`,
        minpoly K N = Xⁿ   ⟺   Nⁿ = 0 ∧ Nⁿ⁻¹ ≠ 0,
  via the fact that the minimal polynomial of such an `N` divides `Xⁿ` and `X` is
  prime, so `minpoly K N = Xⁱ` with `i = n` forced by `Nⁿ⁻¹ ≠ 0`.

  Everything is proved with no `axiom`, no `sorry`, and no `native_decide`.

  References:
  - Hoffman & Kunze, "Linear Algebra" §7.1–7.2 (cyclic vectors, single block)
  - Roman, "Advanced Linear Algebra" §10.4
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

namespace CayleyHamiltonMinpolyOQ04OQ01

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-!
## Part 0: Cyclic vectors and inlined Krylov-independence helpers

`IsCyclicVector M v` says no nonzero polynomial of degree `< n` annihilates `v`
under `M`; equivalently the Krylov vectors `{v, Mv, …, Mⁿ⁻¹v}` are a basis.  The
three lemmas below are self-contained copies of the proven helpers in the
`CayleyHamiltonMinpolyOQ04Backward` sibling.
-/

/-- A vector `v` is a cyclic vector for `M` if no nonzero polynomial of degree `< n`
annihilates `v` under `M`. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- A nonzero matrix has a vector outside its kernel. -/
theorem exists_mulVec_ne_zero {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0) :
    ∃ v : Fin n → K, A.mulVec v ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hA
  funext i j
  specialize hall (Pi.single j 1)
  have : (A.mulVec (Pi.single j 1)) i = 0 := congr_fun hall i
  simp only [mulVec, dotProduct, Pi.single_apply] at this
  simpa using this

/-- If `{v, Mv, …, Mⁿ⁻¹v}` are linearly independent, then `v` is a cyclic vector. -/
theorem isCyclicVector_of_linearIndependent
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hli : LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v)) :
    IsCyclicVector M v := by
  intro p hp hann
  suffices h : ∀ k : Fin n, p.coeff ↑k = 0 by
    ext m; simp only [Polynomial.coeff_zero]
    by_cases hm : m < n
    · exact h ⟨m, hm⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  apply Fintype.linearIndependent_iff.mp hli
  have heval : aeval M p = ∑ i ∈ Finset.range n, p.coeff i • M ^ i :=
    aeval_eq_sum_range' hp M
  have hdist : ∀ (s : Finset ℕ),
      (∑ i ∈ s, p.coeff i • M ^ i).mulVec v =
      ∑ i ∈ s, p.coeff i • (M ^ i).mulVec v := by
    intro s
    induction s using Finset.induction with
    | empty => simp [Matrix.zero_mulVec]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.add_mulVec, ih,
          Finset.sum_insert ha, Matrix.smul_mulVec]
  rw [Fin.sum_univ_eq_sum_range (fun k => p.coeff k • (M ^ k).mulVec v) n, ← hdist, ← heval]
  exact hann

/-- For a nilpotent matrix `N` with `Nⁿ = 0` and `Nⁿ⁻¹ v ≠ 0`, the Krylov vectors
`{v, Nv, …, Nⁿ⁻¹v}` are linearly independent. -/
theorem nilpotent_krylov_independent
    (N : Matrix (Fin n) (Fin n) K) (hnil : N ^ n = 0)
    (v : Fin n → K) (hv : (N ^ (n - 1)).mulVec v ≠ 0) :
    LinearIndependent K (fun k : Fin n => (N ^ (k : ℕ)).mulVec v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  suffices main : ∀ j : ℕ, (hj : j < n) → c ⟨j, hj⟩ = 0 from
    fun i => main ↑i i.isLt
  intro j hj
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have happ : ∑ k : Fin n, c k • (N ^ (n - 1 - j + ↑k)).mulVec v = 0 := by
      have h0 := congr_arg (fun w => (N ^ (n - 1 - j)).mulVec w) hc
      simp only [Matrix.mulVec_zero] at h0
      have hdist : (N ^ (n - 1 - j)).mulVec (∑ k : Fin n, c k • (N ^ (↑k : ℕ)).mulVec v) =
          ∑ k : Fin n, c k • (N ^ (n - 1 - j)).mulVec ((N ^ (↑k : ℕ)).mulVec v) := by
        rw [← Matrix.mulVecLin_apply]; rw [map_sum]
        congr 1; ext k; rw [map_smul, Matrix.mulVecLin_apply]
      rw [hdist] at h0
      simp only [Matrix.mulVec_mulVec, ← pow_add] at h0
      exact h0
    have hred : ∑ k : Fin n, c k • (N ^ (n - 1 - j + ↑k)).mulVec v =
                c ⟨j, hj⟩ • (N ^ (n - 1)).mulVec v := by
      rw [Finset.sum_eq_single_of_mem ⟨j, hj⟩ (Finset.mem_univ _)]
      · congr 1; congr 1; congr 1
        exact Nat.sub_add_cancel (Nat.le_sub_one_of_lt hj)
      · intro k _ hk
        have hk_val : (↑k : ℕ) ≠ j := fun h => hk (Fin.ext h)
        rcases lt_or_gt_of_ne hk_val with hlt | hgt
        · have : c k = 0 := by
            have := ih ↑k hlt k.isLt
            rwa [show (⟨↑k, k.isLt⟩ : Fin n) = k from Fin.eta k k.isLt] at this
          simp [this]
        · have hge : n ≤ n - 1 - j + ↑k := by
            have := Nat.le_sub_one_of_lt hj
            omega
          have hpow : N ^ (n - 1 - j + ↑k) = 0 := by
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
            rw [hd, pow_add, hnil, zero_mul]
          simp [hpow, Matrix.zero_mulVec]
    rw [hred] at happ
    rcases smul_eq_zero.mp happ with h | h
    · exact h
    · exact absurd h hv

/-!
## Part I: The constructive cyclic vector

For a maximal-nilpotent matrix (`Nⁿ = 0`, `Nⁿ⁻¹ ≠ 0`) over any field we obtain a
cyclic vector directly, with no factorisation and no infinitude assumption.
-/

/-- **Constructive converse, maximal-nilpotent case.**
If `Nⁿ = 0` and `Nⁿ⁻¹ ≠ 0`, then `N` has a cyclic vector — over an ARBITRARY
field `K`.  The witness is any `v` with `Nⁿ⁻¹ v ≠ 0`; its Krylov vectors
`{v, Nv, …, Nⁿ⁻¹v}` are then linearly independent. -/
theorem maximal_nilpotent_has_cyclic_vector
    {N : Matrix (Fin n) (Fin n) K} (hnil : N ^ n = 0) (hne : N ^ (n - 1) ≠ 0) :
    ∃ v, IsCyclicVector N v := by
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hne
  exact ⟨v, isCyclicVector_of_linearIndependent N v
    (nilpotent_krylov_independent N hnil v hv)⟩

/-!
## Part II: Arithmetic characterisation via the minimal polynomial
-/

/-- For a maximal-nilpotent matrix the minimal polynomial is exactly `Xⁿ`. -/
theorem minpoly_eq_X_pow_of_maximal_nilpotent
    {N : Matrix (Fin n) (Fin n) K} (hn : 0 < n)
    (hnil : N ^ n = 0) (hne : N ^ (n - 1) ≠ 0) :
    minpoly K N = X ^ n := by
  have haeval : aeval N (X ^ n : K[X]) = 0 := by rw [map_pow, aeval_X]; exact hnil
  have hdvd : minpoly K N ∣ X ^ n := minpoly.dvd K N haeval
  obtain ⟨i, hi_le, hassoc⟩ := (dvd_prime_pow prime_X n).mp hdvd
  have hmono : minpoly K N = X ^ i :=
    eq_of_monic_of_associated (minpoly.monic (isIntegral N)) (monic_X_pow i) hassoc
  have hNi : N ^ i = 0 := by
    have := minpoly.aeval K N
    rw [hmono, map_pow, aeval_X] at this
    exact this
  have hi_ge : n ≤ i := by
    by_contra hlt
    push_neg at hlt
    apply hne
    have hsplit : n - 1 = (n - 1 - i) + i := by omega
    rw [hsplit, pow_add, hNi, mul_zero]
  rw [hmono, le_antisymm hi_le hi_ge]

/-- A maximal-nilpotent matrix has `natDegree (minpoly K N) = n`: its minimal
polynomial reaches the full degree `n` of the characteristic polynomial — the
nonderogatory condition expressed at the level of the minimal polynomial. -/
theorem natDegree_minpoly_eq_of_maximal_nilpotent
    {N : Matrix (Fin n) (Fin n) K} (hn : 0 < n)
    (hnil : N ^ n = 0) (hne : N ^ (n - 1) ≠ 0) :
    (minpoly K N).natDegree = n := by
  rw [minpoly_eq_X_pow_of_maximal_nilpotent hn hnil hne, natDegree_X_pow]

/-- Converse half of the characterisation: `minpoly K N = Xⁿ` recovers maximal
nilpotency `Nⁿ = 0 ∧ Nⁿ⁻¹ ≠ 0`. -/
theorem maximal_nilpotent_of_minpoly_eq_X_pow
    {N : Matrix (Fin n) (Fin n) K} (hn : 0 < n)
    (hmp : minpoly K N = X ^ n) :
    N ^ n = 0 ∧ N ^ (n - 1) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have := minpoly.aeval K N
    rw [hmp, map_pow, aeval_X] at this
    exact this
  · intro hcontra
    have haeval : aeval N (X ^ (n - 1) : K[X]) = 0 := by rw [map_pow, aeval_X]; exact hcontra
    have hdvd : minpoly K N ∣ X ^ (n - 1) := minpoly.dvd K N haeval
    have hle := Polynomial.natDegree_le_of_dvd hdvd (pow_ne_zero _ (X_ne_zero (R := K)))
    rw [hmp, natDegree_X_pow, natDegree_X_pow] at hle
    omega

/-- **Characterisation.** For `0 < n` a matrix is maximal-nilpotent iff its
minimal polynomial is `Xⁿ`. -/
theorem minpoly_eq_X_pow_iff_maximal_nilpotent
    {N : Matrix (Fin n) (Fin n) K} (hn : 0 < n) :
    minpoly K N = X ^ n ↔ N ^ n = 0 ∧ N ^ (n - 1) ≠ 0 :=
  ⟨maximal_nilpotent_of_minpoly_eq_X_pow hn,
   fun ⟨h1, h2⟩ => minpoly_eq_X_pow_of_maximal_nilpotent hn h1 h2⟩

/-- A matrix with `minpoly K N = Xⁿ` (maximal nilpotent) has a cyclic vector. -/
theorem has_cyclic_vector_of_minpoly_eq_X_pow
    {N : Matrix (Fin n) (Fin n) K} (hn : 0 < n) (hmp : minpoly K N = X ^ n) :
    ∃ v, IsCyclicVector N v := by
  obtain ⟨h1, h2⟩ := maximal_nilpotent_of_minpoly_eq_X_pow hn hmp
  exact maximal_nilpotent_has_cyclic_vector h1 h2

end CayleyHamiltonMinpolyOQ04OQ01
