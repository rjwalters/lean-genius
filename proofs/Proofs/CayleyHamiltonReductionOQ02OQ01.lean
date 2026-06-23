import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-
# Rational Canonical Form: Companion Matrix Properties

## Open Question
Formalize the rational canonical form (Frobenius normal form) in Lean 4.

## What This Proves

The rational canonical form states that every matrix over a field is similar
to a block diagonal matrix of companion matrices C(p₁), ..., C(pₖ) where
p₁ | p₂ | ... | pₖ are the invariant factors.

This file focuses on the **companion matrix**, the fundamental building block
of the RCF:

1. **Definition**: The companion matrix C(p) for a monic polynomial p of degree d
2. **Polynomial annihilation**: p(C(p)) = 0 (Cayley-Hamilton for companion)
3. **Characteristic polynomial**: charpoly(C(p)) = p (companion determines charpoly)
4. **Minimal polynomial**: minpoly(C(p)) = p (companion is non-derogatory)

## Status
- [x] Companion matrix definition
- [x] Basic properties (size, entries)
- [x] Column action lemma: C(p) · eⱼ = eⱼ₊₁ for j < d-1
- [x] Last column action: C(p) · e_{d-1} = -∑ aᵢ eᵢ
- [x] Orbit lemma: C(p)^k · e₀ = eₖ for k < d
- [x] p(C(p)) = 0 (proved via orbit argument)
- [x] minpoly(C(p)) = p (proved via orbit independence + degree argument)
- [x] charpoly(C(p)) = p (proved via minpoly = p + Cayley-Hamilton)

## Gap Assessment for Full RCF
- **Smith normal form for F[X]-matrices**: ~800 lines (main blocker)
- **Companion matrix**: ~200 lines (THIS FILE — partial)
- **Block diagonal assembly**: ~300 lines (not started)
- **Full RCF theorem**: ~500 lines (not started)
- **Total estimated**: ~1800 lines

## Mathlib Dependencies
- `Matrix.charpoly`, `Matrix.aeval_self_charpoly` : Cayley-Hamilton
- `minpoly` : Minimal polynomial
- `Polynomial.coeff` : Polynomial coefficients
-/

namespace CayleyHamiltonReductionOQ02OQ01

open Matrix Polynomial BigOperators

variable {F : Type*} [Field F]

/-! ## Part 1: Companion Matrix Definition -/

/-- The **companion matrix** of a monic polynomial p of degree d.

For p(x) = xᵈ + aₐ₋₁xᵈ⁻¹ + ... + a₁x + a₀, the companion matrix is the
d × d matrix:

```
C(p) = | 0  0  0  ...  0  -a₀    |
       | 1  0  0  ...  0  -a₁    |
       | 0  1  0  ...  0  -a₂    |
       | :  :  :  ...  :   :     |
       | 0  0  0  ...  1  -aₐ₋₁  |
```

That is: 1's on the subdiagonal, negated coefficients in the last column,
zeros elsewhere. -/
noncomputable def companionMatrix {d : ℕ} (p : F[X]) : Matrix (Fin d) (Fin d) F :=
  fun i j =>
    if j.val + 1 = d then -(p.coeff i.val)
    else if i.val = j.val + 1 then 1
    else 0

/-! ## Part 2: Basic Properties -/

/-- The subdiagonal entries of the companion matrix are 1. -/
theorem companionMatrix_subdiag {d : ℕ} (p : F[X]) {i j : Fin d}
    (h : i.val = j.val + 1) (hj : j.val + 1 < d) :
    companionMatrix p i j = 1 := by
  simp only [companionMatrix]
  split_ifs with h1 h2
  · omega
  · rfl
  · exact absurd h h2

/-- The last column of the companion matrix has negated coefficients. -/
theorem companionMatrix_last_col {d : ℕ} (p : F[X]) {i : Fin d} {j : Fin d}
    (hj : j.val + 1 = d) :
    companionMatrix p i j = -(p.coeff i.val) := by
  simp only [companionMatrix]
  split_ifs with h1
  · rfl
  · exact absurd hj h1

/-- Off-diagonal, off-last-column entries are zero. -/
theorem companionMatrix_zero {d : ℕ} (p : F[X]) {i j : Fin d}
    (h1 : j.val + 1 ≠ d) (h2 : i.val ≠ j.val + 1) :
    companionMatrix p i j = 0 := by
  simp only [companionMatrix]
  split_ifs <;> contradiction

/-! ## Part 3: Orbit of Standard Basis Vectors

The key structural property of companion matrices: the orbit
{e₀, C(p)·e₀, C(p)²·e₀, ...} produces the standard basis.
This gives a direct proof that p(C(p)) = 0 without determinants. -/

/-- Column j of C(p) is e_{j+1} when j is not the last column.
That is, C(p) maps the j-th basis vector to the (j+1)-th. -/
lemma companionMatrix_col {d : ℕ} (p : F[X]) {j : Fin d}
    (hj : j.val + 1 < d) (i : Fin d) :
    companionMatrix (d := d) p i j =
      if i.val = j.val + 1 then (1 : F) else 0 := by
  simp only [companionMatrix]
  split_ifs with h1 h2
  · omega  -- j.val + 1 = d contradicts hj
  · rfl
  · rfl

/-- The last column of C(p) contains negated polynomial coefficients. -/
lemma companionMatrix_last_col' {d : ℕ} (p : F[X]) {j : Fin d}
    (hj : j.val + 1 = d) (i : Fin d) :
    companionMatrix (d := d) p i j = -(p.coeff i.val) := by
  simp only [companionMatrix, hj, ite_true]

/-- C(p) maps basis vector eⱼ to eⱼ₊₁ for j < d-1. -/
lemma companionMatrix_mulVec_basis {d : ℕ} (p : F[X]) (j : Fin d)
    (hj : j.val + 1 < d) :
    (companionMatrix (d := d) p).mulVec (Pi.single j 1) =
      Pi.single (⟨j.val + 1, hj⟩ : Fin d) 1 := by
  ext ⟨i, hi⟩
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Fintype.sum_eq_single j (fun k hk => by simp [Pi.single_apply, hk])]
  simp only [Pi.single_apply, if_true, eq_self_iff_true, mul_one]
  rw [companionMatrix_col p hj]
  simp [Pi.single_apply, Fin.ext_iff]

/-- C(p) maps basis vector e_{d-1} to -∑ aᵢ eᵢ. -/
lemma companionMatrix_mulVec_last {d : ℕ} (p : F[X]) (hd : 0 < d) :
    (companionMatrix (d := d) p).mulVec
      (Pi.single (⟨d - 1, by omega⟩ : Fin d) 1) =
      fun i => -(p.coeff i.val) := by
  ext ⟨i, hi⟩
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Fintype.sum_eq_single ⟨d - 1, by omega⟩
    (fun k hk => by simp [Pi.single_apply, hk])]
  simp only [Pi.single_apply, if_true, eq_self_iff_true, mul_one]
  rw [companionMatrix_last_col' p (by omega)]

/-- The orbit of e₀ under C(p): C(p)^k · e₀ = eₖ for k < d. -/
lemma companionMatrix_pow_basis {d : ℕ} (p : F[X]) (k : ℕ) (hk : k < d) :
    ((companionMatrix (d := d) p) ^ k).mulVec (Pi.single (0 : Fin d) 1) =
      Pi.single (⟨k, hk⟩ : Fin d) 1 := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    congr 1; ext; simp [Fin.ext_iff]
  | succ m ih =>
    rw [pow_succ, Matrix.mul_mulVec, ih (by omega)]
    exact companionMatrix_mulVec_basis p ⟨m, by omega⟩ hk

/-! ## Part 3b: Polynomial Annihilation and Key Theorems -/

/-! ### Helper lemmas for the three core theorems -/

/-- mulVec distributes over finite sums of matrices. -/
private theorem sum_mulVec' {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin d) (Fin d) F) (v : Fin d → F) :
    (∑ i ∈ s, f i) *ᵥ v = ∑ i ∈ s, f i *ᵥ v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s' has ih => rw [Finset.sum_insert has, Matrix.add_mulVec, ih, Finset.sum_insert has]

/-- The sum ∑ k : Fin d, c k • Pi.single k 1 = c (standard basis expansion). -/
private lemma sum_smul_pi_single {d : ℕ} (c : Fin d → F) :
    ∑ k : Fin d, c k • (Pi.single k 1 : Fin d → F) = c := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
             mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- aeval M p expands as ∑ k in range(d+1), coeff k • M^k. -/
private lemma aeval_eq_sum_pow {d : ℕ} (p : F[X]) (hdeg : p.natDegree = d)
    (M : Matrix (Fin d) (Fin d) F) :
    aeval M p = ∑ k ∈ Finset.range (d + 1), p.coeff k • M ^ k := by
  simp only [aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (hdeg ▸ Polynomial.le_natDegree_of_mem_supp i hi))
  · intro i _ hi
    simp only [Polynomial.notMem_support_iff.mp hi, map_zero, zero_mul]

/-- M^d applied to e₀ = negated coefficient vector (orbit + last column). -/
private lemma pow_d_mulVec_e0 {d : ℕ} [NeZero d] (p : F[X]) :
    ((companionMatrix (d := d) p) ^ d) *ᵥ (Pi.single (0 : Fin d) 1) =
      fun i => -(p.coeff i.val) := by
  have hd1 : d - 1 < d := Nat.sub_lt (NeZero.pos d) one_pos
  rw [show d = d - 1 + 1 from (Nat.succ_pred_eq_of_pos (NeZero.pos d)).symm]
  rw [pow_succ, Matrix.mul_mulVec]
  rw [companionMatrix_pow_basis p (d - 1) hd1]
  exact companionMatrix_mulVec_last p (NeZero.pos d)

/-- p(M) commutes with M^j in the matrix ring (polynomials in M commute). -/
private lemma aeval_commute_pow {d : ℕ} (p : F[X]) (M : Matrix (Fin d) (Fin d) F) (j : ℕ) :
    aeval M p * M ^ j = M ^ j * aeval M p := by
  have hcomm : Commute (aeval M p) M := by
    show aeval M p * M = M * aeval M p
    have h : aeval M p * aeval M X = aeval M X * aeval M p := by
      rw [← map_mul, ← map_mul, mul_comm]
    simpa [aeval_X] using h
  exact hcomm.pow_right j

/-- p(C(p)) applied to e₀ = 0: the orbit ∑ aₖ eₖ cancels with M^d · e₀ = -∑ aₖ eₖ. -/
private lemma aeval_companionMatrix_mulVec_e0 {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    (aeval (companionMatrix (d := d) p) p) *ᵥ (Pi.single (0 : Fin d) 1) = 0 := by
  set M := companionMatrix (d := d) p
  rw [aeval_eq_sum_pow p hdeg M, sum_mulVec', Finset.sum_range_succ]
  simp only [Matrix.smul_mulVec, pow_d_mulVec_e0]
  have hcd : p.coeff d = 1 := by
    have := hp.leadingCoeff; rwa [Polynomial.leadingCoeff, hdeg] at this
  rw [hcd, one_smul]
  -- ∑ k ∈ range d, p.coeff k • M^k *ᵥ e₀ = fun i => p.coeff i.val  (orbit reindexing)
  have hsum : ∑ k ∈ Finset.range d, p.coeff k • (M ^ k) *ᵥ (Pi.single (0 : Fin d) 1) =
      fun i => p.coeff i.val := by
    have heq : ∑ k ∈ Finset.range d, p.coeff k • (M ^ k) *ᵥ (Pi.single (0 : Fin d) 1) =
        ∑ k : Fin d, p.coeff k.val • (Pi.single k 1 : Fin d → F) := by
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1; funext k
      rw [companionMatrix_pow_basis p k.val k.isLt]
    rw [heq]
    exact sum_smul_pi_single (fun i => p.coeff i.val)
  rw [hsum]
  funext i; simp [Pi.add_apply]

/-- **Direct proof**: The companion matrix is annihilated by its polynomial.
Proved by orbit argument: p(C(p)) · e₀ = 0, extended to all eⱼ via commutativity. -/
theorem aeval_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    aeval (companionMatrix (d := d) p) p = 0 := by
  set M := companionMatrix (d := d) p
  ext i j
  have hcol : (aeval M p) *ᵥ (Pi.single j 1) = 0 := by
    rw [← companionMatrix_pow_basis p j.val j.isLt]
    -- (aeval M p) *ᵥ (M^j *ᵥ e₀) = ((aeval M p) * M^j) *ᵥ e₀
    rw [← Matrix.mul_mulVec]
    rw [aeval_commute_pow]
    -- = (M^j * aeval M p) *ᵥ e₀ = M^j *ᵥ ((aeval M p) *ᵥ e₀)
    rw [Matrix.mul_mulVec, aeval_companionMatrix_mulVec_e0 p hp hdeg, Matrix.mulVec_zero]
  have := congr_fun hcol i
  simp only [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
             Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.zero_apply] at this
  exact this

/-- **The minimal polynomial of C(p) equals p.**

The orbit {e₀, C(p)e₀, ..., C(p)^{d-1}e₀} = standard basis shows that
no polynomial of degree < d can annihilate C(p). Combined with
p(C(p)) = 0 (so minpoly | p), we get minpoly = p. -/
theorem minpoly_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    minpoly F (companionMatrix (d := d) p) = p := by
  set M := companionMatrix (d := d) p
  set μ := minpoly F M
  have hμ_monic : μ.Monic := minpoly.monic (Matrix.isIntegral M)
  have hdvd : μ ∣ p := minpoly.dvd F M (aeval_companionMatrix hp hdeg)
  have hdeg_le : μ.natDegree ≤ d :=
    hdeg ▸ Polynomial.natDegree_le_of_dvd hdvd hp.ne_zero
  -- d ≤ deg(μ): any polynomial of degree < d cannot annihilate M
  -- (orbit gives linear independence, leading coeff ≠ 0 contradiction)
  have hdeg_ge : d ≤ μ.natDegree := by
    by_contra hlt
    push_neg at hlt
    have hkill : (aeval M μ) *ᵥ (Pi.single (0 : Fin d) 1) = 0 := by simp [minpoly.aeval]
    rw [aeval_eq_sum_pow μ rfl M, sum_mulVec'] at hkill
    simp only [Matrix.smul_mulVec] at hkill
    -- Rewrite: M^k *ᵥ e₀ = eₖ for k ≤ deg μ < d
    have hterms : ∑ k ∈ Finset.range (μ.natDegree + 1),
        μ.coeff k • (M ^ k) *ᵥ (Pi.single (0 : Fin d) 1) =
        ∑ k : Fin (μ.natDegree + 1),
          μ.coeff k.val • (Pi.single ⟨k.val, Nat.lt_trans k.isLt hlt⟩ 1 : Fin d → F) := by
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1; funext k
      rw [companionMatrix_pow_basis p k.val (Nat.lt_trans k.isLt hlt)]
    rw [hterms] at hkill
    -- Evaluate at i = ⟨μ.natDegree, hlt⟩ to extract leading coefficient
    have hval := congr_fun hkill ⟨μ.natDegree, hlt⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.zero_apply,
               Fin.mk.injEq] at hval
    -- Collapse sum: only k = μ.natDegree contributes at index μ.natDegree
    rw [Finset.sum_eq_single ⟨μ.natDegree, Nat.lt_succ_self _⟩
        (fun k _ hk => by simp [show k.val ≠ μ.natDegree from fun h => hk (Fin.ext h)])
        (fun h => absurd (Finset.mem_univ _) h)] at hval
    simp only [↓reduceIte, mul_one] at hval
    -- hval : μ.coeff μ.natDegree = 0, but μ.leadingCoeff = 1
    exact one_ne_zero (hμ_monic.leadingCoeff ▸ hval)
  obtain ⟨q, hq⟩ := hdvd
  have hq_monic : q.Monic := Polynomial.Monic.of_mul_monic_left hμ_monic (hq ▸ hp)
  have hq_natdeg : q.natDegree = 0 := by
    have := hq ▸ Polynomial.natDegree_mul hμ_monic.ne_zero hq_monic.ne_zero
    linarith [le_antisymm hdeg_le hdeg_ge, hdeg]
  have hq_eq : q = 1 := by
    have h0 := Polynomial.eq_C_of_natDegree_eq_zero hq_natdeg
    have h1 : q.coeff 0 = 1 := by
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hq_natdeg] at hq_monic; exact hq_monic
    rw [h0, h1, map_one]
  rw [hq, hq_eq, mul_one]

/-- **The characteristic polynomial of C(p) equals p.**

Proof: minpoly M = p, and minpoly | charpoly with both monic of degree d. -/
theorem charpoly_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    (companionMatrix (d := d) p).charpoly = p := by
  set M := companionMatrix (d := d) p
  have hdvd : p ∣ M.charpoly :=
    (minpoly_companionMatrix hp hdeg) ▸ Matrix.minpoly_dvd_charpoly M
  have hchar_monic : M.charpoly.Monic := Matrix.charpoly_monic M
  have hchar_deg : M.charpoly.natDegree = d := by
    rw [Matrix.charpoly_natDegree_eq_dim]; rfl
  obtain ⟨q, hq⟩ := hdvd
  have hq_monic : q.Monic := Polynomial.Monic.of_mul_monic_left hp (hq ▸ hchar_monic)
  have hq_natdeg : q.natDegree = 0 := by
    have := hq ▸ Polynomial.natDegree_mul hp.ne_zero hq_monic.ne_zero
    linarith [hdeg, hchar_deg]
  have hq_eq : q = 1 := by
    have h0 := Polynomial.eq_C_of_natDegree_eq_zero hq_natdeg
    have h1 : q.coeff 0 = 1 := by
      rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hq_natdeg] at hq_monic; exact hq_monic
    rw [h0, h1, map_one]
  rw [hq, hq_eq, mul_one]

/-! ## Part 4: Trivial Case — Linear Polynomial -/

/-- For p(x) = x - c, the companion matrix is the 1×1 matrix [c].
This is the base case for RCF: eigenvalues correspond to 1×1 companion blocks. -/
theorem companionMatrix_linear (c : F) :
    companionMatrix (d := 1) (X - C c) = Matrix.of (fun _ _ => c) := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [companionMatrix, Matrix.of]
  have : i = 0 := by omega
  have : j = 0 := by omega
  subst_vars
  simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

/-! ## Part 5: RCF Roadmap

### Full Rational Canonical Form Statement

**Theorem (RCF)**: For any matrix A ∈ Mₙ(F), there exist unique monic
polynomials p₁ | p₂ | ... | pₖ (the invariant factors of A) with
pₖ = minpoly(F, A) and p₁ · p₂ · ... · pₖ = charpoly(A) such that
A is similar to the block diagonal matrix

  diag(C(p₁), C(p₂), ..., C(pₖ))

### Infrastructure Needed

1. **Smith Normal Form** for matrices over F[X] (a PID):
   - Elementary row/column operations
   - Euclidean algorithm for F[X]
   - Diagonalization theorem
   - ~800 lines, main theoretical blocker

2. **xI - A as a polynomial matrix**:
   - Map from Mₙ(F) to Mₙ(F[X])
   - Invariant factors of xI - A are the invariant factors of A
   - ~200 lines

3. **Block diagonal similarity**:
   - Block diagonal construction from list of matrices
   - Similarity to block form via change of basis
   - ~300 lines

4. **Uniqueness**:
   - Same invariant factors ↔ similar matrices
   - Follows from uniqueness of Smith normal form
   - ~200 lines
-/

#check @companionMatrix
#check @charpoly_companionMatrix
#check @minpoly_companionMatrix
#check @aeval_companionMatrix
#check @companionMatrix_linear

end CayleyHamiltonReductionOQ02OQ01
