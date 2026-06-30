import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic
import Proofs.CayleyHamiltonReductionOQ02OQ01

/-
# Rational Canonical Form: Block-Diagonal Assembly of Companion Blocks

## Open Question
Formalize the rational canonical form (Frobenius normal form) in Lean 4.

This file is a follow-up leaf of `CayleyHamiltonReductionOQ02OQ01` (the companion
matrix `C(p)` with the proven facts `charpoly C(p) = p`, `minpoly C(p) = p`,
`p(C(p)) = 0`). The parent file's roadmap flagged **block-diagonal assembly**
(~300 lines) as "not started". This file builds the assembly *invariants* — the
two facts that make the block-diagonal of companion matrices the rational
canonical form:

For the block-diagonal matrix `B = C(p) ⊕ C(q) = fromBlocks C(p) 0 0 C(q)`:

1. **Characteristic polynomial multiplies**:  `charpoly B = p * q`.
2. **Annihilation by the product**:           `(p·q)(B) = 0`.
3. **Minimal polynomial is the lcm**:         `minpoly B = lcm p q`.

(1) is the charpoly side of RCF: the characteristic polynomial of the
block-diagonal companion form is the *product of the invariant factors*.
(3) is the minimal-polynomial side: the minimal polynomial of a block-diagonal
matrix is the **least common multiple** of the blocks' minimal polynomials,
which for companion blocks is `lcm p q`. The non-derogatory characterization
`minpoly = charpoly` of a single companion block (parent file) therefore breaks
for a *direct sum* of companion blocks unless the factors are coprime: in
general `lcm p q ∣ p·q` strictly. This is exactly the phenomenon RCF captures.

## What is new here (relative to the parent and to Mathlib)
- Mathlib has `Matrix.charpoly_fromBlocks_zero₂₁` (charpoly of a block-triangular
  matrix factors) and `Matrix.fromBlocks_diagonal_pow`, but no companion matrix
  and no statement assembling companion blocks into RCF invariants.
- `aeval_fromBlocks_diag`: polynomial evaluation is block-diagonal-respecting,
  `aeval (A ⊕ D) f = (aeval A f) ⊕ (aeval D f)`. This is the algebraic engine
  behind both the annihilation and the minimal-polynomial computation.
- The `minpoly B = lcm p q` result is the genuine RCF content: it is proved by a
  two-sided divisibility (`minpoly B ∣ lcm` from annihilation, `lcm ∣ minpoly B`
  from the block projection) plus monic uniqueness.

## Status
- [x] `aeval_fromBlocks_diag` : aeval respects block-diagonal direct sums
- [x] `charpoly_companion_block` : charpoly (C(p) ⊕ C(q)) = p * q
- [x] `aeval_companion_block_mul` : (p*q)(C(p) ⊕ C(q)) = 0
- [x] `minpoly_companion_block` : minpoly (C(p) ⊕ C(q)) = lcm p q
-/

namespace CayleyHamiltonReductionOQ02OQ01WIP01

open Matrix Polynomial BigOperators
open CayleyHamiltonReductionOQ02OQ01

variable {F : Type*} [Field F]

/-! ## Part 1: Block-diagonal direct sums of polynomial evaluation -/

/-- A finite sum of block-diagonal matrices is the block-diagonal of the
componentwise sums. -/
private theorem fromBlocks_diag_sum {n m : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) F)
    (h : ι → Matrix (Fin m) (Fin m) F) :
    Matrix.fromBlocks (∑ i ∈ s, g i) 0 0 (∑ i ∈ s, h i)
      = ∑ i ∈ s, Matrix.fromBlocks (g i)
          (0 : Matrix (Fin n) (Fin m) F) (0 : Matrix (Fin m) (Fin n) F) (h i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
        Matrix.fromBlocks_add]
    simp

/-- **Polynomial evaluation respects block-diagonal direct sums.**
`aeval (A ⊕ D) f = (aeval A f) ⊕ (aeval D f)`. -/
theorem aeval_fromBlocks_diag {n m : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (D : Matrix (Fin m) (Fin m) F) (f : F[X]) :
    aeval (Matrix.fromBlocks A 0 0 D) f
      = Matrix.fromBlocks (aeval A f) 0 0 (aeval D f) := by
  rw [Polynomial.aeval_eq_sum_range (Matrix.fromBlocks A 0 0 D),
      Polynomial.aeval_eq_sum_range A, Polynomial.aeval_eq_sum_range D,
      fromBlocks_diag_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.fromBlocks_diagonal_pow, Matrix.fromBlocks_smul]
  simp

/-! ## Part 2: Characteristic polynomial of the block-diagonal companion form -/

/-- **The characteristic polynomial of `C(p) ⊕ C(q)` is `p · q`.**

This is the characteristic-polynomial side of the rational canonical form: the
characteristic polynomial of a block-diagonal of companion matrices is the
product of the corresponding (invariant-factor) polynomials. -/
theorem charpoly_companion_block {dp dq : ℕ} [NeZero dp] [NeZero dq]
    (p q : F[X]) (hp : p.Monic) (hpd : p.natDegree = dp)
    (hq : q.Monic) (hqd : q.natDegree = dq) :
    (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q)).charpoly = p * q := by
  rw [Matrix.charpoly_fromBlocks_zero₂₁,
      charpoly_companionMatrix p hp hpd, charpoly_companionMatrix q hq hqd]

/-- The block-diagonal companion form `C(p) ⊕ C(q)` has characteristic polynomial
of degree `dp + dq` (the dimension of the block matrix), as it must. -/
theorem charpoly_companion_block_natDegree {dp dq : ℕ} [NeZero dp] [NeZero dq]
    (p q : F[X]) (hp : p.Monic) (hpd : p.natDegree = dp)
    (hq : q.Monic) (hqd : q.natDegree = dq) :
    (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q)).charpoly.natDegree = dp + dq := by
  rw [charpoly_companion_block p q hp hpd hq hqd,
      Polynomial.natDegree_mul hp.ne_zero hq.ne_zero, hpd, hqd]

/-! ## Part 3: Annihilation and minimal polynomial -/

/-- **The block-diagonal companion form is annihilated by the product `p · q`.**
Each block is killed: `p` kills `C(p)`, `q` kills `C(q)`. -/
theorem aeval_companion_block_mul {dp dq : ℕ} [NeZero dp] [NeZero dq]
    (p q : F[X]) (hp : p.Monic) (hpd : p.natDegree = dp)
    (hq : q.Monic) (hqd : q.natDegree = dq) :
    aeval (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q)) (p * q) = 0 := by
  rw [aeval_fromBlocks_diag, map_mul, map_mul,
      aeval_companionMatrix p hp hpd, aeval_companionMatrix q hq hqd,
      zero_mul, mul_zero]
  exact Matrix.fromBlocks_zero

/-- **The minimal polynomial of `C(p) ⊕ C(q)` is `lcm p q`.**

This is the minimal-polynomial side of the rational canonical form. Proof: two
divisibilities.
* `minpoly ∣ lcm`: `lcm p q` annihilates both blocks (`p ∣ lcm`, `q ∣ lcm`).
* `lcm ∣ minpoly`: `minpoly` annihilates the whole matrix, hence each block, so
  `p = minpoly C(p)` and `q = minpoly C(q)` both divide `minpoly`.
Both polynomials are monic, so mutual divisibility forces equality. -/
theorem minpoly_companion_block {dp dq : ℕ} [NeZero dp] [NeZero dq] [DecidableEq F]
    (p q : F[X]) (hp : p.Monic) (hpd : p.natDegree = dp)
    (hq : q.Monic) (hqd : q.natDegree = dq) :
    minpoly F (Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
        (companionMatrix (d := dq) q)) = lcm p q := by
  set B := Matrix.fromBlocks (companionMatrix (d := dp) p) 0 0
    (companionMatrix (d := dq) q) with hB
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : q ≠ 0 := hq.ne_zero
  have hlcm0 : lcm p q ≠ 0 := by
    rw [Ne, lcm_eq_zero_iff]; push_neg; exact ⟨hp0, hq0⟩
  -- (a) minpoly B ∣ lcm p q : the lcm annihilates B
  have hmin_dvd : minpoly F B ∣ lcm p q := by
    apply minpoly.dvd
    rw [hB, aeval_fromBlocks_diag]
    obtain ⟨r, hr⟩ := dvd_lcm_left p q
    obtain ⟨s, hs⟩ := dvd_lcm_right p q
    have e1 : aeval (companionMatrix (d := dp) p) (lcm p q) = 0 := by
      rw [hr, map_mul, aeval_companionMatrix p hp hpd, zero_mul]
    have e2 : aeval (companionMatrix (d := dq) q) (lcm p q) = 0 := by
      rw [hs, map_mul, aeval_companionMatrix q hq hqd, zero_mul]
    rw [e1, e2]
    exact Matrix.fromBlocks_zero
  -- (b) lcm p q ∣ minpoly B : minpoly B annihilates each block
  have hlcm_dvd : lcm p q ∣ minpoly F B := by
    have haev : aeval B (minpoly F B) = 0 := minpoly.aeval F B
    rw [hB, aeval_fromBlocks_diag, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at haev
    obtain ⟨h1, -, -, h2⟩ := haev
    apply lcm_dvd
    · rw [← minpoly_companionMatrix p hp hpd]; exact minpoly.dvd F _ h1
    · rw [← minpoly_companionMatrix q hq hqd]; exact minpoly.dvd F _ h2
  -- (c) both monic + mutual divisibility ⇒ equal
  have hlcm_monic : (lcm p q).Monic := by
    rw [← normalize_eq_self_iff_monic hlcm0]
    exact normalize_lcm p q
  exact eq_of_monic_of_associated (minpoly.monic (Matrix.isIntegral B)) hlcm_monic
    (associated_of_dvd_dvd hmin_dvd hlcm_dvd)

#check @aeval_fromBlocks_diag
#check @charpoly_companion_block
#check @aeval_companion_block_mul
#check @minpoly_companion_block

end CayleyHamiltonReductionOQ02OQ01WIP01
