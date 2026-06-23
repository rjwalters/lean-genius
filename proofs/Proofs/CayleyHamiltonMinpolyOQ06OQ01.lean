import Mathlib

/-
# Rational Canonical Form readout: minimal polynomial plus invariant factors

The rational canonical form (Frobenius normal form) writes every matrix over a
field as a block-diagonal sum of companion matrices

    C(f₁) ⊕ C(f₂) ⊕ … ⊕ C(f_k),     f₁ ∣ f₂ ∣ … ∣ f_k,

whose blocks are the *invariant factors* `fᵢ`.  The standard "readout" of this
form recovers the two distinguished polynomials of the matrix from its invariant
factors:

  * the **characteristic polynomial** is the *product* of the invariant factors,
    `charpoly = ∏ᵢ fᵢ`; and
  * the **minimal polynomial** is the *largest* invariant factor,
    `minpoly = f_k`  (largest in the divisibility order, since the `fᵢ` form a
    chain).

This file proves the readout for the **two-invariant-factor case** (the
inductive heart of the general statement; the `k`-block case requires a
`Sigma`-indexed block matrix, since companion blocks of different degrees do not
fit Mathlib's uniform `blockDiagonal`).  Crucially the statement is given for
*arbitrary nonderogatory blocks* — a block `A` is nonderogatory when
`minpoly A = charpoly A`, and that common value is its invariant factor — so it
applies verbatim to companion matrices:
`Matrix.charpoly_companionMatrix`/`Matrix.minpoly_companionMatrix` in
`Proofs.CayleyHamiltonReductionOQ02OQ01` show `charpoly (C f) = minpoly (C f) = f`,
exactly the nonderogatory hypothesis below.

## What is new here

Mathlib (v4.26.0) has `Matrix.charpoly_fromBlocks_zero₁₂` (the characteristic
polynomial of a block-triangular matrix is the product of the diagonal blocks'
characteristic polynomials) but **no** statement about the *minimal* polynomial
of a block-diagonal matrix.  The core new results are:

  * `aeval_fromBlocks` — polynomial evaluation distributes over a block-diagonal
    matrix: `q(A ⊕ D) = q(A) ⊕ q(D)`;
  * `minpoly_fromBlocks_of_dvd` — when the blocks' minimal polynomials form a
    divisibility chain `minpoly A ∣ minpoly D`, the minimal polynomial of the
    block-diagonal sum is the larger one, `minpoly D`.  (In general it is the
    lcm; the chain hypothesis, automatic for invariant factors, collapses the
    lcm to the larger element and avoids any normalisation bookkeeping.)

Everything is sorry-free and axiom-free (`import Mathlib` only).

## Open question addressed

`cayley-hamilton-minpoly-oq-06-oq-01`: "Rational Canonical Form: Minimal
Polynomial Plus Invariant Factors", a follow-up to
`cayley-hamilton-minpoly-oq-06` ("similar matrices share a minimal polynomial").
-/

namespace CayleyHamiltonMinpolyOQ06OQ01

open Matrix Polynomial BigOperators

variable {F : Type*} [Field F]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {o : Type*} [Fintype o] [DecidableEq o]

/-! ## Part 1: `algebraMap` and polynomial evaluation on a block-diagonal matrix -/

/-- The scalar matrix `algebraMap F (Matrix (m ⊕ o)) a` is the block-diagonal sum
of the two scalar blocks `algebraMap F (Matrix m) a` and
`algebraMap F (Matrix o) a`. -/
theorem algebraMap_fromBlocks (a : F) :
    algebraMap F (Matrix (m ⊕ o) (m ⊕ o) F) a
      = Matrix.fromBlocks (algebraMap F (Matrix m m F) a) 0 0
          (algebraMap F (Matrix o o F) a) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_smul]
  simp

/-- **Polynomial evaluation distributes over a block-diagonal matrix.**
For any polynomial `q`, `q(A ⊕ D) = q(A) ⊕ q(D)`, where `A ⊕ D` is the
block-diagonal matrix `fromBlocks A 0 0 D`. -/
theorem aeval_fromBlocks (A : Matrix m m F) (D : Matrix o o F) (q : F[X]) :
    aeval (Matrix.fromBlocks A 0 0 D) q
      = Matrix.fromBlocks (aeval A q) 0 0 (aeval D q) := by
  refine Polynomial.induction_on' q (fun p₁ p₂ ih₁ ih₂ => ?_) (fun n a => ?_)
  · rw [map_add, map_add, map_add, ih₁, ih₂, Matrix.fromBlocks_add, add_zero, add_zero]
  · simp only [aeval_monomial]
    rw [Matrix.fromBlocks_diagonal_pow, algebraMap_fromBlocks,
        Matrix.fromBlocks_multiply]
    simp

/-! ## Part 2: characteristic and minimal polynomials of a block-diagonal matrix -/

/-- **Characteristic polynomial of a block-diagonal matrix** is the product of
the blocks' characteristic polynomials.  (A direct restatement of Mathlib's
`Matrix.charpoly_fromBlocks_zero₁₂`, recorded here for the RCF readout.) -/
theorem charpoly_fromBlocks (A : Matrix m m F) (D : Matrix o o F) :
    (Matrix.fromBlocks A 0 0 D).charpoly = A.charpoly * D.charpoly :=
  Matrix.charpoly_fromBlocks_zero₁₂ A 0 D

/-- **Minimal polynomial of a block-diagonal matrix, divisibility-chain case.**
If the blocks' minimal polynomials form a divisibility chain
`minpoly A ∣ minpoly D`, then the minimal polynomial of the block-diagonal sum
`A ⊕ D` is the larger one, `minpoly D`.

This is the minimal-polynomial counterpart of `charpoly_fromBlocks` and is the
key fact missing from Mathlib.  The proof is a clean two-way divisibility:
`minpoly D` annihilates `A ⊕ D` (it annihilates `D`, and divides—hence
annihilates through—`minpoly A`), giving `minpoly (A ⊕ D) ∣ minpoly D`; and
reading off the bottom-right block of `(minpoly (A ⊕ D))(A ⊕ D) = 0` shows
`minpoly D ∣ minpoly (A ⊕ D)`.  Two monic associates are equal. -/
theorem minpoly_fromBlocks_of_dvd (A : Matrix m m F) (D : Matrix o o F)
    (hdvd : minpoly F A ∣ minpoly F D) :
    minpoly F (Matrix.fromBlocks A 0 0 D) = minpoly F D := by
  set B := Matrix.fromBlocks A 0 0 D with hB
  have hDint : IsIntegral F D := Matrix.isIntegral D
  have hBint : IsIntegral F B := Matrix.isIntegral B
  -- `minpoly D` annihilates `A` as well (since `minpoly A ∣ minpoly D`).
  have hAevalD : aeval A (minpoly F D) = 0 := by
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  -- Hence `minpoly D` annihilates the whole block-diagonal matrix.
  have hannih : aeval B (minpoly F D) = 0 := by
    rw [hB, aeval_fromBlocks, hAevalD, minpoly.aeval, Matrix.fromBlocks_zero]
  have hdvd1 : minpoly F B ∣ minpoly F D := minpoly.dvd F B hannih
  -- Conversely, `minpoly D ∣ minpoly B`: read off the bottom-right block of
  -- `(minpoly B)(B) = 0`.
  have hDaeval : aeval D (minpoly F B) = 0 := by
    have hz : Matrix.fromBlocks (aeval A (minpoly F B)) 0 0 (aeval D (minpoly F B))
        = 0 := by rw [← aeval_fromBlocks, ← hB]; exact minpoly.aeval F B
    ext i j
    have h := congr_fun (congr_fun hz (Sum.inr i)) (Sum.inr j)
    rwa [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] at h
  have hdvd2 : minpoly F D ∣ minpoly F B := minpoly.dvd F D hDaeval
  exact Polynomial.eq_of_monic_of_associated (minpoly.monic hBint) (minpoly.monic hDint)
    (associated_of_dvd_dvd hdvd1 hdvd2)

/-! ## Part 3: the rational-canonical-form readout for two invariant factors -/

/-- **Rational canonical form readout (two invariant factors).**

Let `A`, `D` be two *nonderogatory* blocks: `A` has `minpoly A = charpoly A = f₁`
and `D` has `minpoly D = charpoly D = f₂`, with the invariant factors forming a
chain `f₁ ∣ f₂`.  (Companion matrices `C(f₁)`, `C(f₂)` are exactly such blocks.)

Then the block-diagonal matrix `A ⊕ D` realises the two defining RCF relations:

  * its **characteristic polynomial** is the *product* `f₁ · f₂` of the invariant
    factors, and
  * its **minimal polynomial** is the *largest* invariant factor `f₂`. -/
theorem rcf_two_invariant_factors
    (A : Matrix m m F) (D : Matrix o o F) (f₁ f₂ : F[X])
    (hA_min : minpoly F A = f₁) (hA_char : A.charpoly = f₁)
    (hD_min : minpoly F D = f₂) (hD_char : D.charpoly = f₂)
    (hchain : f₁ ∣ f₂) :
    (Matrix.fromBlocks A 0 0 D).charpoly = f₁ * f₂
      ∧ minpoly F (Matrix.fromBlocks A 0 0 D) = f₂ := by
  refine ⟨?_, ?_⟩
  · rw [charpoly_fromBlocks, hA_char, hD_char]
  · rw [minpoly_fromBlocks_of_dvd A D (by rw [hA_min, hD_min]; exact hchain), hD_min]

end CayleyHamiltonMinpolyOQ06OQ01
