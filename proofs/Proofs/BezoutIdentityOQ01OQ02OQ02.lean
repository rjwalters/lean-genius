/-
  Transitivity of SLₙ(ℤ) on primitive vectors — the SLₙ generalization of Bézout reduction
  Open Question: bezout-identity-oq-01-oq-02-oq-02

  The grandparent entry (bezout-identity-oq-01-oq-02) realizes the extended Euclidean algorithm as a
  single unimodular matrix `U(a,b) ∈ SL₂(ℤ)` carrying a primitive pair `(a, b)` (i.e.
  `IsCoprime a b`) to the standard basis vector `(1, 0)`.  That is the `n = 2` case of the classical
  fact that `SLₙ(ℤ)` acts transitively on primitive integer vectors: for every `v ∈ ℤⁿ` whose
  entries have gcd `1`, there is a matrix `M ∈ SLₙ(ℤ)` with `M ·ᵥ v = e₀`.  Its open question asks
  to *generalize to SLₙ(ℤ): construct a unimodular n×n matrix carrying an arbitrary primitive
  integer vector to the first standard basis vector.*

  This entry builds the reduction engine and verifies the first genuinely new cases.

    * **`embedOne` — the induction engine.**  Any `M ∈ SLₙ(ℤ)` extends to
      `embedOne M ∈ SL₍ₙ₊₁₎(ℤ)` acting as the block matrix `diag(1, M)`.  We prove it is
      determinant `1` (`det_embedOne`) and that its action fixes the head coordinate and applies
      `M` to the tail (`embedOne_mulVec`):

            embedOne M ·ᵥ (a ::ᵥ w) = a ::ᵥ (M ·ᵥ w).

      This is exactly the step that reduces `SL₍ₙ₊₁₎`-transitivity to `SLₙ`-transitivity: clear the
      tail with an `SLₙ` matrix, leaving `(v₀, g, 0, …, 0)`.

    * **Base case `n = 2`.**  `sl2_transitive` repackages the grandparent's `bezoutMatrix`: a
      primitive pair is carried to `(1, 0)` by an element of `SL₂(ℤ)`.

    * **First new case `n = 3`.**  `sl3_transitive` carries an arbitrary primitive
      `(a, b, c) ∈ ℤ³` (encoded as `IsCoprime a (gcd b c)`) to `(1, 0, 0)` by an explicit product of
      two block reductions — first `embedOne` clears `c` against `b` (the `SL₂` Bézout step on the
      last two coordinates, sending `(a, b, c) ↦ (a, gcd(b,c), 0)`), then a concrete `SL₂`-in-`SL₃`
      block clears the resulting second coordinate against the first (`(a, gcd(b,c), 0) ↦
      (1, 0, 0)`).  This is the smallest case beyond the grandparent and exhibits the general
      two-step reduction pattern; the degenerate `gcd(b,c) = 0` case (the tail vanishes) is folded in
      by using the identity as the tail reducer.

  The general induction on `n` follows this template — `embedOne` of an `SLₙ` tail-reducer followed
  by an `SL₂`-in-`SL₍ₙ₊₁₎` head block — and its two remaining ingredients (an `SL₂`-in-`SL₍ₙ₊₁₎`
  block embedding for arbitrary `n`, and the `Finset.gcd` content bridge) are recorded as next
  steps.

  Everything is derived from Mathlib's `Matrix` / `SpecialLinearGroup` machinery and the
  grandparent's Bézout matrix; no new axioms are introduced.

  References:
  - Newman, "Integral Matrices" (1972), Ch. II (elementary divisors, unimodular reduction).
  - Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup, Mathlib.LinearAlgebra.Matrix.Transvection.
  - Grandparent: BezoutIdentityOQ01OQ02.lean (`bezoutMatrix`, `bezoutMatrix_mulVec_coprime`).
-/

import Mathlib
import Proofs.BezoutIdentityOQ01OQ02

namespace BezoutIdentityOQ01OQ02OQ02

open Matrix

/-! ### The induction engine: `SLₙ(ℤ) ↪ SL₍ₙ₊₁₎(ℤ)` as `diag(1, M)` -/

/-- Extend an `n×n` matrix `M` to the `(n+1)×(n+1)` block matrix `diag(1, M)`: the top-left entry
is `1`, the first row and column are otherwise zero, and the bottom-right block is `M`. -/
def embedOne {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))

@[simp] theorem embedOne_zero_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    embedOne M 0 0 = 1 := rfl

@[simp] theorem embedOne_zero_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    embedOne M 0 j.succ = 0 := rfl

@[simp] theorem embedOne_succ_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    embedOne M i.succ 0 = 0 := rfl

@[simp] theorem embedOne_succ_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    embedOne M i.succ j.succ = M i j := rfl

/-- `det (diag(1, M)) = det M`: expand along the first column, whose only nonzero entry is the
top-left `1`, and identify the resulting minor with `M`. -/
theorem det_embedOne {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (embedOne M).det = M.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hrest : ∀ i : Fin n,
      (-1) ^ (i.succ : ℕ) * embedOne M i.succ 0 *
        ((embedOne M).submatrix i.succ.succAbove Fin.succ).det = 0 := by
    intro i; simp
  simp only [hrest, Finset.sum_const_zero, add_zero]
  simp only [Fin.val_zero, pow_zero, embedOne_zero_zero, one_mul, Fin.succAbove_zero]
  -- the surviving minor `(embedOne M).submatrix succ succ` is definitionally `M`
  rfl

/-- The action of `diag(1, M)` fixes the head coordinate and applies `M` to the tail. -/
theorem embedOne_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (a : ℤ) (w : Fin n → ℤ) :
    embedOne M *ᵥ Fin.cons a w = Fin.cons a (M *ᵥ w) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · -- head coordinate
    simp [embedOne, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · -- tail coordinate `k.succ`
    simp [embedOne, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_succ]

/-- `embedOne` as an element of the special linear group. -/
def embedOneSL {n : ℕ} (M : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) ℤ :=
  ⟨embedOne (M : Matrix (Fin n) (Fin n) ℤ), by
    rw [det_embedOne]; exact M.2⟩

@[simp] theorem embedOneSL_coe {n : ℕ} (M : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    (embedOneSL M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
      = embedOne (M : Matrix (Fin n) (Fin n) ℤ) := rfl

/-! ### Base case: `SL₂(ℤ)` acts transitively on primitive pairs -/

/-- **`n = 2`.**  A primitive pair `(a, b)` (`IsCoprime a b`) is carried to `(1, 0)` by an element
of `SL₂(ℤ)`. This is the grandparent's `bezoutMatrix`, repackaged as transitivity. -/
theorem sl2_transitive (a b : ℤ) (h : IsCoprime a b) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (M : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![a, b] = ![1, 0] :=
  ⟨BezoutIdentityOQ01OQ02.bezoutSL a b h, BezoutIdentityOQ01OQ02.bezoutSL_mulVec a b h⟩

/-! ### First new case: `SL₃(ℤ)` acts transitively on primitive triples -/

/-- The concrete `SL₂`-in-`SL₃` head block `diag(N, 1)` acting on the first two coordinates. -/
def headBlock3 (N : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![N 0 0, N 0 1, 0; N 1 0, N 1 1, 0; 0, 0, 1]

theorem det_headBlock3 (N : Matrix (Fin 2) (Fin 2) ℤ) :
    (headBlock3 N).det = N.det := by
  rw [headBlock3, Matrix.det_fin_three, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val']
  ring

theorem headBlock3_mulVec (N : Matrix (Fin 2) (Fin 2) ℤ) (x y z : ℤ) :
    headBlock3 N *ᵥ ![x, y, z]
      = ![N 0 0 * x + N 0 1 * y, N 1 0 * x + N 1 1 * y, z] := by
  funext i
  fin_cases i <;>
    simp [headBlock3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **`n = 3`.**  An arbitrary primitive triple `(a, b, c)` (entries with gcd `1`, encoded as
`IsCoprime a (Int.gcd b c)`) is carried to `(1, 0, 0)` by an element of `SL₃(ℤ)`.

The reduction is the general two-step pattern made concrete:
1. `embedOne` of a tail reducer `T` sends `(a, b, c) ↦ (a, gcd(b,c), 0)`;
2. the head block `diag(bezout(a, gcd b c), 1)` sends `(a, gcd(b,c), 0) ↦ (1, 0, 0)`,
using `IsCoprime a (gcd b c)`. -/
theorem sl3_transitive (a b c : ℤ) (h : IsCoprime a (Int.gcd b c : ℤ)) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 3) ℤ,
      (M : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ ![a, b, c] = ![1, 0, 0] := by
  set g : ℤ := (Int.gcd b c : ℤ) with hg
  -- Tail reducer: identity when `gcd b c = 0` (then `b = c = 0`), else the Bézout matrix.
  set T : Matrix (Fin 2) (Fin 2) ℤ :=
    if Int.gcd b c = 0 then 1 else BezoutIdentityOQ01OQ02.bezoutMatrix b c with hT
  have hTdet : T.det = 1 := by
    rw [hT]; split
    · exact Matrix.det_one
    · rename_i hbc; exact BezoutIdentityOQ01OQ02.bezoutMatrix_det b c hbc
  have hTw : T *ᵥ ![b, c] = ![g, 0] := by
    rw [hT]; split
    · rename_i hbc
      obtain ⟨hb, hc⟩ := Int.gcd_eq_zero_iff.mp hbc
      subst hb; subst hc
      rw [hg]; simp
    · exact BezoutIdentityOQ01OQ02.bezoutMatrix_mulVec b c
  -- Head reducer: Bézout on `(a, gcd b c)`, coprime by hypothesis.
  have hgac : Int.gcd a g = 1 := Int.isCoprime_iff_gcd_eq_one.mp h
  set H : Matrix (Fin 2) (Fin 2) ℤ := BezoutIdentityOQ01OQ02.bezoutMatrix a g with hH
  have hHdet : H.det = 1 :=
    BezoutIdentityOQ01OQ02.bezoutMatrix_det a g (by rw [hgac]; exact one_ne_zero)
  have hHw : H *ᵥ ![a, g] = ![1, 0] :=
    BezoutIdentityOQ01OQ02.bezoutMatrix_mulVec_coprime a g h
  -- Assemble the SL₃ element.
  refine ⟨⟨headBlock3 H * embedOne T, ?_⟩, ?_⟩
  · rw [Matrix.det_mul, det_headBlock3, det_embedOne, hHdet, hTdet, mul_one]
  · show (headBlock3 H * embedOne T) *ᵥ ![a, b, c] = ![1, 0, 0]
    -- `![…]` is `Matrix.vecCons`; convert to `Fin.cons` so the reduction lemmas fire.
    have hcons : (![a, b, c] : Fin 3 → ℤ) = Fin.cons a ![b, c] := rfl
    have hcons2 : (Fin.cons a (![g, 0] : Fin 2 → ℤ) : Fin 3 → ℤ) = ![a, g, 0] := rfl
    rw [← Matrix.mulVec_mulVec, hcons, embedOne_mulVec, hTw, hcons2, headBlock3_mulVec]
    funext i
    fin_cases i
    · -- first coordinate: `H 0 0 * a + H 0 1 * g = 1`
      have := congrFun hHw 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    · -- second coordinate: `H 1 0 * a + H 1 1 * g = 0`
      have := congrFun hHw 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    · -- third coordinate: `0 = 0`
      simp

end BezoutIdentityOQ01OQ02OQ02
