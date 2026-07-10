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

  The companion module `BezoutIdentityOQ01OQ02OQ02` (namespace `BezoutPrimitive`) proves the *easy
  half* — every vector in the `SLₙ(ℤ)`-orbit of a basis vector is primitive (`orbit_e_isPrimitive`),
  i.e. primitivity is *necessary* — and records the transvection generators, but explicitly leaves
  the converse (sufficiency) as "the remaining Euclidean-descent construction".  This module builds
  exactly that constructive descent: the block-embedding reduction engine and the verified base
  cases, working toward the sufficiency direction the companion module leaves open.

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

    * **General head block `headBlockN`.**  The arbitrary-`n` analogue of `headBlock3`:
      `diag(N, Iₘ) ∈ SL₍₂₊ₘ₎(ℤ)` for a `2×2` block `N`, built as `fromBlocks N 0 0 1` reindexed by
      `finSumFinEquiv`.  We prove `det (diag(N, Iₘ)) = det N` (`det_headBlockN`) and the split action
      `diag(N, Iₘ) ·ᵥ (u ++ w) = (N ·ᵥ u) ++ w` (`headBlockN_mulVec`).  Together with `embedOne`
      this supplies *both* reduction steps of the general induction for arbitrary `n`.

  The general induction on `n` follows this template — `embedOne` of an `SLₙ` tail-reducer followed
  by the head block `headBlockN` — with the single remaining ingredient being the `Fin.cons`/
  `Fin.append` content bridge (packaging the tail-reduced vector `(v₀, g, 0, …, 0)` as an
  `Fin.append` and threading the `Int.gcd` bookkeeping through the induction), recorded as the next
  step.

  Everything is derived from Mathlib's `Matrix` / `SpecialLinearGroup` machinery and the
  grandparent's Bézout matrix; no new axioms are introduced.

  References:
  - Newman, "Integral Matrices" (1972), Ch. II (elementary divisors, unimodular reduction).
  - Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup, Mathlib.LinearAlgebra.Matrix.Transvection.
  - Grandparent: BezoutIdentityOQ01OQ02.lean (`bezoutMatrix`, `bezoutMatrix_mulVec_coprime`).
-/

import Mathlib
import Proofs.BezoutIdentityOQ01OQ02

namespace BezoutDescent

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
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
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

/-! ### General head block: `SL₂(ℤ) ↪ SL₍₂₊ₘ₎(ℤ)` on the first two coordinates -/

/-- The general `SL₂`-in-`SL₍₂₊ₘ₎` head block `diag(N, Iₘ)`: the `2×2` matrix `N` acts on the first
two coordinates and the identity on the remaining `m`.  Built as `fromBlocks N 0 0 1` reindexed by
`finSumFinEquiv`.  For `m = 1` this is the concrete `headBlock3`; it is the arbitrary-`n` head
reducer required for the general induction. -/
def headBlockN {m : ℕ} (N : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ :=
  (Matrix.fromBlocks N 0 0 (1 : Matrix (Fin m) (Fin m) ℤ)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- `det (diag(N, Iₘ)) = det N`: the reindexing preserves the determinant (`det_submatrix_equiv_self`)
and the block form is block-triangular with an identity corner (`det_fromBlocks_zero₂₁`). -/
theorem det_headBlockN {m : ℕ} (N : Matrix (Fin 2) (Fin 2) ℤ) :
    (headBlockN N).det = N.det := by
  have hsub : (headBlockN N).det
      = (Matrix.fromBlocks N 0 0 (1 : Matrix (Fin m) (Fin m) ℤ)).det :=
    Matrix.det_submatrix_equiv_self finSumFinEquiv.symm _
  rw [hsub, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- The action of `diag(N, Iₘ)` applies `N` to the first two coordinates and fixes the last `m`;
vectors are split with `Fin.append`. This is the general-`n` analogue of `headBlock3_mulVec` and,
paired with `embedOne_mulVec`, supplies both reduction steps of the general induction. -/
theorem headBlockN_mulVec {m : ℕ} (N : Matrix (Fin 2) (Fin 2) ℤ)
    (u : Fin 2 → ℤ) (w : Fin m → ℤ) :
    headBlockN N *ᵥ Fin.append u w = Fin.append (N *ᵥ u) w := by
  rw [headBlockN, submatrix_mulVec_equiv]
  have h1 : (Fin.append u w) ∘ ⇑(finSumFinEquiv.symm.symm) = Sum.elim u w := by
    rw [Equiv.symm_symm]; exact Fin.append_comp_sumElim
  rw [h1, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.one_mulVec,
    add_zero, zero_add]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
  · simp [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]

/-- `headBlockN` packaged as an element of `SL₍₂₊ₘ₎(ℤ)`. -/
def headBlockNSL {m : ℕ} (N : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.SpecialLinearGroup (Fin (2 + m)) ℤ :=
  ⟨headBlockN (N : Matrix (Fin 2) (Fin 2) ℤ), by
    rw [det_headBlockN]; exact N.2⟩

end BezoutDescent
