/-
  Schönhage's Recursive HGCD: Correctness Layer

  This file extends the Lehmer-Schönhage hybrid (BinaryGcdOQ03.lean)
  with Schönhage's recursive half-GCD (HGCD). HGCD computes a single
  cofactor matrix M whose application to (a, b) realizes Θ(n) Euclidean
  steps in one full-precision matrix multiplication, by recursing on
  the top half of the bits.

  Scope (correctness only):
  We define `hgcdMatrix : ℕ → ℕ → ℕ → CofactorMatrix` (fuel-indexed,
  total) and prove:

  1. `hgcdMatrix_det_unit` — the matrix returned by HGCD has det ±1.
  2. `cofactor_mul_apply` — composition of cofactor matrices acts on
     pairs by composition of `apply`.
  3. `hgcdMatrix_preserves_gcd` — applying the HGCD matrix to (a, b)
     preserves GCD. This is the operational correctness statement of
     Schönhage's HGCD.

  Toward size reduction (PART V.5):
  We also build the matrix-vector invariant infrastructure that the
  size-reduction proof needs:

  4. `lehmerCofactors_invariant` — row-vector invariant
     `(a₀, b₀) · M = (current pair)` is preserved across
     `lehmerCofactors`, in the row convention required for the
     size-reduction argument (see PART V.5 docstring on conventions).
  5. `lehmerCofactors_invariant_le` — strengthens (4) with the
     residue-monotonicity bound `max ahat' bhat' ≤ max ahat bhat`.

  Out of scope (deferred — see `hgcdMatrix_size_reduction`):
  The bit-complexity claim O(M(n)·log n) requires a Mathlib model of
  fast multiplication and bit operations that does not yet exist.
  Filling that gap is a multi-thousand-line foundational project. The
  size-reduction lemma needed for the complexity claim is stated as
  `hgcdMatrix_size_reduction` below with a focused open question; the
  remaining piece for closing it is a Cramer-inversion entry bound on
  the cofactor matrix.

  References:
    - Schönhage (1971), "Schnelle Berechnung von Kettenbruchentwicklungen"
    - Knuth, TAOCP Vol. 2, §4.5.2, Algorithm L; §4.5.4 for HGCD
    - Stehlé & Zimmermann (2004), "A Binary Recursive Gcd Algorithm"
    - GMP: mpn_hgcd implementation (matches the structure here)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
import Proofs.BinaryGcdOQ03

open Nat Int LehmerGcd

namespace HGcd

-- ═══════════════════════════════════════════════════════════════
-- PART I: COMPOSITION OF COFACTOR MATRICES UNDER `apply`
-- ═══════════════════════════════════════════════════════════════

/-- Cofactor multiplication corresponds to composition of `apply`.
    This is the algebraic statement that `mul` is the right notion
    of "compose two cofactor matrices". -/
theorem cofactor_mul_apply (M N : CofactorMatrix) (a b : ℤ) :
    (M.mul N).apply a b =
      M.apply (N.apply a b).1 (N.apply a b).2 := by
  simp only [CofactorMatrix.mul, CofactorMatrix.apply, Prod.mk.injEq]
  refine ⟨?_, ?_⟩ <;> ring

-- ═══════════════════════════════════════════════════════════════
-- PART II: RECURSIVE HGCD MATRIX (fuel-indexed, total)
-- ═══════════════════════════════════════════════════════════════

/-- The HGCD recursion threshold. Below this, fall back to the
    full Lehmer cofactor accumulation (which itself bottoms out at
    a Euclidean iteration on small approximations). -/
def hgcdThreshold : ℕ := 64

/-- The half-bit shift used by HGCD recursion: ⌈bits(max a b) / 2⌉. -/
def hgcdShift (a b : ℕ) : ℕ := (Nat.log 2 (max a b) + 1) / 2

/-- Schönhage's recursive HGCD, fuel-indexed for totality.

    `hgcdMatrix fuel a b` returns a cofactor matrix M such that:
      - `M.det = ±1` (so M preserves GCD when applied)
      - intuitively, applying M to (a, b) yields a pair whose
        bit-size is roughly half that of (a, b)

    The recursion structure follows Knuth/Schönhage:

      hgcdMatrix(a, b):
        if max a b is small:
          fall back to lehmerCofactors (single-precision
          Euclidean acceleration)
        else:
          s = ⌈bits(max a b) / 2⌉
          â, b̂ = top-half-bit truncations a >> s, b >> s
          M₁ = hgcdMatrix(â, b̂)              -- top-half subproblem
          (u, v) = M₁ applied to full (a, b)   -- full-precision reduce
          M₂ = hgcdMatrix(|u|, |v|)            -- bottom-half subproblem
          return M₂ · M₁

    Termination by `fuel`: the recursive calls always pass `fuel`
    decreased by one. With `fuel = a + b + 1` (or any large enough
    bound), the algorithm always reaches its natural base.

    The body is structured to avoid `let`-bindings in the recursive
    branch: the same `M₁ := hgcdMatrix fuel (a >> s) (b >> s)` term
    appears explicitly twice. This is intentional — it keeps the
    equation-compiler-generated reduction lemma simple, so proofs
    can `rw [hgcdMatrix]` without needing to unfold any lets. -/
def hgcdMatrix : ℕ → ℕ → ℕ → CofactorMatrix
  | 0, _, _ => CofactorMatrix.id
  | fuel + 1, a, b =>
    if max a b < hgcdThreshold then
      lehmerCofactors hgcdThreshold a b CofactorMatrix.id
    else
      (hgcdMatrix fuel
        ((hgcdMatrix fuel (a / 2 ^ hgcdShift a b)
                          (b / 2 ^ hgcdShift a b)).apply
          (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrix fuel (a / 2 ^ hgcdShift a b)
                          (b / 2 ^ hgcdShift a b)).apply
          (a : ℤ) (b : ℤ)).2.natAbs).mul
      (hgcdMatrix fuel (a / 2 ^ hgcdShift a b)
                       (b / 2 ^ hgcdShift a b))

/-- Top-level entry point: HGCD with sufficient fuel to terminate. -/
def hgcdMatrixOf (a b : ℕ) : CofactorMatrix :=
  hgcdMatrix (a + b + 1) a b

/-- Reduction equation for `hgcdMatrix` at `fuel + 1`.

    Stated explicitly so proofs can `rw` instead of `unfold`/`simp`,
    avoiding fragility with the equation compiler's auto-generated
    lemmas. -/
private theorem hgcdMatrix_succ (f a b : ℕ) :
    hgcdMatrix (f + 1) a b =
      (if max a b < hgcdThreshold then
        lehmerCofactors hgcdThreshold a b CofactorMatrix.id
      else
        (hgcdMatrix f
          ((hgcdMatrix f (a / 2 ^ hgcdShift a b)
                         (b / 2 ^ hgcdShift a b)).apply
            (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrix f (a / 2 ^ hgcdShift a b)
                         (b / 2 ^ hgcdShift a b)).apply
            (a : ℤ) (b : ℤ)).2.natAbs).mul
        (hgcdMatrix f (a / 2 ^ hgcdShift a b)
                      (b / 2 ^ hgcdShift a b))) := rfl

/-- Reduction equation for `hgcdMatrix` at fuel 0. -/
private theorem hgcdMatrix_zero (a b : ℕ) :
    hgcdMatrix 0 a b = CofactorMatrix.id := rfl

-- ═══════════════════════════════════════════════════════════════
-- PART III: DETERMINANT IS ±1 (the operational invariant)
-- ═══════════════════════════════════════════════════════════════

/-- HGCD always returns a cofactor matrix with determinant ±1.

    Proof: induction on fuel.
      - Base (fuel = 0): identity matrix, det = 1.
      - Step: either `lehmerCofactors` (det ±1 by
        `lehmerCofactors_det_unit`) or `M₂.mul M₁` where each
        of M₂, M₁ has det ±1 by IH; product of ±1 is ±1. -/
theorem hgcdMatrix_det_unit (fuel a b : ℕ) :
    (hgcdMatrix fuel a b).det = 1 ∨ (hgcdMatrix fuel a b).det = -1 := by
  induction fuel generalizing a b with
  | zero =>
    rw [hgcdMatrix_zero]
    exact Or.inl CofactorMatrix.det_id
  | succ f ih =>
    rw [hgcdMatrix_succ]
    by_cases hsmall : max a b < hgcdThreshold
    · rw [if_pos hsmall]
      exact lehmerCofactors_det_unit hgcdThreshold a b CofactorMatrix.id
        (Or.inl CofactorMatrix.det_id)
    · rw [if_neg hsmall, CofactorMatrix.det_mul]
      -- Recursive case: result is `(hgcdMatrix f _ _).mul (hgcdMatrix f _ _)`.
      -- Each factor has det ±1 by IH; product of ±1 with ±1 is ±1.
      have h1 := ih (a / 2 ^ hgcdShift a b) (b / 2 ^ hgcdShift a b)
      have h2 := ih
        ((hgcdMatrix f (a / 2 ^ hgcdShift a b)
                       (b / 2 ^ hgcdShift a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrix f (a / 2 ^ hgcdShift a b)
                       (b / 2 ^ hgcdShift a b)).apply (a : ℤ) (b : ℤ)).2.natAbs
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        rw [h1, h2] <;> norm_num

/-- Top-level HGCD has det ±1. -/
theorem hgcdMatrixOf_det_unit (a b : ℕ) :
    (hgcdMatrixOf a b).det = 1 ∨ (hgcdMatrixOf a b).det = -1 :=
  hgcdMatrix_det_unit _ a b

-- ═══════════════════════════════════════════════════════════════
-- PART IV: GCD PRESERVATION (the correctness statement)
-- ═══════════════════════════════════════════════════════════════

/-- Schönhage's HGCD preserves GCD: applying `hgcdMatrix fuel a b`
    to the pair `(a, b)` yields integers whose Int.gcd equals the
    original Nat.gcd of `a` and `b`.

    This is the *operational* correctness statement: any GCD computed
    via the post-HGCD pair is the same as the GCD of the input pair.
    Combined with size reduction (deferred), this gives a recursive
    GCD algorithm that performs Θ(log n) Lehmer-style reductions
    instead of Θ(n) Euclidean steps. -/
theorem hgcdMatrix_preserves_gcd (fuel a b : ℕ) :
    Int.gcd ((hgcdMatrix fuel a b).α * (a : ℤ) + (hgcdMatrix fuel a b).β * (b : ℤ))
            ((hgcdMatrix fuel a b).γ * (a : ℤ) + (hgcdMatrix fuel a b).δ * (b : ℤ))
      = Nat.gcd a b :=
  cofactor_apply_gcd (hgcdMatrix_det_unit fuel a b)

/-- Top-level HGCD preserves GCD. -/
theorem hgcdMatrixOf_preserves_gcd (a b : ℕ) :
    Int.gcd ((hgcdMatrixOf a b).α * (a : ℤ) + (hgcdMatrixOf a b).β * (b : ℤ))
            ((hgcdMatrixOf a b).γ * (a : ℤ) + (hgcdMatrixOf a b).δ * (b : ℤ))
      = Nat.gcd a b :=
  hgcdMatrix_preserves_gcd _ a b

-- ═══════════════════════════════════════════════════════════════
-- PART V: COMPUTATIONAL VERIFICATION (small cases)
-- ═══════════════════════════════════════════════════════════════

/-- Below threshold, HGCD reduces to one Lehmer cofactor accumulation. -/
theorem hgcdMatrix_small (fuel a b : ℕ) (h : max a b < hgcdThreshold) :
    hgcdMatrix (fuel + 1) a b =
      lehmerCofactors hgcdThreshold a b CofactorMatrix.id := by
  rw [hgcdMatrix_succ, if_pos h]

/-- HGCD of (0, 0) is the identity matrix (only the base case fires). -/
example : hgcdMatrix 5 0 0 = CofactorMatrix.id := by native_decide

-- Verify det ±1 on small concrete inputs
example : (hgcdMatrixOf 89 55).det = 1 ∨ (hgcdMatrixOf 89 55).det = -1 :=
  hgcdMatrixOf_det_unit 89 55

example : (hgcdMatrixOf 100 75).det = 1 ∨ (hgcdMatrixOf 100 75).det = -1 :=
  hgcdMatrixOf_det_unit 100 75

-- ═══════════════════════════════════════════════════════════════
-- PART V.5: MATRIX-VECTOR INVARIANT FOR LEHMER COFACTORS
-- (toward size reduction — Steps 1 + 2a of the proof plan)
-- ═══════════════════════════════════════════════════════════════

/-! ### Convention note

The cofactor `CofactorMatrix.apply` is the *column*-vector action:
`M.apply a b = (M.α·a + M.β·b, M.γ·a + M.δ·b)`. This is the right
operator for `cofactor_apply_gcd` (det-based) and `hgcdMatrix_preserves_gcd`
(this file, PART IV).

For the size-reduction lemma, we need the dual *row*-vector relation
`(a₀, b₀) · M = (current pair)`, because that is the invariant
preserved by `lehmerInnerStep` under the update rule
`M' = M.mul ⟨0, 1, 1, -q⟩` (right-multiplication by the Euclidean
step matrix). Concretely, the row product
`(a₀ · M.α + b₀ · M.γ, a₀ · M.β + b₀ · M.δ)` advances by one
Euclidean step on the original pair when M is right-multiplied
by a `[[0, 1], [1, -q]]` step matrix; the column action does not.

This subsection proves Step 1 (matrix-vector invariant in the row
convention) and Step 2a (residue monotonicity), using only the
existing `lehmerCofactors` and `lehmerInnerStep` from
`BinaryGcdOQ03.lean`. The remaining piece — the cofactor-entry
bound via Cramer inversion — is the genuinely novel content of the
size-reduction proof and is the focus of follow-up sessions. -/

/-- Matrix-vector invariant for one Lehmer inner step.

    Given a "ghost original pair" `(a₀, b₀)` consistent with the
    current state `(ahat, bhat, M)` via the row-vector relation
    `a₀·M.α + b₀·M.γ = ahat ∧ a₀·M.β + b₀·M.δ = bhat`, the relation
    persists after one `lehmerInnerStep` to the new state
    `(ahat', bhat', M')`.

    Proof: unfold `lehmerInnerStep` to extract the form of the new
    matrix entries (`α' = M.β`, `β' = M.α - q·M.β`, `γ' = M.δ`,
    `δ' = M.γ - q·M.δ`) and the new pair (`ahat' = bhat`,
    `bhat' = ahat % bhat`). The first conclusion is exactly `h_inv₂`;
    the second follows from `h_inv₁ - q · h_inv₂` and
    `Nat.div_add_mod`. -/
theorem lehmerInnerStep_invariant {a₀ b₀ : ℤ} {ahat bhat : ℕ} {M : CofactorMatrix}
    {ahat' bhat' : ℕ} {M' : CofactorMatrix}
    (h_inv₁ : a₀ * M.α + b₀ * M.γ = (ahat : ℤ))
    (h_inv₂ : a₀ * M.β + b₀ * M.δ = (bhat : ℤ))
    (h_step : lehmerInnerStep ahat bhat M = some (ahat', bhat', M')) :
    a₀ * M'.α + b₀ * M'.γ = (ahat' : ℤ) ∧
    a₀ * M'.β + b₀ * M'.δ = (bhat' : ℤ) := by
  simp [lehmerInnerStep] at h_step
  split at h_step <;> simp_all
  split at h_step <;> simp_all
  -- Surviving case: bhat ≠ 0 and ahat % bhat ≠ 0; the some-equation
  -- has reduced to the equality of the triples.
  obtain ⟨rfl, rfl, rfl⟩ := h_step
  refine ⟨?_, ?_⟩
  · -- a₀ * M'.α + b₀ * M'.γ = a₀ * M.β + b₀ * M.δ = bhat
    exact h_inv₂
  · -- a₀ * (M.α - q·M.β) + b₀ * (M.γ - q·M.δ) = ahat % bhat
    have expand :
        a₀ * (M.α - ((ahat / bhat : ℕ) : ℤ) * M.β)
          + b₀ * (M.γ - ((ahat / bhat : ℕ) : ℤ) * M.δ)
        = (a₀ * M.α + b₀ * M.γ)
            - ((ahat / bhat : ℕ) : ℤ) * (a₀ * M.β + b₀ * M.δ) := by ring
    rw [expand, h_inv₁, h_inv₂]
    -- Goal: (ahat : ℤ) - ↑(ahat/bhat) * (bhat : ℤ) = ↑(ahat % bhat)
    have hdivmod_int :
        (bhat : ℤ) * ((ahat / bhat : ℕ) : ℤ) + ((ahat % bhat) : ℤ) = (ahat : ℤ) := by
      exact_mod_cast Nat.div_add_mod ahat bhat
    linarith

/-- Multi-step matrix-vector invariant for `lehmerCofactors`.

    Existential form: there exist final residues `(ahat', bhat')`
    such that applying the accumulated matrix in row convention to
    the ghost original pair recovers them. Proved by induction on
    `fuel`, applying `lehmerInnerStep_invariant` to the head step. -/
theorem lehmerCofactors_invariant {a₀ b₀ : ℤ} (fuel ahat bhat : ℕ) (M : CofactorMatrix)
    (h_inv₁ : a₀ * M.α + b₀ * M.γ = (ahat : ℤ))
    (h_inv₂ : a₀ * M.β + b₀ * M.δ = (bhat : ℤ)) :
    ∃ ahat' bhat' : ℕ,
      a₀ * (lehmerCofactors fuel ahat bhat M).α
        + b₀ * (lehmerCofactors fuel ahat bhat M).γ = (ahat' : ℤ) ∧
      a₀ * (lehmerCofactors fuel ahat bhat M).β
        + b₀ * (lehmerCofactors fuel ahat bhat M).δ = (bhat' : ℤ) := by
  induction fuel generalizing ahat bhat M with
  | zero => exact ⟨ahat, bhat, h_inv₁, h_inv₂⟩
  | succ n ih =>
    simp only [lehmerCofactors]
    match hstep : lehmerInnerStep ahat bhat M with
    | none => exact ⟨ahat, bhat, h_inv₁, h_inv₂⟩
    | some (ahat'', bhat'', M'') =>
      have ⟨h₁', h₂'⟩ := lehmerInnerStep_invariant h_inv₁ h_inv₂ hstep
      exact ih ahat'' bhat'' M'' h₁' h₂'

/-- Specialisation of `lehmerCofactors_invariant` to `M = id` and the
    "ghost original pair" being the algorithm's actual input pair
    `(ahat, bhat)`.

    Concretely: row-applying the accumulated cofactor matrix to the
    input pair yields the final Euclidean-residue pair. -/
theorem lehmerCofactors_id_apply_eq (fuel ahat bhat : ℕ) :
    ∃ ahat' bhat' : ℕ,
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).α
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).γ
            = (ahat' : ℤ) ∧
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).β
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).δ
            = (bhat' : ℤ) := by
  apply lehmerCofactors_invariant
  · simp [CofactorMatrix.id]
  · simp [CofactorMatrix.id]

/-! ### Residue monotonicity (Step 2a toward size reduction)

The Lehmer-step machine never grows the residues: each successful
inner step sets `ahat' = bhat` and `bhat' = ahat % bhat < bhat`, so
the maximum of the pair is non-increasing. Composed over multiple
steps, this gives the bound `max ahat_final bhat_final ≤
max ahat_initial bhat_initial` for the iterated `lehmerCofactors`. -/

/-- One successful Lehmer inner step strictly decreases `bhat` and
    sets `ahat' = bhat`. -/
theorem lehmerInnerStep_residue_le {ahat bhat : ℕ} {M : CofactorMatrix}
    {ahat' bhat' : ℕ} {M' : CofactorMatrix}
    (h : lehmerInnerStep ahat bhat M = some (ahat', bhat', M')) :
    bhat' < bhat ∧ ahat' = bhat := by
  simp [lehmerInnerStep] at h
  split at h <;> simp_all
  split at h <;> simp_all
  obtain ⟨rfl, rfl, _⟩ := h
  refine ⟨?_, rfl⟩
  -- Goal: ahat % bhat < bhat. omega uses bhat ≠ 0 from context.
  omega

/-- One successful Lehmer inner step does not increase the maximum
    of the pair `(ahat, bhat)`. -/
theorem lehmerInnerStep_max_le {ahat bhat : ℕ} {M : CofactorMatrix}
    {ahat' bhat' : ℕ} {M' : CofactorMatrix}
    (h : lehmerInnerStep ahat bhat M = some (ahat', bhat', M')) :
    max ahat' bhat' ≤ max ahat bhat := by
  obtain ⟨hb_lt, ha_eq⟩ := lehmerInnerStep_residue_le h
  have h1 : ahat' ≤ max ahat bhat := by rw [ha_eq]; exact le_max_right _ _
  have h2 : bhat' ≤ max ahat bhat :=
    le_trans (le_of_lt hb_lt) (le_max_right _ _)
  exact max_le h1 h2

/-- Multi-step matrix-vector invariant for `lehmerCofactors` with the
    additional bound that the final residues do not exceed the initial
    `(ahat, bhat)` in maximum. Strengthens `lehmerCofactors_invariant`. -/
theorem lehmerCofactors_invariant_le {a₀ b₀ : ℤ} (fuel ahat bhat : ℕ)
    (M : CofactorMatrix)
    (h_inv₁ : a₀ * M.α + b₀ * M.γ = (ahat : ℤ))
    (h_inv₂ : a₀ * M.β + b₀ * M.δ = (bhat : ℤ)) :
    ∃ ahat' bhat' : ℕ,
      a₀ * (lehmerCofactors fuel ahat bhat M).α
        + b₀ * (lehmerCofactors fuel ahat bhat M).γ = (ahat' : ℤ) ∧
      a₀ * (lehmerCofactors fuel ahat bhat M).β
        + b₀ * (lehmerCofactors fuel ahat bhat M).δ = (bhat' : ℤ) ∧
      max ahat' bhat' ≤ max ahat bhat := by
  induction fuel generalizing ahat bhat M with
  | zero => exact ⟨ahat, bhat, h_inv₁, h_inv₂, le_refl _⟩
  | succ n ih =>
    simp only [lehmerCofactors]
    match hstep : lehmerInnerStep ahat bhat M with
    | none => exact ⟨ahat, bhat, h_inv₁, h_inv₂, le_refl _⟩
    | some (ahat'', bhat'', M'') =>
      have ⟨h₁', h₂'⟩ := lehmerInnerStep_invariant h_inv₁ h_inv₂ hstep
      have hbound := lehmerInnerStep_max_le hstep
      have ⟨ahat', bhat', hα, hβ, hmax⟩ := ih ahat'' bhat'' M'' h₁' h₂'
      exact ⟨ahat', bhat', hα, hβ, le_trans hmax hbound⟩

/-- Specialisation of `lehmerCofactors_invariant_le` to `M = id` and
    the ghost original pair being the actual input pair `(ahat, bhat)`.

    Combined statement: row-applying the accumulated cofactor matrix to
    `(ahat, bhat)` yields a residue pair `(ahat', bhat')` with
    `max ahat' bhat' ≤ max ahat bhat`. This is the residue-side bound
    used in the size-reduction argument; together with an entry-bound
    on the cofactor matrix it gives the bitsize halving. -/
theorem lehmerCofactors_id_apply_le (fuel ahat bhat : ℕ) :
    ∃ ahat' bhat' : ℕ,
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).α
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).γ
            = (ahat' : ℤ) ∧
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).β
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).δ
            = (bhat' : ℤ) ∧
      max ahat' bhat' ≤ max ahat bhat := by
  apply lehmerCofactors_invariant_le
  · simp [CofactorMatrix.id]
  · simp [CofactorMatrix.id]

-- ═══════════════════════════════════════════════════════════════
-- PART VI: SIZE REDUCTION (deferred — open mathematical content)
-- ═══════════════════════════════════════════════════════════════

/-- The HGCD size-reduction lemma: applying `hgcdMatrix` to `(a, b)`
    yields a pair `(a', b')` whose magnitude is about half of `max a b`.

    This is the only non-trivial mathematical claim that distinguishes
    HGCD from Lehmer's algorithm. Once established (with the right
    constants), iterating HGCD gives O(log n) reductions to size 1,
    each costing one M(n) full-precision matrix-vector multiplication
    — yielding the O(M(n)·log n) complexity bound.

    Stating the lemma precisely requires choosing a `bitsize` measure
    and the constant in front of `bitsize/2`. Standard formulations:

      ‖M·(a,b)‖∞ ≤ ‖(a,b)‖∞ / 2 + O(1)

    where ‖·‖∞ is the max of bit-lengths. The O(1) absorbs the
    "rounding" introduced by truncation of the top half.

    A complete proof requires:
      (a) A clean Lean definition of `bitsize` (or use Nat.log 2 + 1).
      (b) The "advance" lemma for one HGCD step: starting from
          (a, b) with max bitsize n, after applying the recursively
          computed M₁ to full precision, the new max bitsize is
          ≤ n - n/2 + c for some explicit constant c independent of n.
      (c) Composing two such steps for the recursive call structure.

    Open question (this proof obligation):
    Is there a Lean-friendly statement of this lemma that avoids
    deep dependencies on bit-complexity infrastructure? Stehlé and
    Zimmermann (2004) give a careful analysis with explicit constants
    for the binary-recursive variant. -/
theorem hgcdMatrix_size_reduction :
    ∀ (a b : ℕ), 4 ≤ max a b → True := by
  -- Placeholder statement: when filled in, this will assert
  -- a precise size-reduction bound on `hgcdMatrixOf a b`.
  -- See research/problems/binary-gcd-oq-03-oq-02/knowledge.md.
  intros; trivial

/-! ## Summary

**Proved (0 axioms, 0 sorries):**

1. **Composition law** (`cofactor_mul_apply`): cofactor multiplication
   composes the `apply` action correctly. This is the algebraic kernel
   that justifies returning `M₂.mul M₁` from the recursion.

2. **Determinant invariant** (`hgcdMatrix_det_unit`): every matrix
   returned by `hgcdMatrix` has det ±1. Proof by induction on fuel,
   using `lehmerCofactors_det_unit` (BinaryGcdOQ03.lean) at the leaf
   and `det_mul` for the recursive case.

3. **GCD preservation** (`hgcdMatrix_preserves_gcd`): applying the
   HGCD matrix to (a, b) yields a pair with the same GCD. Immediate
   corollary of `cofactor_apply_gcd` (BinaryGcdOQ03.lean) given the
   determinant invariant.

4. **Matrix-vector invariant for Lehmer cofactors**
   (`lehmerInnerStep_invariant`, `lehmerCofactors_invariant`,
   `lehmerCofactors_id_apply_eq`): the row-vector relation
   `(a₀, b₀) · M = (current pair)` is preserved by `lehmerInnerStep`
   and hence by `lehmerCofactors`. This is Step 1 of the size-reduction
   proof plan, working in the row convention dictated by the right-
   multiplication update rule of `lehmerInnerStep` (PART V.5 docstring).

5. **Residue monotonicity** (`lehmerInnerStep_residue_le`,
   `lehmerInnerStep_max_le`, `lehmerCofactors_invariant_le`,
   `lehmerCofactors_id_apply_le`): each Lehmer inner step satisfies
   `bhat' < bhat ∧ ahat' = bhat`, so `max ahat' bhat' ≤ max ahat bhat`;
   this composes through `lehmerCofactors`. Combined with (4), this
   gives the residue-side bound for the size-reduction argument.
   Step 2a of the proof plan.

**Architectural significance:** This file establishes that the
*operational correctness* of Schönhage's recursive HGCD reduces to
the matrix-determinant invariant already proved for Lehmer's
algorithm. The recursion structure adds no new GCD-preservation
obligation — it only redistributes work across recursion levels for
asymptotic complexity gain. The new PART V.5 lays the row-convention
foundation that `hgcdMatrix_size_reduction` (currently a `True`
placeholder) requires; what remains is the Cramer-inversion entry
bound on the cofactor matrix (Step 2b) and a perturbation argument
for the truncated top-half input (Step 3).

**Out of scope (deferred):**

- Bit-complexity bound O(M(n)·log n) (`hgcdMatrix_size_reduction`):
  requires Mathlib infrastructure (fast multiplication, bit-complexity
  model) that does not yet exist. The size-reduction lemma is stated
  as a placeholder; filling it requires a separate Mathlib-contribution
  initiative. See knowledge.md for the breakdown.
-/

end HGcd
