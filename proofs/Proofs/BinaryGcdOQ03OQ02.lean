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

  Toward size reduction (PARTS VIII–IX):
  We also prove `hgcdShift_pos` (shift ≥ 1 for large inputs) and
  `hgcdShift_top_lt` (top-half inputs strictly decrease), which
  enable the strong induction for Step 4. The joint bound
  `hgcdMatrix_joint_bound` is stated as a sorry; the missing piece
  is a "quotient stability" lemma not yet formalized here.

  Out of scope (deferred):
  The bit-complexity claim O(M(n)·log n) requires a Mathlib model of
  fast multiplication and bit operations that does not yet exist.
  Filling that gap is a multi-thousand-line foundational project.

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
-- PART VI: CRAMER IDENTITY AND SIGN PATTERN (Step 2b)
-- ═══════════════════════════════════════════════════════════════

/-- Cramer recovery formula in the row-vector convention.

    From `(a₀, b₀) · M = (ahat, bhat)` — i.e.,
      a₀·M.α + b₀·M.γ = ahat  and  a₀·M.β + b₀·M.δ = bhat —
    the determinant identity gives:

      a₀ · det M = ahat · M.δ - bhat · M.γ
      b₀ · det M = bhat · M.α - ahat · M.β

    Proof: pure algebra. `linear_combination M.δ * h₁ - M.γ * h₂` for
    the first goal, `M.α * h₂ - M.β * h₁` for the second. -/
theorem row_vec_cramer {a₀ b₀ ahat bhat : ℤ} {M : CofactorMatrix}
    (h₁ : a₀ * M.α + b₀ * M.γ = ahat)
    (h₂ : a₀ * M.β + b₀ * M.δ = bhat) :
    a₀ * M.det = ahat * M.δ - bhat * M.γ ∧
    b₀ * M.det = bhat * M.α - ahat * M.β := by
  simp only [CofactorMatrix.det]
  exact ⟨by linear_combination M.δ * h₁ - M.γ * h₂,
         by linear_combination M.α * h₂ - M.β * h₁⟩

/-- The "even-step" sign pattern: entries after an even number of
    `lehmerInnerStep` applications starting from `CofactorMatrix.id`.
    The identity has α = δ = 1 ≥ 0 and β = γ = 0 ≤ 0, so it is even. -/
def EvenPattern (M : CofactorMatrix) : Prop :=
  0 ≤ M.α ∧ M.β ≤ 0 ∧ M.γ ≤ 0 ∧ 0 ≤ M.δ

/-- The "odd-step" sign pattern: α ≤ 0, δ ≤ 0, β ≥ 0, γ ≥ 0. -/
def OddPattern (M : CofactorMatrix) : Prop :=
  M.α ≤ 0 ∧ 0 ≤ M.β ∧ 0 ≤ M.γ ∧ M.δ ≤ 0

/-- The identity matrix has EvenPattern. -/
theorem CofactorMatrix.id_even_pattern : EvenPattern CofactorMatrix.id := by
  simp [EvenPattern, CofactorMatrix.id]

/-- One successful `lehmerInnerStep` takes EvenPattern to OddPattern.

    M' = M.mul [[0,1],[1,-q]]:
      M'.α = M.β,         M'.γ = M.δ
      M'.β = M.α - q·M.β, M'.δ = M.γ - q·M.δ

    For EvenPattern (α ≥ 0, β ≤ 0, γ ≤ 0, δ ≥ 0) and q ≥ 0:
      M'.α = M.β ≤ 0  ✓
      M'.β = M.α + q·(-M.β) ≥ 0  ✓  (both terms non-negative)
      M'.γ = M.δ ≥ 0  ✓
      M'.δ = M.γ - q·M.δ ≤ 0  ✓  (M.γ ≤ 0, -q·M.δ ≤ 0) -/
theorem lehmerInnerStep_even_to_odd {ahat bhat : ℕ} {M M' : CofactorMatrix}
    {ahat' bhat' : ℕ}
    (hstep : lehmerInnerStep ahat bhat M = some (ahat', bhat', M'))
    (heven : EvenPattern M) :
    OddPattern M' := by
  simp [lehmerInnerStep] at hstep
  split at hstep <;> simp_all
  split at hstep <;> simp_all
  obtain ⟨_, _, rfl⟩ := hstep
  obtain ⟨hα, hβ, hγ, hδ⟩ := heven
  simp only [OddPattern]
  have hq : (0 : ℤ) ≤ (ahat / bhat : ℕ) := Int.ofNat_nonneg _
  refine ⟨hβ, ?_, hδ, ?_⟩
  · nlinarith
  · nlinarith

/-- One successful `lehmerInnerStep` takes OddPattern to EvenPattern. -/
theorem lehmerInnerStep_odd_to_even {ahat bhat : ℕ} {M M' : CofactorMatrix}
    {ahat' bhat' : ℕ}
    (hstep : lehmerInnerStep ahat bhat M = some (ahat', bhat', M'))
    (hodd : OddPattern M) :
    EvenPattern M' := by
  simp [lehmerInnerStep] at hstep
  split at hstep <;> simp_all
  split at hstep <;> simp_all
  obtain ⟨_, _, rfl⟩ := hstep
  obtain ⟨hα, hβ, hγ, hδ⟩ := hodd
  simp only [EvenPattern]
  have hq : (0 : ℤ) ≤ (ahat / bhat : ℕ) := Int.ofNat_nonneg _
  -- M' = [[M.β, M.α - q·M.β], [M.δ, M.γ - q·M.δ]]
  -- EvenPattern: M'.α = M.β ≥ 0, M'.β = M.α - q·M.β ≤ 0, M'.γ = M.δ ≤ 0, M'.δ = M.γ - q·M.δ ≥ 0
  refine ⟨hβ, ?_, hδ, ?_⟩
  · -- M.α - q*M.β ≤ 0: M.α ≤ 0, q*M.β ≥ 0
    nlinarith
  · -- 0 ≤ M.γ - q*M.δ: M.γ ≥ 0, -q*M.δ ≥ 0 (since M.δ ≤ 0)
    nlinarith

/-- `lehmerCofactors` preserves the EvenPattern/OddPattern disjunction
    from any starting matrix that has one.

    Induction on fuel: base returns the initial pattern unchanged.
    Each successful step flips even↔odd via the alternation lemmas. -/
theorem lehmerCofactors_has_pattern_from
    (fuel ahat bhat : ℕ) (M₀ : CofactorMatrix)
    (h₀ : EvenPattern M₀ ∨ OddPattern M₀) :
    EvenPattern (lehmerCofactors fuel ahat bhat M₀) ∨
    OddPattern (lehmerCofactors fuel ahat bhat M₀) := by
  induction fuel generalizing ahat bhat M₀ with
  | zero => simp [lehmerCofactors]; exact h₀
  | succ n ih =>
    simp only [lehmerCofactors]
    match hstep : lehmerInnerStep ahat bhat M₀ with
    | none => exact h₀
    | some (ahat', bhat', M') =>
      rcases h₀ with heven | hodd
      · exact ih ahat' bhat' M' (Or.inr (lehmerInnerStep_even_to_odd hstep heven))
      · exact ih ahat' bhat' M' (Or.inl (lehmerInnerStep_odd_to_even hstep hodd))

/-- `lehmerCofactors` starting from `CofactorMatrix.id` always has
    EvenPattern or OddPattern. -/
theorem lehmerCofactors_has_pattern (fuel ahat bhat : ℕ) :
    EvenPattern (lehmerCofactors fuel ahat bhat CofactorMatrix.id) ∨
    OddPattern (lehmerCofactors fuel ahat bhat CofactorMatrix.id) :=
  lehmerCofactors_has_pattern_from fuel ahat bhat CofactorMatrix.id
    (Or.inl CofactorMatrix.id_even_pattern)

/-- Entry bound for `lehmerCofactors` starting from `id`:
    when EvenPattern holds, the non-negative entries δ and α are
    bounded by the initial inputs, and the non-positive entries
    γ and β are bounded in absolute value.

    Precisely: under EvenPattern (so M.δ ≥ 0, M.γ ≤ 0) and the
    row-vector invariant
      `ahat * M.α + bhat * M.γ = ahat'`  (with ahat' : ℤ, ≥ 0)
      `ahat * M.β + bhat * M.δ = bhat'`  (with bhat' : ℤ, ≥ 0)
    and det M = 1:
      ahat = ahat' * M.δ + bhat' * (-M.γ) ≥ ahat' * M.δ ≥ M.δ  (if ahat' ≥ 1)
      bhat = bhat' * M.α + ahat' * (-M.β) ≥ bhat' * M.α ≥ M.α  (if bhat' ≥ 1) -/
theorem entry_bound_of_even {a₀ b₀ ahat' bhat' : ℤ} {M : CofactorMatrix}
    (h₁ : a₀ * M.α + b₀ * M.γ = ahat')
    (h₂ : a₀ * M.β + b₀ * M.δ = bhat')
    (hdet : M.det = 1)
    (heven : EvenPattern M)
    (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hahat' : 1 ≤ ahat') (hbhat' : 1 ≤ bhat') :
    M.δ ≤ a₀ ∧ -(a₀) ≤ M.γ ∧ M.α ≤ b₀ ∧ -(b₀) ≤ M.β := by
  obtain ⟨hα, hβ, hγ, hδ⟩ := heven
  obtain ⟨hcr_a, hcr_b⟩ := row_vec_cramer h₁ h₂
  rw [hdet, mul_one] at hcr_a hcr_b
  -- hcr_a : a₀ = ahat' * M.δ - bhat' * M.γ
  -- hcr_b : b₀ = bhat' * M.α - ahat' * M.β
  -- Since EvenPattern: M.γ ≤ 0 so -bhat' * M.γ ≥ 0,
  -- and M.δ ≥ 0, ahat' ≥ 1 → a₀ ≥ ahat' * M.δ ≥ M.δ
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- M.δ ≤ a₀
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ bhat') (neg_nonneg.mpr hγ),
               mul_le_mul_of_nonneg_left (by linarith : (1:ℤ) ≤ ahat') hδ]
  · -- -a₀ ≤ M.γ, i.e., M.γ ≥ -a₀
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ ahat') hδ,
               mul_nonneg (by linarith : (0:ℤ) ≤ bhat') (neg_nonneg.mpr hγ)]
  · -- M.α ≤ b₀
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ ahat') (neg_nonneg.mpr hβ),
               mul_le_mul_of_nonneg_left (by linarith : (1:ℤ) ≤ bhat') hα]
  · -- -b₀ ≤ M.β, i.e., M.β ≥ -b₀
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ bhat') hα,
               mul_nonneg (by linarith : (0:ℤ) ≤ ahat') (neg_nonneg.mpr hβ)]

/-- Entry bound for OddPattern (symmetric to EvenPattern case). -/
theorem entry_bound_of_odd {a₀ b₀ ahat' bhat' : ℤ} {M : CofactorMatrix}
    (h₁ : a₀ * M.α + b₀ * M.γ = ahat')
    (h₂ : a₀ * M.β + b₀ * M.δ = bhat')
    (hdet : M.det = -1)
    (hodd : OddPattern M)
    (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hahat' : 1 ≤ ahat') (hbhat' : 1 ≤ bhat') :
    -(a₀) ≤ M.δ ∧ M.γ ≤ a₀ ∧ -(b₀) ≤ M.α ∧ M.β ≤ b₀ := by
  obtain ⟨hα, hβ, hγ, hδ⟩ := hodd
  obtain ⟨hcr_a, hcr_b⟩ := row_vec_cramer h₁ h₂
  rw [hdet] at hcr_a hcr_b
  -- hcr_a : a₀ * (-1) = ahat' * M.δ - bhat' * M.γ
  -- → -a₀ = ahat' * M.δ - bhat' * M.γ
  -- OddPattern: M.δ ≤ 0, M.γ ≥ 0
  -- ahat' * M.δ ≤ 0 and bhat' * M.γ ≥ 0
  -- -a₀ = ahat' * M.δ - bhat' * M.γ ≤ ahat' * M.δ ≤ M.δ (if ahat' ≥ 1)
  -- → M.δ ≥ -a₀ ✓
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ bhat') hγ,
               mul_le_mul_of_nonneg_left (by linarith : (1:ℤ) ≤ ahat') (neg_nonneg.mpr hδ)]
  · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ ahat') (neg_nonneg.mpr hδ),
               mul_nonneg (by linarith : (0:ℤ) ≤ bhat') hγ]
  · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ ahat') hβ,
               mul_le_mul_of_nonneg_left (by linarith : (1:ℤ) ≤ bhat') (neg_nonneg.mpr hα)]
  · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ bhat') (neg_nonneg.mpr hα),
               mul_nonneg (by linarith : (0:ℤ) ≤ ahat') hβ]

-- ═══════════════════════════════════════════════════════════════
-- PART VII: PERTURBATION INFRASTRUCTURE (Step 3 building blocks)
-- ═══════════════════════════════════════════════════════════════

/-! ### Step 3 infrastructure

The HGCD algorithm computes `M₁ = hgcdMatrix fuel (a >> s) (b >> s)` using
the top-half truncation of `(a, b)`, then applies `M₁` to the full-precision
`(a, b)`. Step 3 bounds the discrepancy introduced by this truncation.

Write `aHi = a / 2^s`, `bHi = b / 2^s`, `ea = a % 2^s`, `eb = b % 2^s`, so
that `a = aHi * 2^s + ea` and `b = bHi * 2^s + eb` with `0 ≤ ea, eb < 2^s`.

Linearity of `apply` gives:
  `M.apply a b = M.apply (aHi*2^s) (bHi*2^s) + M.apply ea eb`
           `= 2^s · M.apply aHi bHi + M.apply ea eb`.

The first term is bounded by `2^s · max(aHi, bHi)` from residue monotonicity
(Step 2a applied to the top-half subproblem).  The second (error) term is:
  `|M.α · ea + M.β · eb| ≤ (|M.α| + |M.β|) · 2^s`
                        `≤ 2 · max(aHi, bHi) · 2^s`
using the entry bounds from Step 2b (`entry_bound_of_even/odd`).

The lemmas in this section establish the algebraic pieces.  The
inductive bitsize argument needed to close `hgcdMatrix_size_reduction`
is deferred (Step 4). -/

/-- `CofactorMatrix.apply` distributes over addition of inputs.
    This is pure ring algebra: apply(a₁ + a₂, b₁ + b₂) splits into
    apply(a₁, b₁) + apply(a₂, b₂) component-wise. -/
theorem cofactor_apply_add (M : CofactorMatrix) (a₁ a₂ b₁ b₂ : ℤ) :
    (M.apply (a₁ + a₂) (b₁ + b₂)).1 = (M.apply a₁ b₁).1 + (M.apply a₂ b₂).1 ∧
    (M.apply (a₁ + a₂) (b₁ + b₂)).2 = (M.apply a₁ b₁).2 + (M.apply a₂ b₂).2 := by
  simp only [CofactorMatrix.apply]
  exact ⟨by ring, by ring⟩

/-- `CofactorMatrix.apply` commutes with scalar multiplication.
    For any scalar `k : ℤ`, `M.apply (k · a) (k · b) = k · M.apply a b`
    component-wise. -/
theorem cofactor_apply_smul (M : CofactorMatrix) (k a b : ℤ) :
    (M.apply (k * a) (k * b)).1 = k * (M.apply a b).1 ∧
    (M.apply (k * a) (k * b)).2 = k * (M.apply a b).2 := by
  simp only [CofactorMatrix.apply]
  exact ⟨by ring, by ring⟩

/-- The full-precision apply equals `2^s` times the top-half apply, plus the
    error from the low-bits `(ea, eb)`.

    Concretely: `a = aHi * 2^s + ea` and `b = bHi * 2^s + eb`, so by
    `cofactor_apply_add` and `cofactor_apply_smul`:
      `(M.apply a b).1 = 2^s · (M.apply aHi bHi).1 + (M.apply ea eb).1`.
    This is the key decomposition for the perturbation argument. -/
theorem cofactor_apply_shift_decomp (M : CofactorMatrix) (aHi bHi ea eb : ℤ) (s : ℕ) :
    let pow2s : ℤ := 2 ^ s
    (M.apply (aHi * pow2s + ea) (bHi * pow2s + eb)).1 =
      pow2s * (M.apply aHi bHi).1 + (M.apply ea eb).1 ∧
    (M.apply (aHi * pow2s + ea) (bHi * pow2s + eb)).2 =
      pow2s * (M.apply aHi bHi).2 + (M.apply ea eb).2 := by
  simp only [CofactorMatrix.apply]
  exact ⟨by ring, by ring⟩

/-- Triangle bound: |M.α · ea + M.β · eb| ≤ |M.α| · |ea| + |M.β| · |eb|.

    This is Int.natAbs triangle inequality for the first component of
    `M.apply ea eb`. Used to bound the error term in Step 3 given
    entry bounds on M from Step 2b. -/
theorem cofactor_apply_natAbs_le (M : CofactorMatrix) (ea eb : ℤ) :
    (M.apply ea eb).1.natAbs ≤ M.α.natAbs * ea.natAbs + M.β.natAbs * eb.natAbs ∧
    (M.apply ea eb).2.natAbs ≤ M.γ.natAbs * ea.natAbs + M.δ.natAbs * eb.natAbs := by
  simp only [CofactorMatrix.apply]
  constructor
  · calc (M.α * ea + M.β * eb).natAbs
        ≤ (M.α * ea).natAbs + (M.β * eb).natAbs := Int.natAbs_add_le _ _
      _ = M.α.natAbs * ea.natAbs + M.β.natAbs * eb.natAbs := by
            simp [Int.natAbs_mul]
  · calc (M.γ * ea + M.δ * eb).natAbs
        ≤ (M.γ * ea).natAbs + (M.δ * eb).natAbs := Int.natAbs_add_le _ _
      _ = M.γ.natAbs * ea.natAbs + M.δ.natAbs * eb.natAbs := by
            simp [Int.natAbs_mul]

/-- Error bound for the first component of `M.apply ea eb` when entries are
    bounded by `C` and inputs are bounded by `B` (all in ℕ).

    From `cofactor_apply_natAbs_le` with `|M.α|, |M.β| ≤ C` and
    `|ea|, |eb| ≤ B`, the first component is at most `2 · C · B`. -/
theorem cofactor_apply_err_bound (M : CofactorMatrix) (ea eb : ℤ) (C B : ℕ)
    (hα : M.α.natAbs ≤ C) (hβ : M.β.natAbs ≤ C)
    (hea : ea.natAbs ≤ B) (heb : eb.natAbs ≤ B) :
    (M.apply ea eb).1.natAbs ≤ 2 * C * B := by
  have ⟨h, _⟩ := cofactor_apply_natAbs_le M ea eb
  calc (M.apply ea eb).1.natAbs
      ≤ M.α.natAbs * ea.natAbs + M.β.natAbs * eb.natAbs := h
    _ ≤ C * B + C * B := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul hα hea
          · exact Nat.mul_le_mul hβ heb
    _ = 2 * C * B := by ring

/-- Error bound for the second component of `M.apply ea eb`. Symmetric to
    `cofactor_apply_err_bound` using `|M.γ|` and `|M.δ|`. -/
theorem cofactor_apply_err_bound_snd (M : CofactorMatrix) (ea eb : ℤ) (C B : ℕ)
    (hγ : M.γ.natAbs ≤ C) (hδ : M.δ.natAbs ≤ C)
    (hea : ea.natAbs ≤ B) (heb : eb.natAbs ≤ B) :
    (M.apply ea eb).2.natAbs ≤ 2 * C * B := by
  have ⟨_, h⟩ := cofactor_apply_natAbs_le M ea eb
  calc (M.apply ea eb).2.natAbs
      ≤ M.γ.natAbs * ea.natAbs + M.δ.natAbs * eb.natAbs := h
    _ ≤ C * B + C * B := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul hγ hea
          · exact Nat.mul_le_mul hδ heb
    _ = 2 * C * B := by ring

-- ═══════════════════════════════════════════════════════════════
-- PART VIII: SIZE REDUCTION PREREQUISITES (Step 4 foundations)
-- ═══════════════════════════════════════════════════════════════

/-! ### Shift bounds — prerequisite for strong induction

The size-reduction proof proceeds by strong induction on `max a b`.
The key fact enabling the induction is that the top-half inputs
`(a / 2^s, b / 2^s)` are **strictly smaller** than `(a, b)`, so the
induction hypothesis applies.

These lemmas establish that `hgcdShift a b ≥ 1` (for large enough
inputs) and hence the top-half truncation truly reduces the input
magnitude. -/

/-- The half-bit shift is at least 1 when `max a b ≥ 4`.

    Proof: `hgcdShift a b = (Nat.log 2 (max a b) + 1) / 2`.
    Since `max a b ≥ 4 = 2²`, we have `Nat.log 2 (max a b) ≥ 2`,
    so `(2 + 1) / 2 = 1`. -/
theorem hgcdShift_pos (a b : ℕ) (h : 4 ≤ max a b) : 1 ≤ hgcdShift a b := by
  simp only [hgcdShift]
  have hlog2 : 2 ≤ Nat.log 2 (max a b) := by
    calc 2 = Nat.log 2 4 := by native_decide
      _ ≤ Nat.log 2 (max a b) := Nat.log_mono_right h
  omega

/-- The top-half inputs `(a / 2^s, b / 2^s)` are strictly less than
    `max a b` when `hgcdThreshold ≤ max a b`.

    This is the key induction-measure decrease: the recursive calls in
    `hgcdMatrix` pass inputs strictly smaller than the current inputs,
    enabling strong induction on `max a b`.

    Proof: since `hgcdThreshold = 64 ≥ 4`, `hgcdShift ≥ 1`, so
    `2^s ≥ 2`, and dividing by ≥ 2 strictly decreases a positive value. -/
theorem hgcdShift_top_lt (a b : ℕ) (h : hgcdThreshold ≤ max a b) :
    max (a / 2 ^ hgcdShift a b) (b / 2 ^ hgcdShift a b) < max a b := by
  have h4 : 4 ≤ max a b := by simp only [hgcdThreshold] at h; omega
  have hpos : 1 ≤ hgcdShift a b := hgcdShift_pos a b h4
  have hmax_pos : 0 < max a b := by omega
  have h1lt2s : 1 < 2 ^ hgcdShift a b :=
    Nat.one_lt_pow (by omega) (by norm_num)
  calc max (a / 2 ^ hgcdShift a b) (b / 2 ^ hgcdShift a b)
      ≤ max a b / 2 ^ hgcdShift a b := by
          apply max_le
          · exact Nat.div_le_div_right (le_max_left _ _)
          · exact Nat.div_le_div_right (le_max_right _ _)
    _ < max a b := Nat.div_lt_self hmax_pos h1lt2s

-- ═══════════════════════════════════════════════════════════════
-- PART VIII.5: ROW-CONVENTION OUTPUT BOUND (small case, proved)
-- ═══════════════════════════════════════════════════════════════

/-- For small inputs, the HGCD matrix's ROW action yields bounded residues.

    When `max a b < hgcdThreshold`, the HGCD matrix equals
    `lehmerCofactors hgcdThreshold a b id`, and the row-vector product
    `(a · M.α + b · M.γ, a · M.β + b · M.δ)` gives Euclidean residues
    bounded by `max a b`.

    **Convention note**: this theorem uses the ROW action, not
    `M.apply(a, b)` (COLUMN action). The distinction is critical:
    the row action gives GCD residues (bounded), while the column
    action can be much larger. See the counterexample at
    `hgcdMatrix_joint_bound` for details.

    This is the small-case component of the size-reduction argument,
    proved from `lehmerCofactors_id_apply_le` by one rewrite. -/
theorem hgcdMatrix_row_reduction_small (fuel a b : ℕ) (h : max a b < hgcdThreshold) :
    ∃ a' b' : ℕ,
      (a : ℤ) * (hgcdMatrix (fuel + 1) a b).α
        + (b : ℤ) * (hgcdMatrix (fuel + 1) a b).γ = ↑a' ∧
      (a : ℤ) * (hgcdMatrix (fuel + 1) a b).β
        + (b : ℤ) * (hgcdMatrix (fuel + 1) a b).δ = ↑b' ∧
      max a' b' ≤ max a b := by
  rw [hgcdMatrix_small h]
  exact lehmerCofactors_id_apply_le hgcdThreshold a b

-- ═══════════════════════════════════════════════════════════════
-- PART IX: SIZE REDUCTION CLAIM (joint bound — Step 4 proper)
-- ═══════════════════════════════════════════════════════════════

/-! ### The joint size-reduction theorem (statement needs correction)

**FINDING (2026-05-03)**: The theorem `hgcdMatrix_joint_bound` as stated
is **FALSE**. The column action `M.apply(a, b)` is NOT bounded by
`2 ^ (hgcdShift a b + 3)`. Two concrete counterexamples:

**Counterexample 1** (base case, a = 31, b = 20, any fuel ≥ 1):

  hgcdMatrix (fuel+1) 31 20 = lehmerCofactors 64 31 20 id
                             = ⟨α=2, β=-9, γ=-3, δ=14⟩

  Derivation: five Lehmer steps of (31,20) with q=1,1,1,4 (stopping at r=0):
    step 1 q=1: (20,11), M = (0, 1, 1,-1)
    step 2 q=1: (11, 9), M = (1,-1,-1, 2)
    step 3 q=1: ( 9, 2), M = (-1, 2, 2,-3)
    step 4 q=4: ( 2, 1), M = (2,-9,-3,14)
    step 5 q=2:     r=0 → STOP (r=0 returns None, final state not included)

  Column output: M.apply(31, 20) = (2·31 + (-9)·20, (-3)·31 + 14·20)
                                 = (62 - 180, -93 + 280) = (-118, 187)
  natAbs max = 187.
  Required bound: 2^(hgcdShift 31 20 + 3) = 2^(2+3) = 32.
  187 > 32 → **VIOLATED**.

  (Note the ROW action IS bounded: 31·2 + 20·(-3) = 2, 31·(-9) + 20·14 = 1,
   max(2,1) = 2 ≤ 31. So `hgcdMatrix_row_reduction_small` is correct.)

**Counterexample 2** (recursive case, a = 256, b = 141, any fuel):

  s = hgcdShift 256 141 = (Nat.log 2 256 + 1)/2 = 4.
  aHi = 256/16 = 16, bHi = 141/16 = 8.
  M₁ = lehmerCofactors 64 16 8 id: first step q=2, r=0 → STOP immediately.
  M₁ = id.

  With M₁ = id: M₁.apply(256, 141) = (256, 141), so M₂ = hgcdMatrix fuel 256 141.
  But this is the SAME recursion we started with! For any finite fuel k:
    hgcdMatrix 0 256 141 = id
    hgcdMatrix (k+1) 256 141 = (hgcdMatrix k 256 141).mul id = hgcdMatrix k 256 141
  By induction: hgcdMatrix k 256 141 = id for ALL k.

  id.apply(256, 141) = (256, 141), natAbs max = 256.
  Required bound: 2^(4+3) = 128.  256 > 128 → **VIOLATED**.

**Root cause — structural issue in `hgcdMatrix`**:

  When bHi | aHi (i.e., the top-half pair has r = 0 on the very first
  Euclidean step), `lehmerCofactors` returns `id` without making any
  progress. With M₁ = id, the recursive call gets the same (a, b) back,
  causing the recursion to loop until fuel=0. The fuel hypothesis
  `a + b ≤ fuel` does NOT prevent this — the natural termination
  condition for hgcdMatrix is structural (bit-size decrease), not
  sum-decrease.

  **Fix**: add a guard in `hgcdMatrix`: if M₁ = id, fall back to
  `lehmerCofactors hgcdThreshold a b id` on the full inputs (which
  always terminates and is correct, though not size-reducing in one step).

**What IS provable with the current definition**:

  1. `hgcdMatrix_row_reduction_small` (proved above): for small inputs,
     the ROW action `a·M.α + b·M.γ` and `a·M.β + b·M.δ` are bounded
     by `max a b`. This is the correct formulation for small inputs.

  2. Entry bounds for the SMALL case: `M.α.natAbs ≤ max a b` etc. follow
     from `entry_bound_of_even/odd` under the row invariant.

  3. For the LARGE case (recursive), the claim fails both for entries
     and outputs when M₁ = id (trivial recursion).

  **Next step**: fix `hgcdMatrix` to detect the M₁ = id case and fall
  back, then re-state `hgcdMatrix_joint_bound` using the ROW convention:
    `a · M.α + b · M.γ ≤ 2^(s+3)` and `a · M.β + b · M.δ ≤ 2^(s+3)`.

  **Classification**: OPEN (requires fixing the definition, then a new
  induction argument). This is more than a missing lemma — the definition
  has a structural defect for the degenerate bHi | aHi case. -/

/-- [Sorry — STATEMENT IS FALSE] HGCD joint size-reduction bound.

    **⚠ WARNING: This theorem as stated is false.**
    The COLUMN action `M.apply(a, b)` is NOT bounded by `2^(hgcdShift a b + 3)`.

    Counterexample: a=31, b=20, any fuel≥1.
      M = lehmerCofactors 64 31 20 id = ⟨2,-9,-3,14⟩.
      M.apply(31,20) = (-118, 187).  max natAbs = 187.
      2^(hgcdShift 31 20 + 3) = 2^5 = 32.  187 > 32.

    The error is a CONVENTION MISMATCH: the existing infrastructure bounds
    the ROW action `a·M.α + b·M.γ` (which gives Euclidean residues), not
    the COLUMN action `M.α·a + M.β·b` (which does not).

    Additionally, `hgcdMatrix` has a structural defect: when the top-half
    approximation gives M₁ = id (degenerate case bHi | aHi), the recursion
    loops until fuel=0. Counterexample: a=256, b=141 → id for all fuel.

    See the PART IX docstring for the full analysis.
    See `hgcdMatrix_row_reduction_small` (proved) for the correct small case. -/
theorem hgcdMatrix_joint_bound (fuel a b : ℕ) (hfuel : a + b ≤ fuel) :
    let M := hgcdMatrix fuel a b
    let s := hgcdShift a b
    (M.apply (a : ℤ) (b : ℤ)).1.natAbs ≤ 2 ^ (s + 3) ∧
    (M.apply (a : ℤ) (b : ℤ)).2.natAbs ≤ 2 ^ (s + 3) ∧
    M.α.natAbs ≤ 2 ^ (s + 3) ∧
    M.β.natAbs ≤ 2 ^ (s + 3) ∧
    M.γ.natAbs ≤ 2 ^ (s + 3) ∧
    M.δ.natAbs ≤ 2 ^ (s + 3) := by
  sorry

/-! ## Summary

**Proved (0 axioms, 0 sorries):**

1. **Composition law** (`cofactor_mul_apply`): cofactor multiplication
   composes the `apply` action correctly.

2. **Determinant invariant** (`hgcdMatrix_det_unit`): every matrix
   returned by `hgcdMatrix` has det ±1.

3. **GCD preservation** (`hgcdMatrix_preserves_gcd`): applying the
   HGCD matrix to (a, b) yields a pair with the same GCD.

4. **Matrix-vector invariant for Lehmer cofactors**
   (`lehmerInnerStep_invariant`, `lehmerCofactors_invariant`,
   `lehmerCofactors_id_apply_eq`): the row-vector relation
   `(a₀, b₀) · M = (current pair)` is preserved by `lehmerInnerStep`
   and hence by `lehmerCofactors`. Step 1 of the size-reduction proof.

5. **Residue monotonicity** (`lehmerInnerStep_residue_le`,
   `lehmerInnerStep_max_le`, `lehmerCofactors_invariant_le`,
   `lehmerCofactors_id_apply_le`): each step has `bhat' < bhat` and
   `max ahat' bhat' ≤ max ahat bhat`. Step 2a.

6. **Cramer identity** (`row_vec_cramer`): from `(a₀, b₀)·M = (ahat, bhat)`
   and the determinant, derives `a₀·det = ahat·M.δ - bhat·M.γ` and
   `b₀·det = bhat·M.α - ahat·M.β`. Proved by `linear_combination`.

7. **Sign pattern** (`EvenPattern`, `OddPattern`,
   `lehmerInnerStep_even_to_odd`, `lehmerInnerStep_odd_to_even`,
   `lehmerCofactors_has_pattern_from`, `lehmerCofactors_has_pattern`):
   each `lehmerInnerStep` flips the sign pattern of the matrix entries
   (EvenPattern ↔ OddPattern). `lehmerCofactors` starting from id
   always has EvenPattern or OddPattern. Step 2b foundation.

8. **Entry bounds** (`entry_bound_of_even`, `entry_bound_of_odd`):
   under the row-vector invariant with positive residues (ahat', bhat' ≥ 1)
   and EvenPattern (resp. OddPattern), all matrix entries are bounded
   in absolute value by the initial inputs a₀ and b₀. Proved using
   Cramer + sign pattern. This is Step 2b.

9. **Perturbation infrastructure** (PART VII, Step 3 building blocks):
   - `cofactor_apply_add`: `apply` distributes over addition of inputs.
   - `cofactor_apply_smul`: `apply` commutes with scalar multiplication.
   - `cofactor_apply_shift_decomp`: full-precision `apply(aHi·2^s + ea, bHi·2^s + eb)`
     decomposes as `2^s · apply(aHi, bHi) + apply(ea, eb)`.
   - `cofactor_apply_natAbs_le`: triangle bound for `natAbs` of both components.
   - `cofactor_apply_err_bound` / `cofactor_apply_err_bound_snd`: given
     entry bounds `|M.α|, |M.β| ≤ C` and input bounds `|ea|, |eb| ≤ B`,
     the error component is at most `2·C·B`. This is the quantitative error
     bound combining Step 2b entry bounds with the low-bit size.

10. **Shift-position bound** (`hgcdShift_pos`): `hgcdShift a b ≥ 1` when
    `max a b ≥ 4`. Proof: `Nat.log 2 (max a b) ≥ 2` for input ≥ 4, so
    `(2+1)/2 = 1`. Uses `Nat.log_mono_right`.

11. **Top-half strictly smaller** (`hgcdShift_top_lt`): for threshold inputs,
    `max (a / 2^s) (b / 2^s) < max a b`. This is the **induction-measure
    decrease** needed for the Step 4 strong induction. Proof: `2^s ≥ 2`
    from hgcdShift_pos, then `Nat.div_lt_self`.

12. **Row-action bound for small inputs** (`hgcdMatrix_row_reduction_small`,
    PART VIII.5): for `max a b < hgcdThreshold`, the HGCD matrix's ROW
    action `(a·M.α + b·M.γ, a·M.β + b·M.δ)` gives residues bounded by
    `max a b`. One-line proof: `rw [hgcdMatrix_small h]; exact
    lehmerCofactors_id_apply_le hgcdThreshold a b`. This is the CORRECT
    small-case formulation (ROW convention, not COLUMN).

**Remaining for size reduction (1 sorry — statement needs correction):**
- `hgcdMatrix_joint_bound` (PART IX): **STATEMENT IS FALSE** as written.
  The COLUMN action `M.apply(a, b)` is NOT bounded by `2^(s+3)`.
  Counterexample: a=31, b=20 → M.apply = (-118,187), bound = 32. VIOLATED.

  **Two issues identified**:
  1. CONVENTION MISMATCH: existing lemmas bound the ROW action; the sorry
     claims the COLUMN action. For general matrices these differ.
  2. STRUCTURAL DEFECT in `hgcdMatrix`: when the top-half pair has r=0
     immediately (bHi | aHi), M₁ = id and the recursion loops until
     fuel=0. Example: a=256, b=141 → hgcdMatrix k 256 141 = id for all k.

  **Required fix**: correct `hgcdMatrix` to fall back to
  `lehmerCofactors hgcdThreshold a b id` when M₁ = id, then re-state the
  theorem in the ROW convention. See PART IX docstring for full analysis.

**Out of scope (deferred):**
- Bit-complexity bound O(M(n)·log n): requires Mathlib infrastructure
  (fast multiplication, bit-complexity model) that does not yet exist.
-/

end HGcd
