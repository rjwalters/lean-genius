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

  Toward size reduction (PART XI, Session 14):
  We add the abstract composition law `cofactor_mul_row_invariant`
  for the row-vector relation through `M.mul N`, plus the existential
  row-vector invariants `hgcdMatrix_zero_row_invariant` and
  `hgcdMatrix_small_row_invariant` that supply natural-number
  witnesses + monotonicity for the base/threshold cases of HGCD.
  These are the inputs needed by `row_vec_cramer` to derive entry
  bounds at the leaf of the recursion.

  Toward size reduction (PART XII, Session 15):
  We prove `hgcdMatrix_pattern_det_coupled`, the conjoint invariant
  `(EvenPattern ∧ det = 1) ∨ (OddPattern ∧ det = -1)` for every matrix
  produced by HGCD. This couples the PART III determinant bound with
  the PART X sign-pattern lifting; with this coupling, `entry_bound_of_even`
  (which requires `det = 1`) and `entry_bound_of_odd` (which requires
  `det = -1`) can be applied without a four-way case split. Proof:
  the coupling holds for `lehmerInnerStep` (each step flips both
  pattern and det sign), hence inductively for `lehmerCofactors`;
  it is preserved by matrix multiplication via the Z/2-grading of
  patterns matching the multiplicativity of det.

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
  -- Modern simp reduces the some-equation directly to a 5-conjunct
  -- (bhat ≠ 0, ahat%bhat ≠ 0, bhat = ahat', ahat%bhat = bhat', struct = M');
  -- destructure with `rfl` on the last three to substitute ahat', bhat', M'.
  obtain ⟨_, _, rfl, rfl, rfl⟩ := h_step
  refine ⟨?_, ?_⟩
  · -- a₀ * M'.α + b₀ * M'.γ = a₀ * M.β + b₀ * M.δ = bhat
    exact h_inv₂
  · -- a₀ * (M.α - q·M.β) + b₀ * (M.γ - q·M.δ) = ahat % bhat
    -- Modern simp normalizes ↑(ahat/bhat) to ↑ahat / ↑bhat (Int.ediv on coercions),
    -- so `expand` is stated in that normalized form to match the post-simp goal.
    have expand :
        a₀ * (M.α - ((ahat : ℤ) / (bhat : ℤ)) * M.β)
          + b₀ * (M.γ - ((ahat : ℤ) / (bhat : ℤ)) * M.δ)
        = (a₀ * M.α + b₀ * M.γ)
            - ((ahat : ℤ) / (bhat : ℤ)) * (a₀ * M.β + b₀ * M.δ) := by ring
    rw [expand, h_inv₁, h_inv₂]
    -- Goal: (ahat : ℤ) - ↑ahat / ↑bhat * (bhat : ℤ) = ↑(ahat % bhat)
    -- Bridge between the Nat-division (Nat.div_add_mod) and the post-simp Int form.
    have hdiv_eq : ((ahat / bhat : ℕ) : ℤ) = ((ahat : ℤ) / (bhat : ℤ)) := by
      push_cast
      rfl
    have hdivmod_int :
        (bhat : ℤ) * ((ahat : ℤ) / (bhat : ℤ)) + ((ahat % bhat) : ℤ) = (ahat : ℤ) := by
      rw [← hdiv_eq]
      exact_mod_cast Nat.div_add_mod ahat bhat
    linear_combination -hdivmod_int

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
  -- Modern simp produces a 5-conjunct: (bhat ≠ 0, ahat%bhat ≠ 0, bhat = ahat',
  -- ahat%bhat = bhat', struct = M'). Discard the struct-equality with `_`.
  obtain ⟨hb, _, rfl, rfl, _⟩ := h
  refine ⟨?_, rfl⟩
  -- Goal: ahat % bhat < bhat. From hb : bhat ≠ 0.
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

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
  obtain ⟨_, _, _, _, rfl⟩ := hstep
  obtain ⟨hα, hβ, hγ, hδ⟩ := heven
  simp only [OddPattern]
  have hq : (0 : ℤ) ≤ ((ahat : ℤ) / bhat) :=
    Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  refine ⟨hβ, ?_, hδ, ?_⟩
  · -- 0 ≤ M.α - q*M.β: M.α ≥ 0, q*M.β ≤ 0 (q ≥ 0, M.β ≤ 0)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hq hβ]
  · -- M.γ - q*M.δ ≤ 0: M.γ ≤ 0, q*M.δ ≥ 0
    nlinarith [mul_nonneg hq hδ]

/-- One successful `lehmerInnerStep` takes OddPattern to EvenPattern. -/
theorem lehmerInnerStep_odd_to_even {ahat bhat : ℕ} {M M' : CofactorMatrix}
    {ahat' bhat' : ℕ}
    (hstep : lehmerInnerStep ahat bhat M = some (ahat', bhat', M'))
    (hodd : OddPattern M) :
    EvenPattern M' := by
  simp [lehmerInnerStep] at hstep
  obtain ⟨_, _, _, _, rfl⟩ := hstep
  obtain ⟨hα, hβ, hγ, hδ⟩ := hodd
  simp only [EvenPattern]
  have hq : (0 : ℤ) ≤ ((ahat : ℤ) / bhat) :=
    Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  -- M' = [[M.β, M.α - q·M.β], [M.δ, M.γ - q·M.δ]]
  -- EvenPattern: M'.α = M.β ≥ 0, M'.β = M.α - q·M.β ≤ 0, M'.γ = M.δ ≤ 0, M'.δ = M.γ - q·M.δ ≥ 0
  refine ⟨hβ, ?_, hδ, ?_⟩
  · -- M.α - q*M.β ≤ 0: M.α ≤ 0, q*M.β ≥ 0
    nlinarith [mul_nonneg hq hβ]
  · -- 0 ≤ M.γ - q*M.δ: M.γ ≥ 0, q*M.δ ≤ 0 (since q ≥ 0, M.δ ≤ 0)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hq hδ]

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
-- PART VIIb: ROW-CONVENTION DECOMPOSITION LEMMAS
-- ═══════════════════════════════════════════════════════════════

/-! ### Row-product decomposition

When `a = aHi * 2^s + aLo` and `b = bHi * 2^s + bLo`, the row products
`a * M.α + b * M.γ` and `a * M.β + b * M.δ` decompose as:

  `2^s * (aHi * M.α + bHi * M.γ) + (aLo * M.α + bLo * M.γ)`
  `2^s * (aHi * M.β + bHi * M.δ) + (aLo * M.β + bLo * M.δ)`

This is the **row-convention** analogue of `cofactor_apply_shift_decomp`.
It is used in Step 4 to relate the full-precision row output to the
reduced inputs `(aHi, bHi) = (a / 2^s, b / 2^s)`. -/

/-- Row products distribute over the `2^s` decomposition of inputs. -/
theorem row_product_decompose (M : CofactorMatrix)
    (a aHi aLo b bHi bLo : ℤ) (s : ℕ)
    (ha : a = aHi * 2 ^ s + aLo) (hb : b = bHi * 2 ^ s + bLo) :
    a * M.α + b * M.γ =
      (2 : ℤ) ^ s * (aHi * M.α + bHi * M.γ) + (aLo * M.α + bLo * M.γ) ∧
    a * M.β + b * M.δ =
      (2 : ℤ) ^ s * (aHi * M.β + bHi * M.δ) + (aLo * M.β + bLo * M.δ) := by
  subst ha; subst hb; constructor <;> ring

/-- If `aHi * M.α + bHi * M.γ = aHi'` and `aHi * M.β + bHi * M.δ = bHi'`, the
    row products of `(a, b) = (aHi * 2^s + aLo, bHi * 2^s + bLo)` simplify
    to `2^s * aHi' + (aLo * M.α + bLo * M.γ)` and `2^s * bHi' + (aLo * M.β + bLo * M.δ)`. -/
theorem row_product_with_invariant (M : CofactorMatrix)
    (a aHi aLo b bHi bLo : ℤ) (s : ℕ) (aHi' bHi' : ℤ)
    (ha : a = aHi * 2 ^ s + aLo) (hb : b = bHi * 2 ^ s + bLo)
    (hinv₁ : aHi * M.α + bHi * M.γ = aHi')
    (hinv₂ : aHi * M.β + bHi * M.δ = bHi') :
    a * M.α + b * M.γ = (2 : ℤ) ^ s * aHi' + (aLo * M.α + bLo * M.γ) ∧
    a * M.β + b * M.δ = (2 : ℤ) ^ s * bHi' + (aLo * M.β + bLo * M.δ) := by
  subst ha; subst hb
  exact ⟨by linear_combination (2 : ℤ) ^ s * hinv₁,
         by linear_combination (2 : ℤ) ^ s * hinv₂⟩

-- ═══════════════════════════════════════════════════════════════
-- PART VIIc: ROW-OUTPUT COMPOSITION FOR `mul` (Session 12)
-- ═══════════════════════════════════════════════════════════════

/-! ### Row-output composition under matrix multiplication

The PART IX docstring on `hgcdMatrix_row_output_le` identifies the
structural obstacle blocking the recursive case: the IH for the inner
matrix is at `(aHi, bHi)`, but we need the row output of the inner
matrix on a *different* pair (the row output of the outer matrix on
`(a, b)`). This subsection records the algebraic identity that lets
us substitute one row-output computation for another, plus a clean
`natAbs` triangle bound that combines an *input*-side bound on the
outer matrix's row output with an *entry*-side bound on the inner
matrix.

Key identity (`cofactor_mul_row_output`):

  `a · (M.mul N).α + b · (M.mul N).γ`
    `= N.α · (a · M.α + b · M.γ) + N.γ · (a · M.β + b · M.δ)`
  `a · (M.mul N).β + b · (M.mul N).δ`
    `= N.β · (a · M.α + b · M.γ) + N.δ · (a · M.β + b · M.δ)`

i.e. the row output of `M.mul N` on `(a, b)` equals the row output of
`N` evaluated at the row output of `M` on `(a, b)`.  This is the
"row-convention" analogue of `cofactor_mul_apply` (column convention).

Combined with entry bounds for `N` (Step 2b: `entry_bound_of_even/odd`)
and a row-output bound for `M` (the IH being applied at the outer
matrix's *own* inputs), this yields a row-output bound for `M.mul N`
without ever needing a row-output bound for `N` at the outer
matrix's row output. -/

/-- Triangle bound for row products of a single cofactor matrix.

    `(a · M.α + b · M.γ).natAbs ≤ |a| · |M.α| + |b| · |M.γ|`
    `(a · M.β + b · M.δ).natAbs ≤ |a| · |M.β| + |b| · |M.δ|`

    This is the row-convention analogue of `cofactor_apply_natAbs_le`
    (which applies to the column convention `M.α · a + M.β · b`,
    `M.γ · a + M.δ · b`). The two row products use a different pair
    of entries, so a separate lemma is needed. -/
theorem cofactor_row_natAbs_le (M : CofactorMatrix) (a b : ℤ) :
    (a * M.α + b * M.γ).natAbs ≤ a.natAbs * M.α.natAbs + b.natAbs * M.γ.natAbs ∧
    (a * M.β + b * M.δ).natAbs ≤ a.natAbs * M.β.natAbs + b.natAbs * M.δ.natAbs := by
  refine ⟨?_, ?_⟩
  · calc (a * M.α + b * M.γ).natAbs
        ≤ (a * M.α).natAbs + (b * M.γ).natAbs := Int.natAbs_add_le _ _
      _ = a.natAbs * M.α.natAbs + b.natAbs * M.γ.natAbs := by
            simp [Int.natAbs_mul]
  · calc (a * M.β + b * M.δ).natAbs
        ≤ (a * M.β).natAbs + (b * M.δ).natAbs := Int.natAbs_add_le _ _
      _ = a.natAbs * M.β.natAbs + b.natAbs * M.δ.natAbs := by
            simp [Int.natAbs_mul]

/-- Row-output bound from entry bounds and input bounds.

    If every entry of `M` is bounded in absolute value by `E`, and the
    inputs `a, b` are bounded in absolute value by `R`, then both row
    products of `M` on `(a, b)` are bounded by `2 · E · R`. -/
theorem cofactor_row_natAbs_le_of_entry_bounds (M : CofactorMatrix) (a b : ℤ)
    (E R : ℕ)
    (hα : M.α.natAbs ≤ E) (hβ : M.β.natAbs ≤ E)
    (hγ : M.γ.natAbs ≤ E) (hδ : M.δ.natAbs ≤ E)
    (ha : a.natAbs ≤ R) (hb : b.natAbs ≤ R) :
    (a * M.α + b * M.γ).natAbs ≤ 2 * E * R ∧
    (a * M.β + b * M.δ).natAbs ≤ 2 * E * R := by
  obtain ⟨h1, h2⟩ := cofactor_row_natAbs_le M a b
  refine ⟨?_, ?_⟩
  · calc (a * M.α + b * M.γ).natAbs
        ≤ a.natAbs * M.α.natAbs + b.natAbs * M.γ.natAbs := h1
      _ ≤ R * E + R * E :=
            Nat.add_le_add (Nat.mul_le_mul ha hα) (Nat.mul_le_mul hb hγ)
      _ = 2 * E * R := by ring
  · calc (a * M.β + b * M.δ).natAbs
        ≤ a.natAbs * M.β.natAbs + b.natAbs * M.δ.natAbs := h2
      _ ≤ R * E + R * E :=
            Nat.add_le_add (Nat.mul_le_mul ha hβ) (Nat.mul_le_mul hb hδ)
      _ = 2 * E * R := by ring

/-- Row-output composition under `CofactorMatrix.mul`.

    The row output of `M.mul N` on `(a, b)` equals the row output of
    `N` evaluated at the row output of `M` on `(a, b)`. Pure algebra
    (`ring`); this is the row-convention dual of `cofactor_mul_apply`. -/
theorem cofactor_mul_row_output (M N : CofactorMatrix) (a b : ℤ) :
    a * (M.mul N).α + b * (M.mul N).γ =
      N.α * (a * M.α + b * M.γ) + N.γ * (a * M.β + b * M.δ) ∧
    a * (M.mul N).β + b * (M.mul N).δ =
      N.β * (a * M.α + b * M.γ) + N.δ * (a * M.β + b * M.δ) := by
  simp only [CofactorMatrix.mul]
  refine ⟨?_, ?_⟩ <;> ring

/-- Row-output bound for `M.mul N` from a row-output bound on `M` and
    entry bounds on `N`.

    If both row products of `M` on `(a, b)` have `natAbs ≤ R`, and every
    entry of `N` has `natAbs ≤ E`, then both row products of `M.mul N`
    on `(a, b)` have `natAbs ≤ 2 · E · R`.

    Combining `cofactor_mul_row_output` (rewrite to row-of-N applied to
    row-of-M) with the row-natAbs triangle bound, factoring out `N`'s
    entry bounds. This is the central infrastructure lemma for the
    joint-induction approach to `hgcdMatrix_row_output_le`: the IH for
    the inner matrix supplies the entry bounds on `N`, the IH for the
    outer matrix supplies the row-output bound on `M`. -/
theorem cofactor_mul_row_output_natAbs_le {M N : CofactorMatrix} {a b : ℤ}
    {R E : ℕ}
    (hM₁ : (a * M.α + b * M.γ).natAbs ≤ R)
    (hM₂ : (a * M.β + b * M.δ).natAbs ≤ R)
    (hNα : N.α.natAbs ≤ E) (hNβ : N.β.natAbs ≤ E)
    (hNγ : N.γ.natAbs ≤ E) (hNδ : N.δ.natAbs ≤ E) :
    (a * (M.mul N).α + b * (M.mul N).γ).natAbs ≤ 2 * E * R ∧
    (a * (M.mul N).β + b * (M.mul N).δ).natAbs ≤ 2 * E * R := by
  obtain ⟨hα_eq, hβ_eq⟩ := cofactor_mul_row_output M N a b
  refine ⟨?_, ?_⟩
  · rw [hα_eq]
    calc (N.α * (a * M.α + b * M.γ) + N.γ * (a * M.β + b * M.δ)).natAbs
        ≤ (N.α * (a * M.α + b * M.γ)).natAbs
            + (N.γ * (a * M.β + b * M.δ)).natAbs := Int.natAbs_add_le _ _
      _ = N.α.natAbs * (a * M.α + b * M.γ).natAbs
            + N.γ.natAbs * (a * M.β + b * M.δ).natAbs := by
              simp [Int.natAbs_mul]
      _ ≤ E * R + E * R :=
            Nat.add_le_add (Nat.mul_le_mul hNα hM₁) (Nat.mul_le_mul hNγ hM₂)
      _ = 2 * E * R := by ring
  · rw [hβ_eq]
    calc (N.β * (a * M.α + b * M.γ) + N.δ * (a * M.β + b * M.δ)).natAbs
        ≤ (N.β * (a * M.α + b * M.γ)).natAbs
            + (N.δ * (a * M.β + b * M.δ)).natAbs := Int.natAbs_add_le _ _
      _ = N.β.natAbs * (a * M.α + b * M.γ).natAbs
            + N.δ.natAbs * (a * M.β + b * M.δ).natAbs := by
              simp [Int.natAbs_mul]
      _ ≤ E * R + E * R :=
            Nat.add_le_add (Nat.mul_le_mul hNβ hM₁) (Nat.mul_le_mul hNδ hM₂)
      _ = 2 * E * R := by ring

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
-- PART IX: ROW OUTPUT BOUND (corrected Step 4)
-- ═══════════════════════════════════════════════════════════════

/-! ### Convention clarification and counterexample

`hgcdMatrix` uses **right-multiplication accumulation**: each Lehmer step
appends `M' = M.mul S` where `S = ⟨0,1,1,-q⟩`. The resulting matrix satisfies
the **row-convention identity** (`lehmerCofactors_id_apply_eq`):

  `a₀ · M.α + b₀ · M.γ = current_ahat`
  `a₀ · M.β + b₀ · M.δ = current_bhat`

The **column-convention** output `M.apply(a₀, b₀) = (M.α·a₀ + M.β·b₀, M.γ·a₀ + M.δ·b₀)`
is NOT the residue sequence. It can be much larger than `max a b`.

**Counterexample** (a = 37, b = 5):
- `max 37 5 = 37 < 64 = hgcdThreshold`, so `hgcdMatrix 1 37 5 = lehmerCofactors 64 37 5 id`
- Lehmer runs two steps (quotients 7 and 2), stopping when remainder = 0 at step 3
- Final matrix: `⟨1, -2, -7, 15⟩`
- Column output: `(1·37 + (-2)·5, (-7)·37 + 15·5) = (27, -184)`
- `hgcdShift 37 5 = (Nat.log 2 37 + 1) / 2 = 3`; `2^(3+3) = 64`
- `184 > 64`: the previous `hgcdMatrix_joint_bound` statement is **false**.

The correct bound is on the **row output**, which gives Euclidean residues bounded
by `max a b`. `lehmerCofactors_id_apply_le` already establishes this for the base case. -/

/-- Counterexample: column-convention output of `hgcdMatrix 1 37 5` has natAbs = 184. -/
example : ((hgcdMatrix 1 37 5).apply (37 : ℤ) 5).2.natAbs = 184 := by native_decide

/-- For (37, 5), the HGCD shift is 3, so 2^(s+3) = 64 < 184. -/
example : 2 ^ (hgcdShift 37 5 + 3) = 64 := by native_decide

/-- For inputs below threshold, the ROW output of `hgcdMatrix` is bounded by `max a b`.

    After `hgcdMatrix_small` reduces to `lehmerCofactors hgcdThreshold a b id`,
    `lehmerCofactors_id_apply_le` directly supplies natural-number witnesses
    for the row output components with `max ahat' bhat' ≤ max a b`. -/
theorem hgcdMatrix_small_row_output_le (fuel a b : ℕ) (h : max a b < hgcdThreshold) :
    ((a : ℤ) * (hgcdMatrix (fuel + 1) a b).α
        + (b : ℤ) * (hgcdMatrix (fuel + 1) a b).γ).natAbs ≤ max a b ∧
    ((a : ℤ) * (hgcdMatrix (fuel + 1) a b).β
        + (b : ℤ) * (hgcdMatrix (fuel + 1) a b).δ).natAbs ≤ max a b := by
  rw [hgcdMatrix_small fuel a b h]
  obtain ⟨ahat', bhat', h1, h2, hmax⟩ := lehmerCofactors_id_apply_le hgcdThreshold a b
  constructor
  · rw [h1]; simp only [Int.natAbs_natCast]; exact le_trans (le_max_left ahat' bhat') hmax
  · rw [h2]; simp only [Int.natAbs_natCast]; exact le_trans (le_max_right ahat' bhat') hmax

/-- [Sorry] The ROW output of `hgcdMatrix fuel a b` is bounded by `max a b`.

    The row output `(a·M.α + b·M.γ, a·M.β + b·M.δ)` equals the Euclidean residues
    produced by the Lehmer–Schönhage steps applied to `(a, b)`.

    **Base case** (`fuel = 0`): `M = id`, row output = `(a, b)` ≤ `max a b`. ✓
    **Threshold case** (`max a b < hgcdThreshold`): `hgcdMatrix_small_row_output_le`. ✓
    **Recursive case** (Session 11 analysis):
      `hgcdMatrix (f+1) a b = (hgcdMatrix f aHi bHi).mul M₂` where
      `aHi = a / 2^s`, `bHi = b / 2^s`, `s = hgcdShift a b`, and
      `M₂ = hgcdMatrix f (rowOut(hgcdMatrix f aHi bHi))`.

      By `cofactor_mul_apply` + `row_product_decompose`, the row output decomposes as:
        `a·(M₁.mul M₂).α + b·(M₁.mul M₂).γ`
        `= rowOut(M₂, rowOut(M₁, aHi, bHi))` + low-order term from `(aLo, bLo)`.

      The IH gives `|rowOut(M₁, aHi, bHi)| ≤ max(aHi, bHi) < max(a,b)`.
      But M₂ was built for inputs *from M₁'s column output*, not the row output:
      `M₂ = hgcdMatrix f (M₁.apply aHi bHi).1 (M₁.apply aHi bHi).2`.

      Sign-pattern analysis (EvenPattern/OddPattern) bounds each *individual* entry
      of M₁ and M₂ by `max(aHi, bHi) < max(a,b)`, but when applied to the row
      output of M₁ (which can be up to `max(a,b)`), the second-stage row products
      `rowOut(M₂, rowOut(M₁))` can reach `2 · max(a,b)`.

      The fundamental obstacle: the IH for M₂ is at its *own* inputs (column output of
      M₁ applied to `aHi,bHi`), not at `rowOut(M₁, aHi, bHi)`.

    **Required**: Joint induction on `max(a,b)` tracking simultaneously:
      (1) row output ≤ max(a,b), and
      (2) column output ≤ max(a,b) · C for some entry-bound constant C.
    This follows Stehlé–Zimmermann (2004) §4 and requires stronger intermediate lemmas
    connecting the two conventions via the Lehmer invariant.

    **Classification**: HARD (structural invariant linking row and column conventions
    across recursive calls). Not amenable to Aristotle. -/
theorem hgcdMatrix_row_output_le (fuel a b : ℕ) :
    ((a : ℤ) * (hgcdMatrix fuel a b).α
        + (b : ℤ) * (hgcdMatrix fuel a b).γ).natAbs ≤ max a b ∧
    ((a : ℤ) * (hgcdMatrix fuel a b).β
        + (b : ℤ) * (hgcdMatrix fuel a b).δ).natAbs ≤ max a b := by
  induction fuel generalizing a b with
  | zero =>
    rw [hgcdMatrix_zero]
    refine ⟨?_, ?_⟩ <;>
      simp [CofactorMatrix.id, Int.natAbs_natCast, le_max_left, le_max_right]
  | succ f ih =>
    by_cases hsmall : max a b < hgcdThreshold
    · exact hgcdMatrix_small_row_output_le f a b hsmall
    · sorry

-- ═══════════════════════════════════════════════════════════════
-- PART X: SIGN-PATTERN INVARIANT FOR `hgcdMatrix` (Session 13)
-- ═══════════════════════════════════════════════════════════════

/-! ### Lifting EvenPattern/OddPattern from `lehmerCofactors` to `hgcdMatrix`

The PART VI sign-pattern lemmas (`lehmerCofactors_has_pattern`,
`entry_bound_of_even`, `entry_bound_of_odd`) prove that any matrix produced
by `lehmerCofactors` from `CofactorMatrix.id` has either `EvenPattern` or
`OddPattern`, and that this sign discipline yields entry bounds via Cramer.

To extend the entry-bound argument from `lehmerCofactors` to the recursive
`hgcdMatrix`, we first need to lift the sign-pattern invariant itself: every
matrix produced by `hgcdMatrix` should have `EvenPattern` or `OddPattern`.

The recursive case `hgcdMatrix (f+1) a b = M_outer.mul M_inner` requires us
to know how `mul` interacts with patterns. Pattern multiplication is a
`Z/2`-grading: Even * Even = Even, Even * Odd = Odd, Odd * Even = Odd,
Odd * Odd = Even. (The product is Even iff both factors agree on parity,
matching the additive sign-flip of `lehmerInnerStep`.)

This subsection proves the four pattern-multiplication cases and the
combined existential `cofactor_mul_pattern`, then concludes with
`hgcdMatrix_has_pattern` by induction on fuel. -/

/-- Even pattern is preserved by multiplying two Even-pattern matrices.

    For `M, N` with `EvenPattern` (`α ≥ 0, β ≤ 0, γ ≤ 0, δ ≥ 0`):
    - `(M.mul N).α = M.α·N.α + M.β·N.γ = (≥0)(≥0) + (≤0)(≤0) ≥ 0`
    - `(M.mul N).β = M.α·N.β + M.β·N.δ = (≥0)(≤0) + (≤0)(≥0) ≤ 0`
    - `(M.mul N).γ = M.γ·N.α + M.δ·N.γ = (≤0)(≥0) + (≥0)(≤0) ≤ 0`
    - `(M.mul N).δ = M.γ·N.β + M.δ·N.δ = (≤0)(≤0) + (≥0)(≥0) ≥ 0`
    Each follows from `nlinarith` with `mul_nonneg` / `mul_nonpos_iff` facts. -/
theorem cofactor_mul_even_even {M N : CofactorMatrix}
    (hM : EvenPattern M) (hN : EvenPattern N) :
    EvenPattern (M.mul N) := by
  obtain ⟨hMα, hMβ, hMγ, hMδ⟩ := hM
  obtain ⟨hNα, hNβ, hNγ, hNδ⟩ := hN
  simp only [EvenPattern, CofactorMatrix.mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 0 ≤ M.α·N.α + M.β·N.γ
    nlinarith [mul_nonneg hMα hNα, mul_nonneg (neg_nonneg.mpr hMβ) (neg_nonneg.mpr hNγ)]
  · -- M.α·N.β + M.β·N.δ ≤ 0
    nlinarith [mul_nonneg hMα (neg_nonneg.mpr hNβ), mul_nonneg (neg_nonneg.mpr hMβ) hNδ]
  · -- M.γ·N.α + M.δ·N.γ ≤ 0
    nlinarith [mul_nonneg (neg_nonneg.mpr hMγ) hNα, mul_nonneg hMδ (neg_nonneg.mpr hNγ)]
  · -- 0 ≤ M.γ·N.β + M.δ·N.δ
    nlinarith [mul_nonneg (neg_nonneg.mpr hMγ) (neg_nonneg.mpr hNβ), mul_nonneg hMδ hNδ]

/-- Odd pattern * Odd pattern = Even pattern.

    For `M, N` with `OddPattern` (`α ≤ 0, β ≥ 0, γ ≥ 0, δ ≤ 0`):
    - `(M.mul N).α = M.α·N.α + M.β·N.γ = (≤0)(≤0) + (≥0)(≥0) ≥ 0`
    - `(M.mul N).β = M.α·N.β + M.β·N.δ = (≤0)(≥0) + (≥0)(≤0) ≤ 0`
    - `(M.mul N).γ = M.γ·N.α + M.δ·N.γ = (≥0)(≤0) + (≤0)(≥0) ≤ 0`
    - `(M.mul N).δ = M.γ·N.β + M.δ·N.δ = (≥0)(≥0) + (≤0)(≤0) ≥ 0` -/
theorem cofactor_mul_odd_odd {M N : CofactorMatrix}
    (hM : OddPattern M) (hN : OddPattern N) :
    EvenPattern (M.mul N) := by
  obtain ⟨hMα, hMβ, hMγ, hMδ⟩ := hM
  obtain ⟨hNα, hNβ, hNγ, hNδ⟩ := hN
  simp only [EvenPattern, CofactorMatrix.mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (neg_nonneg.mpr hMα) (neg_nonneg.mpr hNα), mul_nonneg hMβ hNγ]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hMα) hNβ, mul_nonneg hMβ (neg_nonneg.mpr hNδ)]
  · nlinarith [mul_nonneg hMγ (neg_nonneg.mpr hNα), mul_nonneg (neg_nonneg.mpr hMδ) hNγ]
  · nlinarith [mul_nonneg hMγ hNβ, mul_nonneg (neg_nonneg.mpr hMδ) (neg_nonneg.mpr hNδ)]

/-- Even pattern * Odd pattern = Odd pattern.

    For `M` Even, `N` Odd:
    - `(M.mul N).α = (≥0)(≤0) + (≤0)(≥0) ≤ 0`
    - `(M.mul N).β = (≥0)(≥0) + (≤0)(≤0) ≥ 0`
    - `(M.mul N).γ = (≤0)(≤0) + (≥0)(≥0) ≥ 0`
    - `(M.mul N).δ = (≤0)(≥0) + (≥0)(≤0) ≤ 0` -/
theorem cofactor_mul_even_odd {M N : CofactorMatrix}
    (hM : EvenPattern M) (hN : OddPattern N) :
    OddPattern (M.mul N) := by
  obtain ⟨hMα, hMβ, hMγ, hMδ⟩ := hM
  obtain ⟨hNα, hNβ, hNγ, hNδ⟩ := hN
  simp only [OddPattern, CofactorMatrix.mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hMα (neg_nonneg.mpr hNα), mul_nonneg (neg_nonneg.mpr hMβ) hNγ]
  · nlinarith [mul_nonneg hMα hNβ, mul_nonneg (neg_nonneg.mpr hMβ) (neg_nonneg.mpr hNδ)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hMγ) (neg_nonneg.mpr hNα), mul_nonneg hMδ hNγ]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hMγ) hNβ, mul_nonneg hMδ (neg_nonneg.mpr hNδ)]

/-- Odd pattern * Even pattern = Odd pattern.

    For `M` Odd, `N` Even:
    - `(M.mul N).α = (≤0)(≥0) + (≥0)(≤0) ≤ 0`
    - `(M.mul N).β = (≤0)(≤0) + (≥0)(≥0) ≥ 0`
    - `(M.mul N).γ = (≥0)(≥0) + (≤0)(≤0) ≥ 0`
    - `(M.mul N).δ = (≥0)(≤0) + (≤0)(≥0) ≤ 0` -/
theorem cofactor_mul_odd_even {M N : CofactorMatrix}
    (hM : OddPattern M) (hN : EvenPattern N) :
    OddPattern (M.mul N) := by
  obtain ⟨hMα, hMβ, hMγ, hMδ⟩ := hM
  obtain ⟨hNα, hNβ, hNγ, hNδ⟩ := hN
  simp only [OddPattern, CofactorMatrix.mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (neg_nonneg.mpr hMα) hNα, mul_nonneg hMβ (neg_nonneg.mpr hNγ)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hMα) (neg_nonneg.mpr hNβ), mul_nonneg hMβ hNδ]
  · nlinarith [mul_nonneg hMγ hNα, mul_nonneg (neg_nonneg.mpr hMδ) (neg_nonneg.mpr hNγ)]
  · nlinarith [mul_nonneg hMγ (neg_nonneg.mpr hNβ), mul_nonneg (neg_nonneg.mpr hMδ) hNδ]

/-- Combined: the matrix product of two pattern-bearing matrices has a
    pattern. This is the Z/2-grading: Even⊕Even = Even, Even⊕Odd = Odd,
    Odd⊕Even = Odd, Odd⊕Odd = Even.

    Together with `lehmerCofactors_has_pattern` and the inductive structure
    of `hgcdMatrix`, this lemma is the key inductive step for
    `hgcdMatrix_has_pattern` below. -/
theorem cofactor_mul_pattern {M N : CofactorMatrix}
    (hM : EvenPattern M ∨ OddPattern M)
    (hN : EvenPattern N ∨ OddPattern N) :
    EvenPattern (M.mul N) ∨ OddPattern (M.mul N) := by
  rcases hM with hM | hM <;> rcases hN with hN | hN
  · exact Or.inl (cofactor_mul_even_even hM hN)
  · exact Or.inr (cofactor_mul_even_odd hM hN)
  · exact Or.inr (cofactor_mul_odd_even hM hN)
  · exact Or.inl (cofactor_mul_odd_odd hM hN)

/-- Sign-pattern invariant for `hgcdMatrix`: every matrix produced by
    Schönhage's recursive HGCD has `EvenPattern` or `OddPattern`.

    Proof: induction on fuel.
    - **Base** (`fuel = 0`): `id` has `EvenPattern`
      (`CofactorMatrix.id_even_pattern`).
    - **Threshold case** (`max a b < hgcdThreshold`): result is
      `lehmerCofactors hgcdThreshold a b id`; pattern by
      `lehmerCofactors_has_pattern`.
    - **Recursive case**: result is `M_outer.mul M_inner` where each factor
      has a pattern by IH; product has a pattern by `cofactor_mul_pattern`.

    This is the first half of the Session 13 plan (sign pattern lifted from
    Lehmer-only to HGCD). The downstream entry bound `hgcdMatrix_entry_bound`
    uses this together with a row-vector invariant + Cramer + det to bound
    individual entries by `max a b`. -/
theorem hgcdMatrix_has_pattern (fuel a b : ℕ) :
    EvenPattern (hgcdMatrix fuel a b) ∨ OddPattern (hgcdMatrix fuel a b) := by
  induction fuel generalizing a b with
  | zero =>
    rw [hgcdMatrix_zero]
    exact Or.inl CofactorMatrix.id_even_pattern
  | succ f ih =>
    rw [hgcdMatrix_succ]
    by_cases hsmall : max a b < hgcdThreshold
    · rw [if_pos hsmall]
      exact lehmerCofactors_has_pattern hgcdThreshold a b
    · rw [if_neg hsmall]
      -- Result is `M_outer.mul M_inner`. Each factor's pattern by IH;
      -- product by `cofactor_mul_pattern`.
      exact cofactor_mul_pattern
        (ih _ _) (ih (a / 2 ^ hgcdShift a b) (b / 2 ^ hgcdShift a b))

/-- Top-level HGCD has `EvenPattern` or `OddPattern`. -/
theorem hgcdMatrixOf_has_pattern (a b : ℕ) :
    EvenPattern (hgcdMatrixOf a b) ∨ OddPattern (hgcdMatrixOf a b) :=
  hgcdMatrix_has_pattern _ a b

-- ═══════════════════════════════════════════════════════════════
-- PART XI: ROW-VECTOR INVARIANT FOR `hgcdMatrix` (Session 14)
-- ═══════════════════════════════════════════════════════════════

/-! ### Row-vector invariant — base, threshold, and composition law

The PART V.5 row-vector invariant `(a₀, b₀) · M = (ahat', bhat')` is stated
for `lehmerCofactors`. To feed Cramer's identity (`row_vec_cramer`) and the
entry bounds (`entry_bound_of_even/odd`) at the level of the recursive
`hgcdMatrix`, we need the analogous existential row-vector statement for
`hgcdMatrix` itself, with **natural-number** witnesses for the residue pair.

This subsection contributes:
  * the **abstract composition law** `cofactor_mul_row_invariant`: if the
    row-vector relation holds for `M` between ghost `(a₀, b₀)` and
    intermediate `(ahat₁, bhat₁)`, and for `N` between `(ahat₁, bhat₁)` and
    final `(ahat₂, bhat₂)`, then it holds for `M.mul N` between
    `(a₀, b₀)` and `(ahat₂, bhat₂)`. Pure algebra (`ring` after expanding
    `cofactor_mul_row_output`).
  * the **base case** `hgcdMatrix_zero_row_invariant`: for `fuel = 0`,
    `hgcdMatrix` returns the identity, and the row-vector relation is just
    `(a, b) · id = (a, b)` with `max a b ≤ max a b`.
  * the **threshold case** `hgcdMatrix_small_row_invariant`: for
    `max a b < hgcdThreshold`, `hgcdMatrix (fuel+1) a b` reduces to
    `lehmerCofactors hgcdThreshold a b id`, and the existential
    row-vector invariant comes directly from `lehmerCofactors_id_apply_le`.

The recursive case `hgcdMatrix (f+1) a b = M_outer.mul M_inner` for inputs
above threshold is **not** proved here. The structural obstacle is that
`M_outer = hgcdMatrix f c1 c2` is built for inputs `(c1, c2)` derived from
the column-apply of `M_inner` on `(a, b)`, so its row-vector invariant (by
IH) is at ghost `(c1, c2)` rather than at `(a, b)`. Composing via
`cofactor_mul_row_invariant` therefore requires a row-vector invariant for
`M_outer` at the *full-precision* ghost `(a, b)`, which is precisely the
sorry of `hgcdMatrix_row_output_le` (recursive case). Establishing it
requires the joint induction documented in the PART IX docstring;
the abstract composition law contributed here will plug into that induction
once the entry-bound side is closed.

The base + threshold cases proved here are sufficient for the leaf of any
recursive analysis of HGCD; together with PART X's sign-pattern lifting,
they supply two of the three ingredients for `hgcdMatrix_entry_bound`. -/

/-- Sequential composition of the row-vector invariant through
    `CofactorMatrix.mul`.

    From the row-vector relations
      `a₀ · M.α + b₀ · M.γ = ahat₁`,  `a₀ · M.β + b₀ · M.δ = bhat₁`
    and
      `ahat₁ · N.α + bhat₁ · N.γ = ahat₂`,  `ahat₁ · N.β + bhat₁ · N.δ = bhat₂`,
    the row-vector relation holds for the product:
      `a₀ · (M.mul N).α + b₀ · (M.mul N).γ = ahat₂`,
      `a₀ · (M.mul N).β + b₀ · (M.mul N).δ = bhat₂`.

    Proof: substitute via `cofactor_mul_row_output` and use the inner
    relations linearly (`linear_combination`). This is the row-convention
    dual of the `cofactor_mul_apply` chaining rule. -/
theorem cofactor_mul_row_invariant {a₀ b₀ ahat₁ bhat₁ ahat₂ bhat₂ : ℤ}
    {M N : CofactorMatrix}
    (hM₁ : a₀ * M.α + b₀ * M.γ = ahat₁) (hM₂ : a₀ * M.β + b₀ * M.δ = bhat₁)
    (hN₁ : ahat₁ * N.α + bhat₁ * N.γ = ahat₂)
    (hN₂ : ahat₁ * N.β + bhat₁ * N.δ = bhat₂) :
    a₀ * (M.mul N).α + b₀ * (M.mul N).γ = ahat₂ ∧
    a₀ * (M.mul N).β + b₀ * (M.mul N).δ = bhat₂ := by
  obtain ⟨hα_eq, hβ_eq⟩ := cofactor_mul_row_output M N a₀ b₀
  refine ⟨?_, ?_⟩
  · rw [hα_eq, hM₁, hM₂]; linear_combination hN₁
  · rw [hβ_eq, hM₁, hM₂]; linear_combination hN₂

/-- Base case: at `fuel = 0`, `hgcdMatrix` returns `CofactorMatrix.id`,
    so the row-vector relation `(a, b) · id = (a, b)` holds with the input
    pair as the witness, trivially with `max a b ≤ max a b`. -/
theorem hgcdMatrix_zero_row_invariant (a b : ℕ) :
    ∃ ahat' bhat' : ℕ,
      (a : ℤ) * (hgcdMatrix 0 a b).α
        + (b : ℤ) * (hgcdMatrix 0 a b).γ = (ahat' : ℤ) ∧
      (a : ℤ) * (hgcdMatrix 0 a b).β
        + (b : ℤ) * (hgcdMatrix 0 a b).δ = (bhat' : ℤ) ∧
      max ahat' bhat' ≤ max a b := by
  rw [hgcdMatrix_zero]
  refine ⟨a, b, ?_, ?_, le_refl _⟩
  · simp [CofactorMatrix.id]
  · simp [CofactorMatrix.id]

/-- Threshold case: when `max a b < hgcdThreshold`,
    `hgcdMatrix (fuel+1) a b = lehmerCofactors hgcdThreshold a b id`,
    and `lehmerCofactors_id_apply_le` directly supplies natural-number
    witnesses for the row-vector relation, with the residue-monotonicity
    bound `max ahat' bhat' ≤ max a b`.

    This is the existential-witness companion of
    `hgcdMatrix_small_row_output_le`, exposing the natural witnesses that
    feed Cramer's identity (`row_vec_cramer`) for the entry bound. -/
theorem hgcdMatrix_small_row_invariant (fuel a b : ℕ)
    (h : max a b < hgcdThreshold) :
    ∃ ahat' bhat' : ℕ,
      (a : ℤ) * (hgcdMatrix (fuel + 1) a b).α
        + (b : ℤ) * (hgcdMatrix (fuel + 1) a b).γ = (ahat' : ℤ) ∧
      (a : ℤ) * (hgcdMatrix (fuel + 1) a b).β
        + (b : ℤ) * (hgcdMatrix (fuel + 1) a b).δ = (bhat' : ℤ) ∧
      max ahat' bhat' ≤ max a b := by
  rw [hgcdMatrix_small fuel a b h]
  exact lehmerCofactors_id_apply_le hgcdThreshold a b

-- ═══════════════════════════════════════════════════════════════
-- PART XII: PATTERN-DET COUPLING (Session 15)
-- ═══════════════════════════════════════════════════════════════

/-! ### Conjoint sign-pattern × determinant invariant

PART X (`hgcdMatrix_has_pattern`) proved that every matrix produced by
`hgcdMatrix` has `EvenPattern` or `OddPattern`. Independently, PART III
(`hgcdMatrix_det_unit`) proved that every such matrix has det ±1. This
subsection proves the **conjoint** invariant — pattern and determinant
are *coupled*:

    EvenPattern  ↔  det = 1,
    OddPattern   ↔  det = -1

(restricted to matrices produced by Lehmer or HGCD reductions starting
from the identity).

The coupling is a strict prerequisite for the entry-bound result.
`entry_bound_of_even` requires `det = 1`; `entry_bound_of_odd` requires
`det = -1`. Without the coupling, applying the right entry-bound lemma
in a downstream proof would require a four-way case split
(Even+1, Even+(-1), Odd+1, Odd+(-1)); two of those four cases never
occur, but ruling them out *is* this coupling.

Structure:
  * `lehmerInnerStep_pattern_det_coupled`: each `lehmerInnerStep`
    preserves the `(Even ∧ +1) ∨ (Odd ∧ -1)` disjunction.
  * `lehmerCofactors_pattern_det_coupled_from`: by induction on fuel,
    the coupling propagates through `lehmerCofactors`.
  * `lehmerCofactors_pattern_det_coupled`: specialisation to the
    identity matrix (the form HGCD's threshold case uses).
  * `cofactor_mul_pattern_det_coupled`: for products `M.mul N`, the
    Z/2-grading of the patterns coincides with the multiplicativity of
    the determinant, so the coupling is preserved.
  * `hgcdMatrix_pattern_det_coupled`: the conjoint invariant for HGCD,
    by induction on fuel.

This is one of the two prerequisites for `hgcdMatrix_entry_bound` (the
other being a row-vector invariant for the recursive case, which the
Stehlé–Zimmermann joint induction is designed to break). -/

/-- Each Lehmer step preserves the conjoint pattern-det invariant.

    Proof: combine `lehmerInnerStep_even_to_odd`/`lehmerInnerStep_odd_to_even`
    (PART VI) with `lehmerInnerStep_det` (BinaryGcdOQ03 PART IV), which
    flips the sign of the determinant. -/
theorem lehmerInnerStep_pattern_det_coupled
    {ahat bhat : ℕ} {M M' : CofactorMatrix} {ahat' bhat' : ℕ}
    (hstep : lehmerInnerStep ahat bhat M = some (ahat', bhat', M'))
    (h : (EvenPattern M ∧ M.det = 1) ∨ (OddPattern M ∧ M.det = -1)) :
    (EvenPattern M' ∧ M'.det = 1) ∨ (OddPattern M' ∧ M'.det = -1) := by
  have hflip : M'.det = -M.det := lehmerInnerStep_det hstep
  rcases h with ⟨heven, hdet⟩ | ⟨hodd, hdet⟩
  · -- (Even, +1) → (Odd, -1)
    refine Or.inr ⟨lehmerInnerStep_even_to_odd hstep heven, ?_⟩
    rw [hflip, hdet]
  · -- (Odd, -1) → (Even, +1)
    refine Or.inl ⟨lehmerInnerStep_odd_to_even hstep hodd, ?_⟩
    rw [hflip, hdet]; ring

/-- `lehmerCofactors` preserves the conjoint pattern-det invariant.

    Induction on fuel: each successful step flips both the pattern
    (`EvenPattern ↔ OddPattern`) and the determinant sign
    (`+1 ↔ -1`); termination (`none` branch) returns the input
    unchanged. -/
theorem lehmerCofactors_pattern_det_coupled_from
    (fuel ahat bhat : ℕ) (M₀ : CofactorMatrix)
    (h₀ : (EvenPattern M₀ ∧ M₀.det = 1) ∨ (OddPattern M₀ ∧ M₀.det = -1)) :
    (EvenPattern (lehmerCofactors fuel ahat bhat M₀)
        ∧ (lehmerCofactors fuel ahat bhat M₀).det = 1) ∨
    (OddPattern (lehmerCofactors fuel ahat bhat M₀)
        ∧ (lehmerCofactors fuel ahat bhat M₀).det = -1) := by
  induction fuel generalizing ahat bhat M₀ with
  | zero => simp [lehmerCofactors]; exact h₀
  | succ n ih =>
    simp only [lehmerCofactors]
    match hstep : lehmerInnerStep ahat bhat M₀ with
    | none => exact h₀
    | some (ahat', bhat', M') =>
      exact ih ahat' bhat' M' (lehmerInnerStep_pattern_det_coupled hstep h₀)

/-- Specialisation to `M₀ = id`: the identity matrix has `EvenPattern`
    and `det = 1`, so any `lehmerCofactors fuel ahat bhat id` satisfies
    the conjoint invariant. This is the form used by HGCD's threshold
    case. -/
theorem lehmerCofactors_pattern_det_coupled (fuel ahat bhat : ℕ) :
    (EvenPattern (lehmerCofactors fuel ahat bhat CofactorMatrix.id)
        ∧ (lehmerCofactors fuel ahat bhat CofactorMatrix.id).det = 1) ∨
    (OddPattern (lehmerCofactors fuel ahat bhat CofactorMatrix.id)
        ∧ (lehmerCofactors fuel ahat bhat CofactorMatrix.id).det = -1) :=
  lehmerCofactors_pattern_det_coupled_from fuel ahat bhat CofactorMatrix.id
    (Or.inl ⟨CofactorMatrix.id_even_pattern, CofactorMatrix.det_id⟩)

/-- The conjoint pattern-det invariant is preserved by matrix
    multiplication: the Z/2-grading on patterns matches the
    multiplicativity of the determinant.

      (Even, +1) · (Even, +1) = (Even, +1·+1 = +1)
      (Even, +1) · (Odd,  -1) = (Odd,  +1·-1 = -1)
      (Odd,  -1) · (Even, +1) = (Odd,  -1·+1 = -1)
      (Odd,  -1) · (Odd,  -1) = (Even, -1·-1 = +1)

    Pattern part by `cofactor_mul_even_even`/`cofactor_mul_even_odd`/
    `cofactor_mul_odd_even`/`cofactor_mul_odd_odd` (PART X);
    determinant part by `CofactorMatrix.det_mul` and arithmetic. -/
theorem cofactor_mul_pattern_det_coupled {M N : CofactorMatrix}
    (hM : (EvenPattern M ∧ M.det = 1) ∨ (OddPattern M ∧ M.det = -1))
    (hN : (EvenPattern N ∧ N.det = 1) ∨ (OddPattern N ∧ N.det = -1)) :
    (EvenPattern (M.mul N) ∧ (M.mul N).det = 1) ∨
    (OddPattern (M.mul N) ∧ (M.mul N).det = -1) := by
  rw [CofactorMatrix.det_mul]
  rcases hM with ⟨hMpat, hMdet⟩ | ⟨hMpat, hMdet⟩ <;>
    rcases hN with ⟨hNpat, hNdet⟩ | ⟨hNpat, hNdet⟩
  · -- Even · Even = Even, det = 1·1 = 1
    refine Or.inl ⟨cofactor_mul_even_even hMpat hNpat, ?_⟩
    rw [hMdet, hNdet]; norm_num
  · -- Even · Odd = Odd, det = 1·(-1) = -1
    refine Or.inr ⟨cofactor_mul_even_odd hMpat hNpat, ?_⟩
    rw [hMdet, hNdet]; ring
  · -- Odd · Even = Odd, det = (-1)·1 = -1
    refine Or.inr ⟨cofactor_mul_odd_even hMpat hNpat, ?_⟩
    rw [hMdet, hNdet]; ring
  · -- Odd · Odd = Even, det = (-1)·(-1) = 1
    refine Or.inl ⟨cofactor_mul_odd_odd hMpat hNpat, ?_⟩
    rw [hMdet, hNdet]; norm_num

/-- The conjoint pattern-det invariant for `hgcdMatrix`: every matrix
    produced by Schönhage's recursive HGCD satisfies one of:

      `EvenPattern ∧ det = 1`   or   `OddPattern ∧ det = -1`.

    Proof: induction on fuel.
    - Base (`fuel = 0`): identity is `(Even, det = 1)`.
    - Threshold case: `lehmerCofactors_pattern_det_coupled` applies
      directly.
    - Recursive case: the result is `M_outer.mul M_inner`; both factors
      satisfy the invariant by IH, and `cofactor_mul_pattern_det_coupled`
      lifts to the product.

    This is the Z/2-grading half of `hgcdMatrix_entry_bound`; combined
    with PART XI's row-vector invariant + `row_vec_cramer` +
    `entry_bound_of_even`/`entry_bound_of_odd`, it eliminates the
    spurious (Even ∧ -1) and (Odd ∧ +1) cases that would otherwise
    block applying the entry bound. -/
theorem hgcdMatrix_pattern_det_coupled (fuel a b : ℕ) :
    (EvenPattern (hgcdMatrix fuel a b)
        ∧ (hgcdMatrix fuel a b).det = 1) ∨
    (OddPattern (hgcdMatrix fuel a b)
        ∧ (hgcdMatrix fuel a b).det = -1) := by
  induction fuel generalizing a b with
  | zero =>
    rw [hgcdMatrix_zero]
    exact Or.inl ⟨CofactorMatrix.id_even_pattern, CofactorMatrix.det_id⟩
  | succ f ih =>
    rw [hgcdMatrix_succ]
    by_cases hsmall : max a b < hgcdThreshold
    · rw [if_pos hsmall]
      exact lehmerCofactors_pattern_det_coupled hgcdThreshold a b
    · rw [if_neg hsmall]
      exact cofactor_mul_pattern_det_coupled
        (ih _ _) (ih (a / 2 ^ hgcdShift a b) (b / 2 ^ hgcdShift a b))

/-- Top-level HGCD satisfies the conjoint pattern-det invariant. -/
theorem hgcdMatrixOf_pattern_det_coupled (a b : ℕ) :
    (EvenPattern (hgcdMatrixOf a b) ∧ (hgcdMatrixOf a b).det = 1) ∨
    (OddPattern (hgcdMatrixOf a b) ∧ (hgcdMatrixOf a b).det = -1) :=
  hgcdMatrix_pattern_det_coupled _ a b

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

10. **Row-convention decomposition** (PART VIIb, Session 11):
    - `row_product_decompose`: for `a = aHi·2^s + aLo`, `b = bHi·2^s + bLo`,
      the row products `a·M.α + b·M.γ` and `a·M.β + b·M.δ` factor as
      `2^s · (aHi·M.α + bHi·M.γ) + (aLo·M.α + bLo·M.γ)` (and symmetrically).
    - `row_product_with_invariant`: if `aHi·M.α + bHi·M.γ = aHi'` and
      `aHi·M.β + bHi·M.δ = bHi'`, then the full-precision row products simplify
      to `2^s · aHi' + low-order term`. Both proved by `ring` / `linear_combination`.

11. **Shift-position bound** (`hgcdShift_pos`): `hgcdShift a b ≥ 1` when
    `max a b ≥ 4`. Proof: `Nat.log 2 (max a b) ≥ 2` for input ≥ 4, so
    `(2+1)/2 = 1`. Uses `Nat.log_mono_right`.

12. **Top-half strictly smaller** (`hgcdShift_top_lt`): for threshold inputs,
    `max (a / 2^s) (b / 2^s) < max a b`. This is the **induction-measure
    decrease** needed for the Step 4 strong induction. Proof: `2^s ≥ 2`
    from hgcdShift_pos, then `Nat.div_lt_self`.

13. **Column-convention counterexample** (PART IX): `hgcdMatrix_joint_bound`
    as previously stated is FALSE. For (a, b) = (37, 5), the column output
    component has natAbs = 184 > 64 = 2^(hgcdShift 37 5 + 3). Verified by
    `native_decide`. The column convention `M.apply(a,b)` does NOT bound
    Euclidean residues for a right-accumulated Lehmer matrix.

14. **Base-case row output bound** (`hgcdMatrix_small_row_output_le`): for
    `max a b < hgcdThreshold`, the ROW output `(a·M.α + b·M.γ, a·M.β + b·M.δ)`
    of `hgcdMatrix (fuel+1) a b` is ≤ `max a b`. Proved using `hgcdMatrix_small`
    and `lehmerCofactors_id_apply_le`.

15. **Row-output composition under `mul`** (PART VIIc, Session 12):
    - `cofactor_row_natAbs_le`: row-convention triangle bound,
      `(a·M.α + b·M.γ).natAbs ≤ |a|·|M.α| + |b|·|M.γ|` (and symmetrically).
    - `cofactor_row_natAbs_le_of_entry_bounds`: combined bound, given
      `|M.•| ≤ E` and `|a|, |b| ≤ R`, both row products are ≤ `2·E·R`.
    - `cofactor_mul_row_output`: the algebraic identity
      `a·(M.mul N).α + b·(M.mul N).γ = N.α·(a·M.α + b·M.γ) + N.γ·(a·M.β + b·M.δ)`
      (and symmetrically). Row output of `M.mul N` on `(a, b)` equals the row
      output of `N` evaluated at the row output of `M` on `(a, b)`. This is
      the row-convention dual of `cofactor_mul_apply`. Proved by `ring`.
    - `cofactor_mul_row_output_natAbs_le`: from a row-output bound on `M`
      (`R`) and entry bounds on `N` (`E`), the row output of `M.mul N` is
      bounded by `2·E·R`. This decouples the IH for the inner matrix
      (entries) from the IH for the outer matrix (row output), avoiding the
      Session 11 obstacle where M₂'s IH was at the wrong inputs.

16. **Sign-pattern invariant for `hgcdMatrix`** (PART X, Session 13):
    - `cofactor_mul_even_even`, `cofactor_mul_odd_odd`, `cofactor_mul_even_odd`,
      `cofactor_mul_odd_even`: the four Z/2-graded multiplication cases
      (Even*Even = Odd*Odd = Even; Even*Odd = Odd*Even = Odd). Each proved
      by sign analysis (`nlinarith` with `mul_nonneg`).
    - `cofactor_mul_pattern`: combined existential — `M.mul N` has a pattern
      whenever both factors do.
    - `hgcdMatrix_has_pattern`, `hgcdMatrixOf_has_pattern`: every matrix
      produced by recursive HGCD has `EvenPattern` or `OddPattern`. Proved
      by induction on fuel: identity is Even (base), Lehmer threshold case
      via `lehmerCofactors_has_pattern`, recursive case via
      `cofactor_mul_pattern` and the IH for both subproblems.

    This lifts the sign-pattern half of Step 2b from `lehmerCofactors`-only
    to all of HGCD. It is the first half of the Session 13 plan
    (sign-pattern invariant); the entry-bound half remains as future work
    (it requires a row-vector invariant for HGCD, which requires solving the
    `hgcdMatrix_row_output_le` recursive case — circularity to be broken
    via joint induction).

17. **Row-vector invariant for `hgcdMatrix`** (PART XI, Session 14):
    - `cofactor_mul_row_invariant`: the abstract composition law for the
      row-vector relation through `M.mul N`. From
      `(a₀, b₀) · M = (ahat₁, bhat₁)` and `(ahat₁, bhat₁) · N = (ahat₂, bhat₂)`,
      deduces `(a₀, b₀) · (M.mul N) = (ahat₂, bhat₂)`. Proved via
      `cofactor_mul_row_output` plus linear substitution.
    - `hgcdMatrix_zero_row_invariant`: at `fuel = 0`, the row-vector
      relation is trivial — `(a, b) · id = (a, b)` with monotonicity bound
      `max a b ≤ max a b`.
    - `hgcdMatrix_small_row_invariant`: for inputs below threshold,
      `hgcdMatrix (fuel+1) a b = lehmerCofactors hgcdThreshold a b id` and
      the existential row-vector invariant + monotonicity comes directly
      from `lehmerCofactors_id_apply_le`. This exposes natural-number
      witnesses (rather than just the `natAbs` bound that
      `hgcdMatrix_small_row_output_le` provides), suitable for plugging
      into `row_vec_cramer` for entry bounds.

    The recursive case of `hgcdMatrix_row_invariant` is **not** closed
    here. Structural obstacle: `M_outer = hgcdMatrix f c1 c2` is built
    for column-output inputs `(c1, c2)` from `M_inner.apply ↑a ↑b`, so its
    IH-supplied row-vector invariant is at ghost `(c1, c2)`, not at the
    full-precision `(a, b)`. Composing via `cofactor_mul_row_invariant`
    therefore requires a row-vector invariant for `M_outer` at ghost
    `(a, b)` — exactly the obstacle of the `hgcdMatrix_row_output_le`
    sorry, which the joint induction (Stehlé–Zimmermann §4) is designed
    to break.

18. **Pattern-det coupling for `hgcdMatrix`** (PART XII, Session 15):
    - `lehmerInnerStep_pattern_det_coupled`: a single Lehmer step
      preserves the conjoint invariant
      `(EvenPattern ∧ det = 1) ∨ (OddPattern ∧ det = -1)`. Pattern flips
      via the PART VI alternation lemmas; det flips by
      `lehmerInnerStep_det`.
    - `lehmerCofactors_pattern_det_coupled_from`/
      `lehmerCofactors_pattern_det_coupled`: the conjoint invariant
      propagates through `lehmerCofactors`; the specialised form starts
      from `(EvenPattern id, det id = 1)`.
    - `cofactor_mul_pattern_det_coupled`: the Z/2-grading on patterns
      coincides with the multiplicativity of the determinant — products
      preserve the coupling. Combines the four PART X mul rules with
      `CofactorMatrix.det_mul`.
    - `hgcdMatrix_pattern_det_coupled`/`hgcdMatrixOf_pattern_det_coupled`:
      the conjoint invariant for HGCD by induction on fuel
      (base = identity, threshold via Lehmer coupling, recursive via
      `cofactor_mul_pattern_det_coupled`).

    This eliminates the spurious `(Even ∧ -1)` and `(Odd ∧ +1)` cases
    that would otherwise force a four-way split in any downstream
    entry-bound argument: with the coupling in hand, `det = 1` *forces*
    `EvenPattern`, so `entry_bound_of_even` applies directly (and
    symmetrically for odd/-1). This is the second prerequisite for
    `hgcdMatrix_entry_bound` (the first being the row-vector invariant
    at the recursive case, which still requires the
    Stehlé–Zimmermann joint induction).

**Remaining for size reduction (1 sorry):**
- `hgcdMatrix_row_output_le` (PART IX): the full row-output bound for all fuel.
  Base cases (fuel=0 and threshold case) are proved; the **missing piece** is the
  recursive case. The Session 12 infrastructure (PART VIIc) reframes the
  recursive case so that the inner subproblem `M_inner = hgcdMatrix f aHi bHi`
  contributes via *entry* bounds (still to be derived from
  `lehmerCofactors_has_pattern` + `entry_bound_of_even/odd`, lifted to
  arbitrary fuel) rather than via its row-output bound at the wrong inputs.
  The remaining gap is a `hgcdMatrix_entry_bound` lemma (analogue of
  `entry_bound_of_even/odd` for HGCD); Sessions 13–15 supply two of the
  three ingredients (sign pattern + pattern-det coupling); the row-vector
  invariant at the recursive case (PART XI Session 14 base/threshold +
  joint induction for the recursive case) remains future work.

**Out of scope (deferred):**
- Bit-complexity bound O(M(n)·log n): requires Mathlib infrastructure
  (fast multiplication, bit-complexity model) that does not yet exist.
-/

end HGcd
