/-
  HGCD (Half-GCD) -- Schönhage's recursive cofactor algorithm

  Open question OQ-02 of binary-gcd-OQ-03: can Schönhage's recursive
  HGCD be formalized?  We split the question into three parts:

  (A) **Correctness**: there is a function `hgcdMatrix : ℕ → ℕ → CofactorMatrix`
      such that for all `a b : ℕ`, `(hgcdMatrix a b).det ∈ {±1}` and
      applying it to `(a, b)` preserves `Nat.gcd a b`.

  (B) **Size reduction**: applying `hgcdMatrix a b` reduces the bitsize
      of `max a b` by approximately half (the genuinely new mathematical
      content vs. plain Lehmer).

  (C) **Bit complexity** O(M(n) log n): currently inexpressible in Mathlib
      because there is no bit-complexity model of arithmetic and no fast
      multiplication. Deferred -- documented as a Mathlib infrastructure gap.

  This file establishes (A), the matrix-vector invariant that
  underpins (B) (the row-vector relation `(a₀, b₀) · M = (current pair)`
  for `M = lehmerCofactors fuel a₀ b₀ id`), and the structural
  skeleton for (B). The size-reduction lemma itself is stated with
  the precise quantitative bound and marked `sorry`; closing it is
  the focus of follow-up sessions.

  All cofactor-matrix machinery (det, mul, apply, GCD invariance under
  unimodular matrices) is reused from `BinaryGcdOQ03.lean`.

  **Cofactor convention.** `lehmerCofactors` accumulates the cofactor
  matrix in the row-vector convention: each Lehmer step `S_k`
  right-multiplies the accumulator (`M' = M · S_k`), so the invariant
  maintained is `(a₀, b₀) · M = (current pair)`.

  Consequently this file's `applyToNat M a b` performs the row-vector
  product `(a, b) · M = (a·M.α + b·M.γ, a·M.β + b·M.δ)`, *not* the
  column-vector `M.apply` from `BinaryGcdOQ03.lean`. Both products
  preserve `Nat.gcd` when `det M = ±1`, but only the row product yields
  the actual reduced pair from the iterated Lehmer steps. The
  composition order in `hgcdMatrix` (`M_top.mul M_rec`, with the top
  step on the *left*) is similarly chosen so that
  `(a, b) · (M_top · M_rec) = ((a, b) · M_top) · M_rec` matches "apply
  the top-half step first, then recurse".

  References:
  - Schönhage (1971), "Schnelle Berechnung von Kettenbruchentwicklungen"
  - Brent & Zimmermann, "Modern Computer Arithmetic", §1.6.3
  - Stehlé & Zimmermann (2004), "A binary recursive gcd algorithm"
-/

import Proofs.BinaryGcdOQ03

open Nat Int

namespace LehmerGcd

-- ═══════════════════════════════════════════════════════════════
-- PART I: HGCD DEFINITION
-- ═══════════════════════════════════════════════════════════════

/-- Threshold below which HGCD bottoms out and returns the identity
    cofactor matrix. The caller is expected to fall back to plain
    Euclidean / Lehmer reduction below this size. -/
def hgcdThreshold : ℕ := 4

/-- One Lehmer-style reduction step on the top half of the bits of `(a, b)`.
    Given `a b : ℕ` with `max a b ≥ 2^hgcdThreshold`, extracts the top
    `n - n/2` bits and runs `lehmerCofactors` on the approximation to
    get a cofactor matrix.  Used as the recursive base step inside HGCD. -/
def hgcdTopHalfStep (a b : ℕ) : CofactorMatrix :=
  let n := Nat.log 2 (max a b) + 1
  let shift := n / 2
  let aHi := a / 2 ^ shift
  let bHi := b / 2 ^ shift
  -- Run plain Lehmer cofactor accumulation on the top half.
  -- Using the same `lehmerCofactors` routine that already has det-unit
  -- accounted for in BinaryGcdOQ03.
  lehmerCofactors n aHi bHi CofactorMatrix.id

/-- Apply a cofactor matrix to a non-negative pair, taking absolute values
    of the result.

    **Convention.** `lehmerCofactors` accumulates the cofactor matrix in the
    *row-vector* convention: each Lehmer step `S_k` right-multiplies the
    accumulator (`M' = M · S_k`), so the invariant maintained is
    `(a₀, b₀) · M = (current pair)`. Hence "applying" `M` to `(a, b)` to
    obtain the Lehmer-reduced pair means computing the row-vector product
    `(a, b) · M = (a·M.α + b·M.γ, a·M.β + b·M.δ)`.

    This is *not* the column-vector product `M.apply (a, b)` from
    `BinaryGcdOQ03.lean` (which would give `(M.α·a + M.β·b, M.γ·a + M.δ·b)`).
    Both products preserve `Nat.gcd` when `det M = ±1`, but only the
    row-vector product yields the actual reduced pair from the iterated
    Lehmer steps. See knowledge.md / state.md for the worked counterexample
    `(a, b) = (1000, 300)` where the column form does *not* reduce. -/
def applyToNat (M : CofactorMatrix) (a b : ℕ) : ℕ × ℕ :=
  let u : ℤ := (a : ℤ) * M.α + (b : ℤ) * M.γ
  let v : ℤ := (a : ℤ) * M.β + (b : ℤ) * M.δ
  (u.natAbs, v.natAbs)

/-- Recursive HGCD with explicit fuel. Returns a cofactor matrix `M` whose
    determinant is `±1` and which preserves `Nat.gcd`. The size-reduction
    property is stated separately.

    The recursive composition order — `M_top.mul M_rec` rather than
    `M_rec.mul M_top` — matches the row-vector convention: row-applying
    the composite is `(a, b) · M_top · M_rec`, i.e. apply the top-half
    step first, then apply the recursive matrix to the reduced pair. -/
def hgcdMatrix : (fuel a b : ℕ) → CofactorMatrix
  | 0,        _, _ => CofactorMatrix.id
  | fuel + 1, a, b =>
    if max a b < 2 ^ hgcdThreshold then
      CofactorMatrix.id
    else
      -- Step 1: reduce on the top half of the bits.
      -- Step 2: recurse on the reduced pair, compose, and return.
      -- (Branching on whether the half-reduced pair is small enough
      --  to skip the recursive call.)
      if (max (applyToNat (hgcdTopHalfStep a b) a b).1
              (applyToNat (hgcdTopHalfStep a b) a b).2)
          < 2 ^ hgcdThreshold then
        hgcdTopHalfStep a b
      else
        (hgcdTopHalfStep a b).mul
          (hgcdMatrix fuel
            (applyToNat (hgcdTopHalfStep a b) a b).1
            (applyToNat (hgcdTopHalfStep a b) a b).2)

-- ═══════════════════════════════════════════════════════════════
-- PART II: DETERMINANT IS ±1
-- ═══════════════════════════════════════════════════════════════

/-- The Lehmer cofactor accumulator preserves det = ±1 starting from
    the identity. Re-stated here for `hgcdTopHalfStep`. -/
theorem hgcdTopHalfStep_det_unit (a b : ℕ) :
    (hgcdTopHalfStep a b).det = 1 ∨ (hgcdTopHalfStep a b).det = -1 := by
  unfold hgcdTopHalfStep
  exact lehmerCofactors_det_unit _ _ _ _ (Or.inl CofactorMatrix.det_id)

/-- Helper: a product of two `±1` integers is itself `±1`. -/
private theorem mul_unit_of_unit_of_unit {x y : ℤ}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    subst hx <;> subst hy <;> simp

/-- The recursive HGCD matrix has determinant `±1`.

    Proof is by induction on the fuel. The fuel-zero case returns the
    identity matrix (det = 1). At successor fuel the definition has two
    nested `if`s; we branch on each and use `hgcdTopHalfStep_det_unit`
    plus the inductive hypothesis. The composed case uses
    `CofactorMatrix.det_mul`. -/
theorem hgcdMatrix_det_unit (fuel a b : ℕ) :
    (hgcdMatrix fuel a b).det = 1 ∨ (hgcdMatrix fuel a b).det = -1 := by
  induction fuel generalizing a b with
  | zero => left; exact CofactorMatrix.det_id
  | succ n ih =>
    simp only [hgcdMatrix]
    split_ifs with h₁ h₂
    · left; exact CofactorMatrix.det_id
    · exact hgcdTopHalfStep_det_unit a b
    · rw [CofactorMatrix.det_mul]
      exact mul_unit_of_unit_of_unit
        (hgcdTopHalfStep_det_unit a b)
        (ih (applyToNat (hgcdTopHalfStep a b) a b).1
            (applyToNat (hgcdTopHalfStep a b) a b).2)

-- ═══════════════════════════════════════════════════════════════
-- PART III: GCD PRESERVATION
-- ═══════════════════════════════════════════════════════════════

/-- Applying `hgcdMatrix` to `(a, b)` (row convention) preserves the GCD.
    This is the row-vector analogue of `cofactor_apply_gcd`; it follows from
    `gcd_cofactor_eq` applied to the relabelled coefficients
    `(α, β, γ, δ) ← (M.α, M.γ, M.β, M.δ)`, since the determinant condition
    `α·δ - β·γ = M.α·M.δ - M.γ·M.β = M.det = ±1` is symmetric under the
    swap `β ↔ γ`. -/
theorem hgcdMatrix_apply_gcd (fuel a b : ℕ) :
    let M := hgcdMatrix fuel a b
    Int.gcd ((↑a : ℤ) * M.α + ↑b * M.γ) ((↑a : ℤ) * M.β + ↑b * M.δ)
      = Nat.gcd a b := by
  set M := hgcdMatrix fuel a b
  have hdet : M.α * M.δ - M.γ * M.β = 1 ∨ M.α * M.δ - M.γ * M.β = -1 := by
    have h := hgcdMatrix_det_unit fuel a b
    simp only [CofactorMatrix.det] at h
    rcases h with h | h
    · left; linarith
    · right; linarith
  have h := gcd_cofactor_eq (α := M.α) (β := M.γ) (γ := M.β) (δ := M.δ)
              (a := a) (b := b) hdet
  -- h : Int.gcd (M.α * ↑a + M.γ * ↑b) (M.β * ↑a + M.δ * ↑b) = Nat.gcd a b
  -- Goal differs only by commutativity of `*` on `ℤ`.
  have eq1 : (↑a : ℤ) * M.α + ↑b * M.γ = M.α * ↑a + M.γ * ↑b := by ring
  have eq2 : (↑a : ℤ) * M.β + ↑b * M.δ = M.β * ↑a + M.δ * ↑b := by ring
  rw [eq1, eq2]
  exact h

-- ═══════════════════════════════════════════════════════════════
-- PART IV: MATRIX-VECTOR INVARIANT (foundational for size reduction)
-- ═══════════════════════════════════════════════════════════════

/-! ### Matrix-vector invariant for `lehmerCofactors`

The maintained invariant of the Lehmer-step machine is that the
accumulated cofactor matrix, applied (in row-vector convention) to
the *original* pair, recovers the *current* pair after each step.

Formally: if `(a₀, b₀)` is the initial pair (as integers, allowing
the proof to track sign cleanly) and `M` is the cofactor accumulator
at some intermediate step where the current pair is `(ahat, bhat)`,
then:

    a₀ * M.α + b₀ * M.γ = ahat
    a₀ * M.β + b₀ * M.δ = bhat

Starting from `M = id`, the relation holds trivially because
`(a₀, b₀) · id = (a₀, b₀)`. We prove it carries through one step
of `lehmerInnerStep`, then iterate to cover `lehmerCofactors`.

This invariant is the foundation of the size-reduction argument
for `hgcdMatrix_size_reduction`: combined with the bound
`bhat_final ≤ bhat₀` (Euclidean-step monotonicity, separate
lemma) and the determinant condition (Cramer inversion), it
gives entry bounds on the cofactor matrix.

The proof of `hgcdMatrix_size_reduction` itself is still `sorry`
in PART V; this PART supplies the first of three components
identified in the next-action plan in
`research/problems/binary-gcd-oq-03-oq-02/state.md`. -/

/-- Matrix-vector invariant for one Lehmer inner step.

    Given a "ghost original pair" `(a₀, b₀)` consistent with the
    current state `(ahat, bhat, M)` via the row-vector relation
    `(a₀, b₀) · M = (ahat, bhat)`, the relation persists after one
    `lehmerInnerStep` to the new state `(ahat', bhat', M')`.

    Proof: unfold `lehmerInnerStep` to extract the form of the new
    matrix entries (`α' = β`, `β' = α - q·β`, `γ' = δ`,
    `δ' = γ - q·δ`) and the new pair (`ahat' = bhat`,
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
    -- From Nat.div_add_mod: bhat * (ahat/bhat) + ahat % bhat = ahat
    -- Cast to ℤ: ↑bhat * ↑(ahat/bhat) + ↑(ahat%bhat) = ↑ahat
    -- Then commute multiplication and rearrange.
    have hdivmod_int :
        (bhat : ℤ) * ((ahat / bhat : ℕ) : ℤ) + ((ahat % bhat) : ℤ) = (ahat : ℤ) := by
      exact_mod_cast Nat.div_add_mod ahat bhat
    have hcomm : ((ahat / bhat : ℕ) : ℤ) * (bhat : ℤ)
               = (bhat : ℤ) * ((ahat / bhat : ℕ) : ℤ) := by ring
    linarith

/-- Multi-step matrix-vector invariant for `lehmerCofactors`.

    Existential form: there exist final residues `(ahat', bhat')`
    such that applying the accumulated matrix to the ghost original
    pair recovers them. Proved by induction on `fuel`, applying
    `lehmerInnerStep_invariant` to the head step.

    Note: the existential form avoids defining a parallel
    "track residues" function; the residues are determined by the
    iterated `lehmerInnerStep`s, but expressing them explicitly is
    not needed for the entry-bound argument. -/
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
    input pair yields the final Euclidean-residue pair. This is the
    correctness of `applyToNat (lehmerCofactors fuel ahat bhat id)
    ahat bhat`: it equals the final reduced pair. -/
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

/-! ### Residue monotonicity (Step 2 toward size reduction)

The Lehmer-step machine never grows the residues: each successful
inner step sets `ahat' = bhat` and `bhat' = ahat % bhat`, so the
maximum of the pair is non-increasing. Composed over multiple
steps, this gives the bound `max ahat_final bhat_final ≤
max ahat_initial bhat_initial` for the iterated `lehmerCofactors`.

Combined with the matrix-vector invariant from PART IV, this
is the residue-bound half of the size-reduction proof: applying
the accumulated matrix to the input pair yields a Euclidean-
residue pair whose max is bounded by the input max. The
remaining piece is the cofactor-entry bound (Cramer inversion
applied to the invariant), which is the focus of follow-up
sessions. -/

/-- One successful Lehmer inner step strictly decreases `bhat` and
    sets `ahat' = bhat`. -/
theorem lehmerInnerStep_residue_le {ahat bhat : ℕ} {M : CofactorMatrix}
    {ahat' bhat' : ℕ} {M' : CofactorMatrix}
    (h : lehmerInnerStep ahat bhat M = some (ahat', bhat', M')) :
    bhat' < bhat ∧ ahat' = bhat := by
  simp [lehmerInnerStep] at h
  split at h <;> simp_all
  split at h <;> simp_all
  -- Surviving case: bhat ≠ 0 and ahat % bhat ≠ 0; substitution gives
  -- ahat' = bhat, bhat' = ahat % bhat, M' = explicit matrix.
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
  -- ahat' = bhat ≤ max ahat bhat; bhat' < bhat ≤ max ahat bhat.
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
    the "ghost original pair" being the actual input pair `(ahat, bhat)`.

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
-- PART V: SIZE REDUCTION (the genuinely new content)
-- ═══════════════════════════════════════════════════════════════

/-- The bitsize of a natural number: `Nat.log 2 n + 1` for `n > 0`,
    and `0` for `n = 0`. -/
def bitsize (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log 2 n + 1

@[simp] theorem bitsize_zero : bitsize 0 = 0 := by simp [bitsize]

/-- **Size reduction (statement)**: for inputs above the HGCD threshold,
    one application of `hgcdMatrix` reduces `bitsize (max a b)` to
    approximately `bitsize (max a b) / 2 + c`.

    This is the only mathematically novel claim in the file relative to
    `BinaryGcdOQ03.lean`; closing it is the next-session focus.

    The constant `c = hgcdThreshold + 2` is an over-approximation; the
    Brent–Zimmermann analysis gives `c = O(1)` more precisely.

    The matrix-vector invariant in PART IV is the first of three
    components needed to close this proof; the remaining two are
    (a) Euclidean-residue monotonicity (`bhat_final ≤ bhat₀`,
    derivable from `lehmerInnerStep` flipping `(ahat, bhat)` to
    `(bhat, ahat % bhat)` with `ahat % bhat < bhat`) and (b) a
    perturbation argument bounding the difference between
    `(a, b) · M` and `(aHi · 2^shift, bHi · 2^shift) · M = (aHi', bHi') · 2^shift`. -/
theorem hgcdMatrix_size_reduction (fuel a b : ℕ)
    (hfuel : bitsize (max a b) ≤ fuel)
    (hbig : 2 ^ hgcdThreshold ≤ max a b) :
    bitsize (max (applyToNat (hgcdMatrix fuel a b) a b).1
                 (applyToNat (hgcdMatrix fuel a b) a b).2)
      ≤ bitsize (max a b) / 2 + (hgcdThreshold + 2) := by
  -- Deferred: this is the substantive next-session goal. The proof
  -- requires:
  --   (a) bounding the entries of `hgcdTopHalfStep a b` by
  --       2^(bitsize(max a b)/2 + 2) (a Lehmer accumulator entry-bound
  --       lemma — likely Mathlib gap, may need to prove inline);
  --   (b) using the unimodularity to bound the entries of the inverse
  --       and hence the difference between (a, b) and the new pair;
  --   (c) iterating the half-reduction twice (once for the top step,
  --       once for the recursive call) to halve the bitsize.
  -- See research/problems/binary-gcd-oq-03-oq-02/state.md.
  sorry

-- ═══════════════════════════════════════════════════════════════
-- PART VI: COMPLEXITY (DEFERRED)
-- ═══════════════════════════════════════════════════════════════

/-! ### Bit-complexity claim — deferred

The classical Schönhage analysis gives `T_hgcd(n) = O(M(n) · log n)`
where `M(n)` is the bit cost of multiplying two `n`-bit integers and
`n = bitsize(max a b)`. We **cannot state this in Lean today** because:

* Mathlib has no bit-complexity model for arithmetic. `Computability`
  has Turing machines and `primrec` / `partrec`, but nothing that
  attaches "bit operations" to integer arithmetic primitives.
* Mathlib has no fast multiplication (Karatsuba, Toom–Cook,
  Schönhage–Strassen). All multiplication on `ℕ` / `ℤ` is opaque.
* There is no big-integer-as-array-of-words representation in Mathlib;
  `ℕ` and `ℤ` are abstract algebraic structures.

Filling these gaps is a multi-thousand-line Mathlib-contribution
initiative; we therefore document the complexity claim here without
attempting to formalise it. -/

-- ═══════════════════════════════════════════════════════════════
-- PART VII: COMPUTATIONAL SANITY CHECKS
-- ═══════════════════════════════════════════════════════════════

example : (hgcdMatrix 0 100 80).det = 1 := by
  unfold hgcdMatrix
  exact CofactorMatrix.det_id

example : (hgcdMatrix 5 7 3).det = 1 ∨ (hgcdMatrix 5 7 3).det = -1 :=
  hgcdMatrix_det_unit 5 7 3

example :
    let M := hgcdMatrix 4 5 3
    Int.gcd ((5 : ℤ) * M.α + (3 : ℤ) * M.γ) ((5 : ℤ) * M.β + (3 : ℤ) * M.δ)
      = Nat.gcd 5 3 :=
  hgcdMatrix_apply_gcd 4 5 3

/-- **Convention sanity check.** For `(a, b) = (1000, 300)` the top-half
    Lehmer step extracts `aHi = 31, bHi = 9` (`shift = 5`) and runs two
    cofactor steps, yielding `M = ⟨1, -2, -3, 7⟩`.

    * Row-apply (this file's convention):
      `(1000·1 + 300·(-3), 1000·(-2) + 300·7) = (100, 100)` — reduced.
    * Column-apply (the previous, *incorrect*, convention):
      `(1·1000 + (-2)·300, (-3)·1000 + 7·300) = (400, -900)` — *not* reduced.

    Both pairs preserve `Nat.gcd 1000 300 = 100`, but only the row-apply
    pair is a valid Lehmer reduction (max bit-size 7 < 10). -/
example : applyToNat (hgcdTopHalfStep 1000 300) 1000 300 = (100, 100) := by
  native_decide

/-! ## Summary

**Established (1 sorry, 0 axioms)**

* Definitions: `hgcdThreshold`, `hgcdTopHalfStep`, `applyToNat`, `hgcdMatrix`.
* `hgcdTopHalfStep_det_unit`: the top-half Lehmer step keeps `det = ±1`.
* `hgcdMatrix_det_unit`: the recursive HGCD matrix is unimodular.
* `hgcdMatrix_apply_gcd`: applying the HGCD matrix preserves `Nat.gcd`.
* `lehmerInnerStep_invariant`, `lehmerCofactors_invariant`,
  `lehmerCofactors_id_apply_eq`: the row-vector matrix-vector
  invariant `(a₀, b₀) · M = (current pair)` is preserved by the
  Lehmer-step machine. Foundational lemma for the size-reduction
  argument (Step 1 of three in the proof plan).

**Deferred**

* `hgcdMatrix_size_reduction`: stated, currently `sorry`. Proving it is
  the genuinely new mathematical content of this OQ; see Part V docstring.
  Step 1 (matrix-vector invariant) is now in PART IV; remaining work is
  Steps 2 (entry bound via Cramer + residue monotonicity) and 3
  (perturbation argument from low bits + recursion-iteration).
* Bit complexity `O(M(n) log n)`: not formulable in Mathlib today; see
  Part VI docstring for the foundational gaps.
-/

end LehmerGcd
