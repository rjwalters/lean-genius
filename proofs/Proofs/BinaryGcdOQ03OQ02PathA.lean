/-
  Schönhage Recursive HGCD — Path A Foundation (Session 18, 2026-05-08)

  Background.
  Sessions 1–16 in `BinaryGcdOQ03OQ02.lean` developed a recursive HGCD
  matrix `hgcdMatrix` and pursued a "row-vector size-reduction"
  argument toward proving that the entries of the matrix returned by
  HGCD are bounded by the inputs (so that one matrix application
  performs Θ(log n) Euclidean steps without growth). Session 17
  (PR #17024) found a `native_decide`-checked counterexample at
  `(fuel, a, b) = (5, 130, 89)` showing that BOTH the row-output
  bound `(|a·α + b·γ|, |a·β + b·δ|) ≤ max a b` AND the column-output
  bound `(|α·a + β·b|, |γ·a + δ·b|) ≤ max a b` are FALSE for the
  current `hgcdMatrix` algorithm, with statistical incidence ≈ 39.6%
  on pairs above threshold. The recursive composition can produce
  matrix entries on the order of 10^268 for some inputs.

  This file (Path A in PR #17024's recommendation list).
  We define a SAFER variant `hgcdMatrixSafe` that adds a runtime
  size-reduction guard: in the recursive branch, the inner matrix
  is composed into the result only if applying it strictly reduces
  `max a b`; otherwise the inner matrix is returned unchanged.
  This matches GMP's `mpn_hgcd` strategy of aborting recursive
  composition when an iteration fails to reduce.

  The crucial structural property is that `hgcdMatrixSafe` ALWAYS
  preserves the GCD: the matrix returned is built only from
  determinant-±1 ingredients (Lehmer cofactors at the leaf;
  recursive products in the recursive branch), and on every code
  path the result has determinant ±1.

  Main theorems (this file, 0 sorries, 0 axioms):

  1. `hgcdMatrixSafe_det_unit` — the result of `hgcdMatrixSafe`
     has determinant ±1.

  2. `hgcdMatrixSafe_preserves_gcd` — applying `hgcdMatrixSafe`
     to `(a, b)` yields a pair whose `Int.gcd` equals
     `Nat.gcd a b`. Operational correctness of the safer
     algorithm.

  3. `hgcdMatrixSafeOf_det_unit` /
     `hgcdMatrixSafeOf_preserves_gcd` — top-level wrappers
     using sufficient fuel.

  Out of scope here: a positive size-reduction theorem
  (i.e. that on inputs above threshold the recursion makes
  measurable progress). Session 19+ work. The point of this
  file is to lay the GCD-preservation foundation for Path A so
  that subsequent work on size reduction has a definition with
  the right computational shape to reason about.

  References (re Path A motivation):
    - Stehlé & Zimmermann (2004), "A Binary Recursive Gcd
      Algorithm" (the abort-on-no-progress strategy).
    - GMP, `mpn/generic/hgcd.c` (the safety check in production
      code).
    - PR #17024 (Session 17 PART XIV counterexample).
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
import Proofs.BinaryGcdOQ03

open Nat Int LehmerGcd

namespace HGcdSafe

-- ═══════════════════════════════════════════════════════════════
-- PART I: BASIC CONSTANTS (mirrors `HGcd.hgcdThreshold`/`.hgcdShift`)
-- ═══════════════════════════════════════════════════════════════

/-- Recursion threshold for the safer HGCD: below this size the
    function falls back to a Lehmer cofactor accumulation, which is
    itself the unimodular building block from `BinaryGcdOQ03.lean`. -/
def hgcdThresholdSafe : ℕ := 64

/-- Half-bit shift for HGCD recursion: ⌈bits(max a b) / 2⌉.
    Same as `HGcd.hgcdShift`; redefined here to keep this file
    self-contained. -/
def hgcdShiftSafe (a b : ℕ) : ℕ := (Nat.log 2 (max a b) + 1) / 2

-- ═══════════════════════════════════════════════════════════════
-- PART II: SAFE HGCD WITH SIZE-REDUCTION GUARD
-- ═══════════════════════════════════════════════════════════════

/-- Schönhage's recursive HGCD with a size-reduction safety check.

    The body mirrors `HGcd.hgcdMatrix` except that, in the recursive
    branch, the outer-recursion call is guarded by a check that
    `max u v < max a b`, where `(u, v)` is the natAbs of the column
    output of the inner matrix on the full-precision pair `(a, b)`.
    If that check fails (e.g. the recursive composition would not
    decrease the inputs), the function aborts the second recursive
    call and returns the inner matrix `M_inner` unchanged.

    Crucially, the returned matrix is constructed exclusively from
    `lehmerCofactors`-derived blocks (det ±1 by
    `lehmerCofactors_det_unit`) combined under
    `CofactorMatrix.mul` (det multiplicative); on every code path
    the determinant is ±1 and the GCD is preserved.

    Termination: by `fuel`, exactly as in `HGcd.hgcdMatrix`. -/
def hgcdMatrixSafe : ℕ → ℕ → ℕ → CofactorMatrix
  | 0, _, _ => CofactorMatrix.id
  | fuel + 1, a, b =>
    if max a b < hgcdThresholdSafe then
      lehmerCofactors hgcdThresholdSafe a b CofactorMatrix.id
    else
      let M_inner :=
        hgcdMatrixSafe fuel (a / 2 ^ hgcdShiftSafe a b)
                            (b / 2 ^ hgcdShiftSafe a b)
      let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
      let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
      if max u v < max a b then
        (hgcdMatrixSafe fuel u v).mul M_inner
      else
        M_inner

/-- Top-level entry point: HGCD-safe with sufficient fuel. -/
def hgcdMatrixSafeOf (a b : ℕ) : CofactorMatrix :=
  hgcdMatrixSafe (a + b + 1) a b

/-- Reduction equation at `fuel + 1`. Stated as a `theorem` rather
    than a `private theorem` so downstream files (or this one's
    proofs) can rewrite cleanly without unfolding the auto-generated
    equation lemmas of the equation compiler. -/
theorem hgcdMatrixSafe_succ (f a b : ℕ) :
    hgcdMatrixSafe (f + 1) a b =
      (if max a b < hgcdThresholdSafe then
        lehmerCofactors hgcdThresholdSafe a b CofactorMatrix.id
      else
        let M_inner :=
          hgcdMatrixSafe f (a / 2 ^ hgcdShiftSafe a b)
                           (b / 2 ^ hgcdShiftSafe a b)
        let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
        let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
        if max u v < max a b then
          (hgcdMatrixSafe f u v).mul M_inner
        else
          M_inner) := by
  rfl

theorem hgcdMatrixSafe_zero (a b : ℕ) :
    hgcdMatrixSafe 0 a b = CofactorMatrix.id := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- PART III: DETERMINANT IS ±1 (the unimodularity invariant)
-- ═══════════════════════════════════════════════════════════════

/-- The matrix returned by `hgcdMatrixSafe` is unimodular.

    Proof: induction on fuel, case-splitting both `if` branches
    in the recursive case. The threshold case is
    `lehmerCofactors_det_unit` from `BinaryGcdOQ03`. Both branches
    of the safety guard preserve the unimodular invariant — the
    "abort" branch returns `M_inner` directly (unimodular by IH),
    the "compose" branch returns a product of two unimodular
    matrices (unimodular by `CofactorMatrix.det_mul`). -/
theorem hgcdMatrixSafe_det_unit (fuel a b : ℕ) :
    (hgcdMatrixSafe fuel a b).det = 1 ∨ (hgcdMatrixSafe fuel a b).det = -1 := by
  induction fuel generalizing a b with
  | zero =>
    rw [hgcdMatrixSafe_zero]
    exact Or.inl CofactorMatrix.det_id
  | succ f ih =>
    rw [hgcdMatrixSafe_succ]
    by_cases hsmall : max a b < hgcdThresholdSafe
    · -- Threshold branch.
      rw [if_pos hsmall]
      exact lehmerCofactors_det_unit hgcdThresholdSafe a b CofactorMatrix.id
        (Or.inl CofactorMatrix.det_id)
    · -- Recursive branch. Beta-reduce the `let`s so the inner `if` is
      -- visible to `by_cases`.
      rw [if_neg hsmall]
      dsimp only
      have hI := ih (a / 2 ^ hgcdShiftSafe a b) (b / 2 ^ hgcdShiftSafe a b)
      by_cases hreduce :
          max ((hgcdMatrixSafe f (a / 2 ^ hgcdShiftSafe a b)
                                  (b / 2 ^ hgcdShiftSafe a b)).apply
                  (a : ℤ) (b : ℤ)).1.natAbs
              ((hgcdMatrixSafe f (a / 2 ^ hgcdShiftSafe a b)
                                  (b / 2 ^ hgcdShiftSafe a b)).apply
                  (a : ℤ) (b : ℤ)).2.natAbs
            < max a b
      · -- Compose branch.
        rw [if_pos hreduce, CofactorMatrix.det_mul]
        have hO := ih
          ((hgcdMatrixSafe f (a / 2 ^ hgcdShiftSafe a b)
                              (b / 2 ^ hgcdShiftSafe a b)).apply
            (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe f (a / 2 ^ hgcdShiftSafe a b)
                              (b / 2 ^ hgcdShiftSafe a b)).apply
            (a : ℤ) (b : ℤ)).2.natAbs
        rcases hO with hO | hO <;> rcases hI with hI | hI <;>
          rw [hO, hI] <;> norm_num
      · -- Abort branch.
        rw [if_neg hreduce]
        exact hI

/-- Top-level safe HGCD has det ±1. -/
theorem hgcdMatrixSafeOf_det_unit (a b : ℕ) :
    (hgcdMatrixSafeOf a b).det = 1 ∨ (hgcdMatrixSafeOf a b).det = -1 :=
  hgcdMatrixSafe_det_unit _ a b

-- ═══════════════════════════════════════════════════════════════
-- PART IV: GCD PRESERVATION (the operational correctness statement)
-- ═══════════════════════════════════════════════════════════════

/-- Applying `hgcdMatrixSafe` to a pair `(a, b)` preserves their
    GCD. Direct corollary of `cofactor_apply_gcd` and
    `hgcdMatrixSafe_det_unit`: any unimodular matrix preserves
    the GCD when applied. -/
theorem hgcdMatrixSafe_preserves_gcd (fuel a b : ℕ) :
    Int.gcd ((hgcdMatrixSafe fuel a b).α * (a : ℤ)
              + (hgcdMatrixSafe fuel a b).β * (b : ℤ))
            ((hgcdMatrixSafe fuel a b).γ * (a : ℤ)
              + (hgcdMatrixSafe fuel a b).δ * (b : ℤ))
      = Nat.gcd a b :=
  cofactor_apply_gcd (hgcdMatrixSafe_det_unit fuel a b)

/-- Top-level safe HGCD preserves GCD. -/
theorem hgcdMatrixSafeOf_preserves_gcd (a b : ℕ) :
    Int.gcd ((hgcdMatrixSafeOf a b).α * (a : ℤ)
              + (hgcdMatrixSafeOf a b).β * (b : ℤ))
            ((hgcdMatrixSafeOf a b).γ * (a : ℤ)
              + (hgcdMatrixSafeOf a b).δ * (b : ℤ))
      = Nat.gcd a b :=
  hgcdMatrixSafe_preserves_gcd _ a b

-- ═══════════════════════════════════════════════════════════════
-- PART V: COMPUTATIONAL CHECKS (small concrete cases)
-- ═══════════════════════════════════════════════════════════════

/-- Below threshold, `hgcdMatrixSafe` reduces to a Lehmer cofactor
    accumulation. -/
theorem hgcdMatrixSafe_small (fuel a b : ℕ) (h : max a b < hgcdThresholdSafe) :
    hgcdMatrixSafe (fuel + 1) a b =
      lehmerCofactors hgcdThresholdSafe a b CofactorMatrix.id := by
  rw [hgcdMatrixSafe_succ, if_pos h]

/-- The base case is the identity matrix at any inputs. -/
example : hgcdMatrixSafe 0 100 75 = CofactorMatrix.id := by native_decide

example : hgcdMatrixSafe 5 0 0 = CofactorMatrix.id := by native_decide

-- Verify det ±1 on small concrete inputs.
example : (hgcdMatrixSafeOf 89 55).det = 1 ∨ (hgcdMatrixSafeOf 89 55).det = -1 :=
  hgcdMatrixSafeOf_det_unit 89 55

example : (hgcdMatrixSafeOf 100 75).det = 1 ∨ (hgcdMatrixSafeOf 100 75).det = -1 :=
  hgcdMatrixSafeOf_det_unit 100 75

/-- The PR #17024 counterexample input `(130, 89)`: under
    `hgcdMatrixSafe`, the result is still unimodular (whatever the
    runtime guard decides). This is the algorithmic safety net
    Path A provides — even when the "naive" composition would
    blow up, GCD preservation is unconditional. -/
example :
    (hgcdMatrixSafeOf 130 89).det = 1 ∨ (hgcdMatrixSafeOf 130 89).det = -1 :=
  hgcdMatrixSafeOf_det_unit 130 89

-- ═══════════════════════════════════════════════════════════════
-- PART VI: VERIFIED GCD FUNCTION (Session 19)
-- ═══════════════════════════════════════════════════════════════

/-! ### A correct HGCD-based GCD function

    Sessions 18 (this file's PARTS II–V) established the unimodularity
    and GCD-preservation foundation for `hgcdMatrixSafe`. Session 19
    (this PART) wraps that foundation into a TOTAL CORRECT GCD
    function `hgcdSafeGcd : ℕ → ℕ → ℕ` and proves
    `hgcdSafeGcd a b = Nat.gcd a b` unconditionally.

    The construction is direct: apply `hgcdMatrixSafeOf a b` to
    `(a, b)`, take the `Int.gcd` of the two output integers. By
    `hgcdMatrixSafeOf_preserves_gcd`, that integer GCD equals
    `Nat.gcd a b`.

    Significance. Per S17 PART XIV, the original unguarded
    `hgcdMatrix` produces matrix entries of order `10^268` for
    inputs as small as `(107, 85)`, which means `hgcdMatrix.apply`
    cannot be the basis of a verified GCD function on naturals
    (the column output exceeds any reasonable bound). The Path-A
    safety guard does not eliminate this magnitude blowup in the
    abort branch (where no reduction occurred), but the resulting
    matrix is still unimodular, so the COLUMN-OUTPUT GCD is still
    the original GCD — even if the column-output magnitudes are
    unbounded. The correctness of `hgcdSafeGcd` is therefore
    independent of the algorithm's size-reduction behaviour: it
    follows from the unimodularity invariant alone.

    What this does NOT prove: that `hgcdSafeGcd` runs in
    `O(M(n)·log n)` bit operations, or even that it asymptotically
    beats `Nat.gcd`. Those claims need (i) a bit-complexity model in
    Mathlib and (ii) a positive size-reduction theorem for
    `hgcdMatrixSafe` (which is not proved here — the runtime guard
    enables such a proof structurally, but the actual proof is S20+
    work). What S19 does prove: the algorithm RUNS to a correct
    answer on every natural-number input, with 0 sorries and 0
    axioms. -/

/-- Apply the top-level safe HGCD matrix to its inputs. Returns the
    `(α·a + β·b, γ·a + δ·b)` pair as integers. -/
def hgcdSafeApply (a b : ℕ) : ℤ × ℤ :=
  (hgcdMatrixSafeOf a b).apply (a : ℤ) (b : ℤ)

/-- The integer GCD of the two components of `hgcdSafeApply` equals
    the input `Nat.gcd`. Direct corollary of
    `hgcdMatrixSafeOf_preserves_gcd`, just unfolding `apply`. -/
theorem hgcdSafeApply_gcd_eq (a b : ℕ) :
    Int.gcd (hgcdSafeApply a b).1 (hgcdSafeApply a b).2 = Nat.gcd a b := by
  unfold hgcdSafeApply CofactorMatrix.apply
  -- After unfolding, the projections `.1`/`.2` reduce to the linear
  -- combinations and the goal matches `hgcdMatrixSafeOf_preserves_gcd`.
  exact hgcdMatrixSafeOf_preserves_gcd a b

/-- Verified HGCD-based GCD function: apply the safe HGCD matrix
    once and take the GCD of the column-output. -/
def hgcdSafeGcd (a b : ℕ) : ℕ :=
  let p := hgcdSafeApply a b
  Int.gcd p.1 p.2

/-- **Correctness of `hgcdSafeGcd`.** For all natural inputs,
    the HGCD-based GCD function agrees with the standard
    `Nat.gcd`. This is the operational endpoint of Path A's
    correctness story.

    Note: this theorem holds unconditionally — including on the
    PR #17024 counterexample family (e.g. `(130, 89)`, `(107, 85)`)
    where the unguarded `hgcdMatrix` produces magnitude blowup.
    The correctness depends only on `hgcdMatrixSafeOf` returning a
    unimodular matrix, which `hgcdMatrixSafeOf_det_unit` (S18)
    establishes for every input. -/
theorem hgcdSafeGcd_eq_gcd (a b : ℕ) : hgcdSafeGcd a b = Nat.gcd a b := by
  unfold hgcdSafeGcd
  exact hgcdSafeApply_gcd_eq a b

-- ═══════════════════════════════════════════════════════════════
-- PART VII: COMPUTATIONAL EXAMPLES (Session 19)
-- ═══════════════════════════════════════════════════════════════

/-! ### Computational verification on PR #17024 counterexamples

    These examples exercise `hgcdSafeGcd` on the inputs where the
    unguarded `hgcdMatrix` of S17 produced magnitude-blowup
    counterexamples. They reduce by `native_decide` to the standard
    GCD values, demonstrating that the column-output GCD is well-
    defined and matches `Nat.gcd` even where the matrix entries or
    column-output magnitudes might be huge.

    The `hgcdSafeGcd_eq_gcd` theorem proves these abstractly; the
    examples below are sanity checks that the kernel can reduce the
    closed-form definitions. -/

example : hgcdSafeGcd 0 0 = 0 := by native_decide

example : hgcdSafeGcd 12 8 = 4 := by native_decide

example : hgcdSafeGcd 89 55 = 1 := by native_decide

example : hgcdSafeGcd 100 75 = 25 := by native_decide

/-- The S17 counterexample input. Under the unguarded `hgcdMatrix`,
    the column output at `(130, 89)` and fuel 5 has α-component 1390
    and β-component -2287 — magnitudes far exceeding the inputs.
    Under `hgcdMatrixSafe`, the column-output magnitudes may still
    be large (we make no claim about them in this theorem), but the
    `Int.gcd` of the pair is well-defined and equals
    `Nat.gcd 130 89 = 1`. -/
example : hgcdSafeGcd 130 89 = 1 := by native_decide

/-- The S17 worst-case input from the survey range
    `[64, 130) × [64, a]`. Under the unguarded `hgcdMatrix`, the
    matrix entries reach magnitude on the order of `10^268`. Under
    `hgcdMatrixSafe` and `hgcdSafeGcd`, the result is the standard
    GCD `Nat.gcd 107 85 = 1`. -/
example : hgcdSafeGcd 107 85 = 1 := by native_decide

example : hgcdSafeGcd 1000 1000 = 1000 := by native_decide

end HGcdSafe

/-! ## Summary

**Proved (0 axioms, 0 sorries):**

1. **Determinant ±1 on every code path**
   (`hgcdMatrixSafe_det_unit`, S18):
   The safer HGCD always returns a unimodular matrix, regardless
   of whether the runtime size-reduction guard fires or aborts the
   recursive composition.

2. **GCD preservation under safe HGCD**
   (`hgcdMatrixSafe_preserves_gcd`, S18):
   Applying the safer HGCD matrix to `(a, b)` yields a pair whose
   `Int.gcd` equals `Nat.gcd a b`. This is the operational
   correctness statement, and it holds unconditionally — even on
   inputs (like `(130, 89)` from PR #17024's counterexample) where
   the original `hgcdMatrix` produces unbounded entries.

3. **Top-level wrappers**
   (`hgcdMatrixSafeOf`, `hgcdMatrixSafeOf_det_unit`,
   `hgcdMatrixSafeOf_preserves_gcd`, S18): convenient surface for
   callers that want HGCD with sufficient fuel pre-supplied.

4. **Verified HGCD-based GCD function**
   (`hgcdSafeGcd`, `hgcdSafeApply_gcd_eq`, `hgcdSafeGcd_eq_gcd`,
   S19, this PR): a TOTAL CORRECT GCD function based on Path A.
   `hgcdSafeGcd_eq_gcd` proves `hgcdSafeGcd a b = Nat.gcd a b`
   unconditionally, including on the PR #17024 counterexample
   inputs. Correctness depends only on the unimodularity invariant,
   not on size reduction (which remains the open subproblem).

**Path A roadmap (Session 20+):**

- Prove `hgcdMatrixSafe_size_reduction` (POSITIVE form): on inputs
  `max a b ≥ hgcdThresholdSafe`, when the runtime guard fires
  (compose branch), the column output `(M.apply a b).natAbs`
  strictly reduces. The runtime guard makes this provable
  structurally rather than via a deep algebraic lift of the
  row-vector invariant (which Session 17 showed is false for the
  unguarded `hgcdMatrix`).

- Quantitative bit-complexity bound: requires Mathlib
  infrastructure (fast multiplication, bit-complexity model)
  that does not exist. Out of scope until Mathlib lands these.

- Compare runtime behaviour of `hgcdMatrixSafe` against
  `hgcdMatrix` on the PR #17024 counterexample family
  (`(130, 89)`, the worst case `(107, 85)`, etc.) to verify the
  guard fires when expected.
-/
