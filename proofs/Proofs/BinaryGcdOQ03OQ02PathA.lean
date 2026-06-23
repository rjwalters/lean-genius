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

-- ═══════════════════════════════════════════════════════════════
-- PART VIII: RECURSIVE SCHÖNHAGE GCD (Session 20)
-- ═══════════════════════════════════════════════════════════════

/-! ### Iterated Path-A GCD via guarded recursion

    Sessions 18–19 (PARTS II–VII) provide a verified single-step
    HGCD operation `hgcdSafeApply : ℕ → ℕ → ℤ × ℤ` whose component
    `Int.gcd` agrees with `Nat.gcd a b` unconditionally, plus a
    GCD function `hgcdSafeGcd` that wraps a single matrix
    application.

    This PART implements the Schönhage-style RECURSIVE GCD. The
    iteration applies `hgcdSafeApply` REPEATEDLY: each step
    produces a candidate smaller pair `(p.1.natAbs, p.2.natAbs)`,
    and we recurse on that pair WHEN — and only when — its `max`
    is strictly less than `max a b`. Two structural fallbacks make
    the function total and unconditionally correct:

      1. `max a b < hgcdThresholdSafe` ⇒ dispatch to `Nat.gcd`.
      2. Per-step size-reduction guard fails ⇒ dispatch to
         `Nat.gcd`.

    Termination. The recursion is structural on `fuel`, so Lean's
    equation compiler accepts the definition without a custom
    well-founded relation. Correctness (Theorem
    `schonhageGcd_eq_gcd`) is INDEPENDENT of whether the underlying
    `hgcdMatrixSafe`'s OWN runtime size-reduction guard ever fires.
    Even on pathological inputs where that guard always aborts
    (returning `M_inner` unchanged), the OUTER size-reduction
    guard here ensures the function still returns `Nat.gcd a b`.

    What this provides. A TOTAL CORRECT GCD function whose
    computational shape mirrors Schönhage's recursion. The
    quantitative speedup story (an `O(M(n)·log n)` bit-complexity
    bound) is deferred until Mathlib lands fast multiplication and
    a bit-complexity model — see the Path A roadmap in PART VI's
    docstring. -/

/-- Iterated Schönhage-style GCD, fuel-indexed for totality.

    On inputs above threshold, the body applies `hgcdSafeApply` once,
    obtaining a pair `(p.1, p.2)` of integers. If
    `max p.1.natAbs p.2.natAbs < max a b` (size reduction succeeded),
    we recurse on that pair. Otherwise — and on inputs below
    threshold — we fall back to `Nat.gcd`. -/
def schonhageGcd : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => Nat.gcd a b
  | fuel + 1, a, b =>
    if max a b < hgcdThresholdSafe then
      Nat.gcd a b
    else
      let p := hgcdSafeApply a b
      let a' := p.1.natAbs
      let b' := p.2.natAbs
      if max a' b' < max a b then
        schonhageGcd fuel a' b'
      else
        Nat.gcd a b

/-- Top-level entry point: fuel chosen so the recursion always
    reaches a base case before exhaustion. Each iteration that
    recurses strictly decreases `max a b` (by the runtime guard),
    so `max a b + 1` units of fuel suffice in the worst case where
    every step reduces by exactly one. The two fallback branches
    consume at most one fuel unit each before terminating. -/
def schonhageGcdOf (a b : ℕ) : ℕ := schonhageGcd (max a b + 1) a b

/-- Reduction equation at fuel 0. -/
theorem schonhageGcd_zero (a b : ℕ) :
    schonhageGcd 0 a b = Nat.gcd a b := rfl

/-- Reduction equation at fuel `f + 1`. Stated without `let`-binders
    so `rw` rewrites cleanly without needing `dsimp` on the inner
    `if`. -/
theorem schonhageGcd_succ (f a b : ℕ) :
    schonhageGcd (f + 1) a b =
      (if max a b < hgcdThresholdSafe then
        Nat.gcd a b
      else if max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
              < max a b then
        schonhageGcd f (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
      else
        Nat.gcd a b) := rfl

/-- Key step toward correctness. The natural-number components
    from one `hgcdSafeApply` step have the same `Nat.gcd` as the
    original input pair.

    Proof: `Int.gcd p.1 p.2` is defined as
    `Nat.gcd p.1.natAbs p.2.natAbs`, so the equality follows
    directly from S19's `hgcdSafeApply_gcd_eq`. -/
theorem hgcdSafeApply_natAbs_gcd (a b : ℕ) :
    Nat.gcd (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
      = Nat.gcd a b := by
  -- `Int.gcd m n` definitionally equals `Nat.gcd m.natAbs n.natAbs`,
  -- so `hgcdSafeApply_gcd_eq` discharges the goal directly.
  exact hgcdSafeApply_gcd_eq a b

/-- **Correctness of the iterated Schönhage-style GCD.**

    For every fuel and every pair of natural inputs,
    `schonhageGcd` agrees with `Nat.gcd`. Proof by induction on
    `fuel`. The base case (fuel 0) and both fallback branches
    return `Nat.gcd a b` directly. In the recursive branch, the
    induction hypothesis identifies the recursive call with
    `Nat.gcd p.1.natAbs p.2.natAbs`, which equals `Nat.gcd a b`
    by `hgcdSafeApply_natAbs_gcd`. -/
theorem schonhageGcd_eq_gcd (fuel a b : ℕ) :
    schonhageGcd fuel a b = Nat.gcd a b := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ f ih =>
    rw [schonhageGcd_succ]
    by_cases hsmall : max a b < hgcdThresholdSafe
    · rw [if_pos hsmall]
    · rw [if_neg hsmall]
      by_cases hreduce :
          max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
            < max a b
      · rw [if_pos hreduce]
        rw [ih (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs]
        exact hgcdSafeApply_natAbs_gcd a b
      · rw [if_neg hreduce]

/-- Top-level Schönhage GCD agrees with `Nat.gcd`. -/
theorem schonhageGcdOf_eq_gcd (a b : ℕ) :
    schonhageGcdOf a b = Nat.gcd a b :=
  schonhageGcd_eq_gcd _ a b

-- ═══════════════════════════════════════════════════════════════
-- PART IX: COMPUTATIONAL EXAMPLES — RECURSIVE SCHÖNHAGE (S20)
-- ═══════════════════════════════════════════════════════════════

/-! ### Sanity checks for `schonhageGcdOf`

    These exercise the recursive iteration. Inputs are chosen to
    cover the three branches:
      - Below-threshold dispatch (`Nat.gcd` fallback at small inputs).
      - Recursive iteration (above threshold, guard fires).
      - Pathological inputs from PR #17024's counterexample family. -/

example : schonhageGcdOf 0 0 = 0 := by native_decide

example : schonhageGcdOf 12 8 = 4 := by native_decide

example : schonhageGcdOf 89 55 = 1 := by native_decide

example : schonhageGcdOf 100 75 = 25 := by native_decide

/-- The S17 counterexample input `(130, 89)`. Even though the
    underlying `hgcdMatrix` is unbounded here, the Schönhage
    iteration is still well-defined and returns the correct GCD. -/
example : schonhageGcdOf 130 89 = 1 := by native_decide

example : schonhageGcdOf 107 85 = 1 := by native_decide

example : schonhageGcdOf 1000 1000 = 1000 := by native_decide

example : schonhageGcdOf 1000000 999999 = 1 := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- PART X: API SURFACE FOR `schonhageGcdOf` (S21)
-- ═══════════════════════════════════════════════════════════════

/-! ### `schonhageGcdOf` satisfies the standard `Nat.gcd` API

    With `schonhageGcdOf_eq_gcd` (S20) in hand, the entire
    `Nat.gcd` API transfers to the verified Schönhage GCD function
    by routine rewriting. The lemmas below state these wrappers
    explicitly so that downstream code can use `schonhageGcdOf`
    as a drop-in replacement for `Nat.gcd` without manually
    invoking the correctness theorem at every site.

    Each proof reduces to `schonhageGcdOf_eq_gcd` plus a single
    `Nat.gcd` lemma; the section is purely an API surface, with
    no new mathematical content beyond Session 20. The point is
    pragmatic: a verified GCD function should expose the same
    algebraic identities as the reference, and after S21 it does. -/

/-- Schönhage GCD with zero on the left: returns the right argument. -/
theorem schonhageGcdOf_zero_left (a : ℕ) : schonhageGcdOf 0 a = a := by
  rw [schonhageGcdOf_eq_gcd, Nat.gcd_zero_left]

/-- Schönhage GCD with zero on the right: returns the left argument. -/
theorem schonhageGcdOf_zero_right (a : ℕ) : schonhageGcdOf a 0 = a := by
  rw [schonhageGcdOf_eq_gcd, Nat.gcd_zero_right]

/-- Schönhage GCD of `a` with itself is `a`. -/
theorem schonhageGcdOf_self (a : ℕ) : schonhageGcdOf a a = a := by
  rw [schonhageGcdOf_eq_gcd, Nat.gcd_self]

/-- Schönhage GCD with one on the left collapses to one. -/
theorem schonhageGcdOf_one_left (a : ℕ) : schonhageGcdOf 1 a = 1 := by
  rw [schonhageGcdOf_eq_gcd, Nat.gcd_one_left]

/-- Schönhage GCD with one on the right collapses to one. -/
theorem schonhageGcdOf_one_right (a : ℕ) : schonhageGcdOf a 1 = 1 := by
  rw [schonhageGcdOf_eq_gcd, Nat.gcd_one_right]

/-- Schönhage GCD is commutative. -/
theorem schonhageGcdOf_comm (a b : ℕ) :
    schonhageGcdOf a b = schonhageGcdOf b a := by
  rw [schonhageGcdOf_eq_gcd, schonhageGcdOf_eq_gcd, Nat.gcd_comm]

/-- The Schönhage GCD divides the first argument. -/
theorem schonhageGcdOf_dvd_left (a b : ℕ) : schonhageGcdOf a b ∣ a := by
  rw [schonhageGcdOf_eq_gcd]; exact Nat.gcd_dvd_left a b

/-- The Schönhage GCD divides the second argument. -/
theorem schonhageGcdOf_dvd_right (a b : ℕ) : schonhageGcdOf a b ∣ b := by
  rw [schonhageGcdOf_eq_gcd]; exact Nat.gcd_dvd_right a b

/-- Universal property: any common divisor divides the Schönhage GCD. -/
theorem dvd_schonhageGcdOf {c a b : ℕ} (ha : c ∣ a) (hb : c ∣ b) :
    c ∣ schonhageGcdOf a b := by
  rw [schonhageGcdOf_eq_gcd]; exact Nat.dvd_gcd ha hb

/-- Schönhage GCD is associative. -/
theorem schonhageGcdOf_assoc (a b c : ℕ) :
    schonhageGcdOf (schonhageGcdOf a b) c
      = schonhageGcdOf a (schonhageGcdOf b c) := by
  rw [schonhageGcdOf_eq_gcd, schonhageGcdOf_eq_gcd, schonhageGcdOf_eq_gcd,
      schonhageGcdOf_eq_gcd, Nat.gcd_assoc]

/-- Schönhage GCD vanishes precisely when both inputs vanish. -/
theorem schonhageGcdOf_eq_zero_iff (a b : ℕ) :
    schonhageGcdOf a b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [schonhageGcdOf_eq_gcd, Nat.gcd_eq_zero_iff]

/-- **Fuel irrelevance.** The fuel-indexed `schonhageGcd` is
    fundamentally fuel-free: every choice of fuel yields the same
    answer (namely `Nat.gcd a b`). The fuel parameter exists only
    to satisfy Lean's structural recursion checker; semantically
    the function is `Nat.gcd`.

    This packages a corollary of `schonhageGcd_eq_gcd` that
    downstream consumers find more directly useful when fuel
    accounting bookkeeping would otherwise pollute proofs. -/
theorem schonhageGcd_fuel_irrelevant (f₁ f₂ a b : ℕ) :
    schonhageGcd f₁ a b = schonhageGcd f₂ a b := by
  rw [schonhageGcd_eq_gcd, schonhageGcd_eq_gcd]

-- ═══════════════════════════════════════════════════════════════
-- PART XI: ADDITIONAL ALGEBRAIC IDENTITIES (S22)
-- ═══════════════════════════════════════════════════════════════

/-! ### Multiplicative laws, dvd-iff, positivity, coprimality

    Session 22 extends S21's API surface with six further
    `Nat.gcd` identities not previously packaged:

      * **Universal property as iff** (`schonhageGcdOf_dvd_iff`).
        S21 supplied `dvd_schonhageGcdOf` (one direction) and the
        two `_dvd_left`/`_dvd_right` lemmas; the iff form is the
        single statement downstream callers most often need.

      * **Multiplicative laws** (`_mul_left`, `_mul_right`). Scalar
        multiplication distributes through the Schönhage GCD,
        inherited from `Nat.gcd_mul_left`/`Nat.gcd_mul_right`.

      * **Strict positivity** (`_pos_of_pos_left`, `_pos_of_pos_right`).
        The Schönhage GCD is positive whenever at least one input
        is, mirroring `Nat.gcd_pos_of_pos_*`.

      * **Concrete coprimality witness** (`_succ_self`). Two
        consecutive natural numbers are coprime under the verified
        Schönhage GCD, lifting `Nat.coprime_succ_self`.

    Each proof reduces to `schonhageGcdOf_eq_gcd` plus the
    corresponding `Nat.gcd` Mathlib lemma. Mathematical content is
    inherited; the contribution is the named wrapper. -/

/-- Universal property as an iff: `c` divides the Schönhage GCD
    iff `c` divides both inputs. -/
theorem schonhageGcdOf_dvd_iff {c a b : ℕ} :
    c ∣ schonhageGcdOf a b ↔ c ∣ a ∧ c ∣ b := by
  rw [schonhageGcdOf_eq_gcd]
  exact Nat.dvd_gcd_iff

/-- Scalar multiplication on the left distributes through the
    Schönhage GCD. -/
theorem schonhageGcdOf_mul_left (k a b : ℕ) :
    schonhageGcdOf (k * a) (k * b) = k * schonhageGcdOf a b := by
  rw [schonhageGcdOf_eq_gcd, schonhageGcdOf_eq_gcd, Nat.gcd_mul_left]

/-- Scalar multiplication on the right distributes through the
    Schönhage GCD. -/
theorem schonhageGcdOf_mul_right (a b k : ℕ) :
    schonhageGcdOf (a * k) (b * k) = schonhageGcdOf a b * k := by
  rw [schonhageGcdOf_eq_gcd, schonhageGcdOf_eq_gcd, Nat.gcd_mul_right]

/-- Strict positivity from a positive left input. -/
theorem schonhageGcdOf_pos_of_pos_left (b : ℕ) {a : ℕ} (h : 0 < a) :
    0 < schonhageGcdOf a b := by
  rw [schonhageGcdOf_eq_gcd]
  exact Nat.gcd_pos_of_pos_left b h

/-- Strict positivity from a positive right input. -/
theorem schonhageGcdOf_pos_of_pos_right (a : ℕ) {b : ℕ} (h : 0 < b) :
    0 < schonhageGcdOf a b := by
  rw [schonhageGcdOf_eq_gcd]
  exact Nat.gcd_pos_of_pos_right a h

/-- Two consecutive naturals are coprime under `schonhageGcdOf`.
    Reduces via `schonhageGcdOf_eq_gcd` to `Nat.gcd (n + 1) n = 1`,
    then proved by the standard Bézout argument: any divisor `d`
    of both `n + 1` and `n` must divide their difference `1`, so
    `d = 1`. Self-contained proof using only core
    `Nat.gcd_dvd_left/right`, `Nat.dvd_sub'`, and
    `Nat.eq_one_of_dvd_one`. -/
theorem schonhageGcdOf_succ_self (n : ℕ) :
    schonhageGcdOf (n + 1) n = 1 := by
  rw [schonhageGcdOf_eq_gcd]
  have h1 : Nat.gcd (n + 1) n ∣ (n + 1) := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (n + 1) n ∣ n := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (n + 1) n ∣ 1 := by
    have hdvd : Nat.gcd (n + 1) n ∣ (n + 1) - n := Nat.dvd_sub h1 h2
    simpa using hdvd
  exact Nat.eq_one_of_dvd_one h3

-- ═══════════════════════════════════════════════════════════════
-- PART XII: EMPIRICAL COMPARISON WITNESSES (S22)
-- ═══════════════════════════════════════════════════════════════

/-! ### Native-decide witnesses across the S17 survey range

    Session 17 (PR #17024) characterised the pathological behaviour
    of the unguarded `hgcdMatrix` on the survey range
    `{(a, b) | 64 ≤ b ≤ a < 130}` — a 39.6%-density set of pairs
    where the column-output of the unguarded recursion blew up to
    magnitudes on the order of 10^268. The examples below confirm
    by `native_decide` that on a curated sample of inputs from that
    range (plus several adjacent above-threshold pairs),
    `schonhageGcdOf` returns the standard `Nat.gcd` value.

    These checks are direct consequences of `schonhageGcdOf_eq_gcd`
    (S20), but `native_decide` exercises the actual closed-form
    recursion: the kernel reduces every fuel level, every
    `hgcdSafeApply` call, every `hgcdMatrixSafe` recursion, and
    confirms the answer matches the reference GCD. They therefore
    serve as a computational sanity check on the entire Path A
    algorithmic stack, complementing the abstract correctness
    proof. -/

/-- Threshold-edge: `(64, 64)` is exactly at the threshold.
    `hgcdThresholdSafe = 64`, so `max a b = 64` is NOT strictly
    less than threshold; the recursive branch fires for the first
    iteration. -/
example : schonhageGcdOf 64 64 = 64 := by native_decide

/-- Threshold-edge: consecutive integers at the threshold. -/
example : schonhageGcdOf 65 64 = 1 := by native_decide

/-- Mid-range S17-survey example with non-trivial common factor. -/
example : schonhageGcdOf 121 88 = 11 := by native_decide

/-- Above-S17-survey range, with composite GCD. -/
example : schonhageGcdOf 200 175 = 25 := by native_decide

/-- Far above S17 range, large composite GCD: `gcd(2520, 1980) = 180`. -/
example : schonhageGcdOf 2520 1980 = 180 := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- PART XIII: OUTER GUARD CHARACTERISATION (Session 23)
-- ═══════════════════════════════════════════════════════════════

/-! ### Outer-guard predicate for `schonhageGcd`

    The recursive Schönhage GCD (PART VIII) has TWO control-flow
    forks per fuel step:

      1. **Threshold check** (line 434): below threshold, dispatch
         to `Nat.gcd`.
      2. **Outer size-reduction guard** (line 440): above threshold,
         recurse iff `max p.1.natAbs p.2.natAbs < max a b`, where
         `p = hgcdSafeApply a b`.

    The OUTER guard is the actual mechanism that handles the S17
    counterexample family `(130, 89)` etc.: even when the inner
    `hgcdMatrixSafe`'s matrix-level guard aborts (returning the
    inner matrix unchanged), the schonhageGcd's outer guard catches
    the lack of size reduction and falls back to `Nat.gcd`. The
    correctness of `schonhageGcd_eq_gcd` (S20) is independent of
    which branch fires; this PART makes the branching predicate
    explicit and characterises it.

    The headline theorem `schonhageGcd_succ_via_outerGuard` shows
    that one fuel step of `schonhageGcd` is fully determined by
    the outer-guard Boolean: when it fires we recurse on the
    reduced pair, otherwise we dispatch to `Nat.gcd`. -/

/-- Boolean predicate capturing the outer size-reduction guard from
    `schonhageGcd`'s recursive case (PART VIII line 440).

    Returns `true` iff applying `hgcdSafeApply` strictly reduces
    `max a b`; returns `false` on below-threshold inputs (where the
    algorithm has already dispatched to `Nat.gcd`) and on
    above-threshold inputs where the runtime size-reduction check
    fails. The predicate is `Decidable` on every input — the
    underlying inequality reduces to `Nat.decLt` once
    `hgcdSafeApply a b` is evaluated. -/
def schonhageOuterGuardFires (a b : ℕ) : Bool :=
  if max a b < hgcdThresholdSafe then
    false
  else
    decide (max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
              < max a b)

/-- Below threshold, the outer guard does not fire. Vacuously,
    since the threshold check handles all such inputs by
    dispatching to `Nat.gcd` before reaching the size-reduction
    fork. -/
theorem schonhageOuterGuardFires_below_threshold {a b : ℕ}
    (h : max a b < hgcdThresholdSafe) :
    schonhageOuterGuardFires a b = false := by
  unfold schonhageOuterGuardFires
  rw [if_pos h]

/-- Iff characterisation: the outer guard fires iff we are above
    threshold AND the post-application maximum is strictly smaller
    than the pre-application maximum. Conjunctive form, useful for
    extracting both facts from a single hypothesis. -/
theorem schonhageOuterGuardFires_iff {a b : ℕ} :
    schonhageOuterGuardFires a b = true ↔
      ¬ max a b < hgcdThresholdSafe ∧
        max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
          < max a b := by
  unfold schonhageOuterGuardFires
  by_cases hsmall : max a b < hgcdThresholdSafe
  · rw [if_pos hsmall]
    simp [hsmall]
  · rw [if_neg hsmall]
    simp [hsmall]

/-- Strict size-reduction is a direct consequence of the outer
    guard firing: the recursive call's input has strictly smaller
    `max` than the current call's. This is the *quantitative*
    content of the guard: every iteration on which we recurse
    reduces the working size by at least one. -/
theorem schonhageOuterGuardFires_strict_decrease {a b : ℕ}
    (h : schonhageOuterGuardFires a b = true) :
    max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
      < max a b :=
  (schonhageOuterGuardFires_iff.mp h).2

/-- Above-threshold specialisation of `schonhageOuterGuardFires_iff`.

    On any pair `(a, b)` whose `max` is at least `hgcdThresholdSafe`,
    the early-return branch of `schonhageOuterGuardFires` is excluded,
    and the predicate reduces purely to the size-reduction inequality.

    This is the workhorse "above-threshold ⇒ guard fires iff size
    reduces" form referenced by `s28b-inner-guard-equivalence-spec.md`
    §3, where the proposed S28b structural theorem extends it by
    relating the size-reduction predicate to the inner-guard branch
    of `hgcdMatrixSafe`. -/
theorem schonhageOuterGuardFires_above_iff {a b : ℕ}
    (h : ¬ max a b < hgcdThresholdSafe) :
    schonhageOuterGuardFires a b = true ↔
      max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
        < max a b := by
  rw [schonhageOuterGuardFires_iff, and_iff_right h]

/-- Above-threshold abort iff: the dual of `_above_iff`, packaging
    the `false` case of `schonhageOuterGuardFires` on above-threshold
    inputs as the size-NON-reduction inequality `max a b ≤ max u v`.

    Useful for case-splitting on the outer-guard predicate when the
    interesting information is the abort branch — the canonical
    setting for the S28a counterexamples `(130, 89)` and `(107, 85)`,
    which are above threshold and abort. -/
theorem schonhageOuterGuardFires_above_aborts_iff {a b : ℕ}
    (h : ¬ max a b < hgcdThresholdSafe) :
    schonhageOuterGuardFires a b = false ↔
      max a b ≤ max (hgcdSafeApply a b).1.natAbs
                    (hgcdSafeApply a b).2.natAbs := by
  constructor
  · intro hfalse
    by_contra hlt
    push_neg at hlt
    have htrue : schonhageOuterGuardFires a b = true :=
      schonhageOuterGuardFires_iff.mpr ⟨h, hlt⟩
    simp [htrue] at hfalse
  · intro hge
    by_contra hne
    have htrue : schonhageOuterGuardFires a b = true := by
      cases hb : schonhageOuterGuardFires a b
      · exact absurd hb hne
      · rfl
    exact Nat.not_lt.mpr hge
      (schonhageOuterGuardFires_strict_decrease htrue)

/-- Disjunctive iff for the outer-guard `false` case. The predicate
    `schonhageOuterGuardFires a b = false` decomposes into a
    two-disjunct characterisation: either the input is below the
    safe-HGCD threshold (early-return branch), or the input is above
    threshold but `hgcdSafeApply` does not strictly reduce `max a b`
    (size-reduction failure). The simplification

    `(below) ∨ (max a b ≤ max u v)`

    folds the above-threshold + size-failure clause into a single
    inequality that holds vacuously below threshold (since both sides
    of the conjunction are then unconstrained), giving a clean
    flat disjunction.

    This is the structural counterpart of `schonhageOuterGuardFires_iff`
    for the negative branch, supporting reasoning patterns where one
    case-splits on `outer = false` and needs to extract WHY the guard
    failed (early return vs size-failure). -/
theorem schonhageOuterGuardFires_eq_false_iff {a b : ℕ} :
    schonhageOuterGuardFires a b = false ↔
      max a b < hgcdThresholdSafe ∨
      max a b ≤ max (hgcdSafeApply a b).1.natAbs
                    (hgcdSafeApply a b).2.natAbs := by
  by_cases hsmall : max a b < hgcdThresholdSafe
  · constructor
    · intro _; exact Or.inl hsmall
    · intro _; exact schonhageOuterGuardFires_below_threshold hsmall
  · rw [schonhageOuterGuardFires_above_aborts_iff hsmall]
    constructor
    · exact fun h => Or.inr h
    · rintro (h | h)
      · exact absurd h hsmall
      · exact h

/-- One fuel step of `schonhageGcd` is fully described by the
    outer-guard predicate. **Headline theorem of S23.** When
    `schonhageOuterGuardFires a b = true`, the recursive case
    iterates on the reduced pair; otherwise it falls back to
    `Nat.gcd`. The `Nat.gcd` branch covers BOTH the threshold case
    AND the above-threshold-no-reduction case, since the predicate
    returns `false` in both. -/
theorem schonhageGcd_succ_via_outerGuard (f a b : ℕ) :
    schonhageGcd (f + 1) a b =
      (if schonhageOuterGuardFires a b = true then
        schonhageGcd f (hgcdSafeApply a b).1.natAbs
                       (hgcdSafeApply a b).2.natAbs
      else
        Nat.gcd a b) := by
  rw [schonhageGcd_succ]
  by_cases hsmall : max a b < hgcdThresholdSafe
  · have hfalse : schonhageOuterGuardFires a b = false :=
      schonhageOuterGuardFires_below_threshold hsmall
    simp [hsmall, hfalse]
  · by_cases hg :
        max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
          < max a b
    · have htrue : schonhageOuterGuardFires a b = true :=
        schonhageOuterGuardFires_iff.mpr ⟨hsmall, hg⟩
      simp [hsmall, hg, htrue]
    · have hfalse : schonhageOuterGuardFires a b = false := by
        unfold schonhageOuterGuardFires
        rw [if_neg hsmall]
        simp [hg]
      simp [hsmall, hg, hfalse]

/-- Specialised reduction equation: when the outer guard fires
    above threshold, `schonhageGcd` recurses. Direct rewrite for
    proofs that case-split on the predicate. -/
theorem schonhageGcd_succ_recurse_of_fires (f a b : ℕ)
    (h : schonhageOuterGuardFires a b = true) :
    schonhageGcd (f + 1) a b =
      schonhageGcd f (hgcdSafeApply a b).1.natAbs
                     (hgcdSafeApply a b).2.natAbs := by
  rw [schonhageGcd_succ_via_outerGuard, if_pos h]

/-- Specialised reduction equation: when the outer guard does not
    fire, `schonhageGcd` falls back to `Nat.gcd`. Covers both the
    below-threshold and the above-threshold-no-reduction cases. -/
theorem schonhageGcd_succ_fallback_of_aborts (f a b : ℕ)
    (h : schonhageOuterGuardFires a b = false) :
    schonhageGcd (f + 1) a b = Nat.gcd a b := by
  rw [schonhageGcd_succ_via_outerGuard]
  simp [h]

-- ═══════════════════════════════════════════════════════════════
-- PART XIV: OUTER GUARD WITNESSES (Session 23)
-- ═══════════════════════════════════════════════════════════════

/-! ### Below-threshold witnesses

    By `schonhageOuterGuardFires_below_threshold`, the outer guard
    is uniformly `false` whenever `max a b < hgcdThresholdSafe = 64`.
    These `native_decide` checks confirm that the closed-form
    Boolean kernel agrees with the abstract characterisation on
    concrete sub-threshold inputs. -/

example : schonhageOuterGuardFires 0 0 = false := by native_decide

example : schonhageOuterGuardFires 5 3 = false := by native_decide

example : schonhageOuterGuardFires 12 8 = false := by native_decide

example : schonhageOuterGuardFires 63 1 = false := by native_decide

example : schonhageOuterGuardFires 63 63 = false := by native_decide

/-! ### Above-threshold abort witnesses (Session 28a)

    The S17 PR #17024 counterexample family `(130, 89)` and the
    statistical worst case `(107, 85)` (BinaryGcdOQ03OQ02 PART XIV)
    refute the naive S28 conjecture that "above-threshold + coprime
    implies the outer guard fires". On both pairs:

    * `min a b ≥ hgcdThresholdSafe`, so the early-return branch of
      `schonhageOuterGuardFires` is excluded.
    * `Nat.Coprime a b` holds (`130 = 2·5·13`, `89` is prime;
      `107` is prime, `85 = 5·17`).
    * Yet the outer guard returns `false`: per state.md S20 and
      `s28-coprime-firing-spec.md` §1, `hgcdMatrixSafe`'s OWN inner
      guard aborts on each pair, leaving the column-output `(u, v)`
      with `max u v ≥ max a b`, so `schonhageOuterGuardFires`
      evaluates the size-reduction predicate to `false`.

    The first witness in each block is the headline algorithm-level
    `native_decide` evaluation; the supporting `decide` facts
    contextualise it (coprimality + above-threshold). Together they
    document the canonical structural counterexample to the naive
    coprime-firing hypothesis. -/

example : schonhageOuterGuardFires 130 89 = false := by native_decide

example : Nat.Coprime 130 89 := by decide

example : hgcdThresholdSafe ≤ min 130 89 := by decide

example : schonhageOuterGuardFires 107 85 = false := by native_decide

example : Nat.Coprime 107 85 := by decide

example : hgcdThresholdSafe ≤ min 107 85 := by decide

-- ═══════════════════════════════════════════════════════════════
-- PART XV: SURVEY-RANGE TABULATION FRAMEWORK (Session 24)
-- ═══════════════════════════════════════════════════════════════

/-! ### Outer-guard density framework on the S17 counterexample range

    The S17 PART XIV counterexample family `(130, 89)` (BinaryGcd
    OQ03OQ02 PART XIV) sits inside a survey range
      `S = {(a, b) : 64 ≤ b ≤ a < 130}`.
    On `S` the row-vector invariant fails on a positive-density
    subset (PART XIV); the S23 outer guard `schonhageOuterGuardFires`
    catches every such pair and dispatches to `Nat.gcd`.

    This section provides the QUANTITATIVE infrastructure to measure
    outer-guard firing density on `S`:

      * `surveyRange`: the explicit list of all 2211 pairs
        (lower-triangular `[64, 130) × [64, 130)`).
      * `outerGuardFiresInSurveyRange`: count of pairs where the
        outer guard fires (`schonhageGcd` recurses on a strictly
        smaller pair).
      * `outerGuardAbortsInSurveyRange`: count of pairs where the
        outer guard aborts (`schonhageGcd` falls back to `Nat.gcd`).

    The exact numerical density is left as a future `native_decide`
    evaluation (each of the 2211 calls runs a full safe-HGCD
    recursion). This session establishes the data structure and
    the enumeration size; downstream callers can plug specific
    `native_decide` checks against the count definitions. -/

/-- Explicit enumeration of pairs `(a, b)` with `64 ≤ b ≤ a < 130`,
    constructed via nested `foldr` (no `bind` / `flatMap`
    dependency). The result is the lower-triangular set on
    `[64, 130) × [64, 130)`. -/
def surveyRange : List (ℕ × ℕ) :=
  (List.range 66).foldr
    (fun i acc =>
      (List.range (i + 1)).foldr
        (fun j acc' => (64 + i, 64 + j) :: acc') acc)
    []

/-- The survey range has exactly `2211 = 66 · 67 / 2` pairs.
    Verified by `native_decide` on a structural fold over `List.range`,
    independent of any `hgcdSafeApply` recursion. -/
theorem surveyRange_length : surveyRange.length = 2211 := by native_decide

/-- Count of pairs `(a, b)` in `surveyRange` for which the outer
    guard fires — equivalently, on which `schonhageGcd` recurses
    rather than falling back to `Nat.gcd`. -/
def outerGuardFiresInSurveyRange : ℕ :=
  (surveyRange.filter (fun p => schonhageOuterGuardFires p.1 p.2)).length

/-- Count of pairs `(a, b)` in `surveyRange` for which the outer
    guard aborts — equivalently, on which `schonhageGcd` falls back
    to `Nat.gcd` (whether because of below-threshold dispatch or
    because `hgcdSafeApply` did not strictly reduce `max a b`). -/
def outerGuardAbortsInSurveyRange : ℕ :=
  (surveyRange.filter (fun p => !schonhageOuterGuardFires p.1 p.2)).length

-- ═══════════════════════════════════════════════════════════════
-- PART XVI: GENERALISED FINSET DENSITY FRAMEWORK (Session 25)
-- ═══════════════════════════════════════════════════════════════

/-! ### Finset-parameterised density framework

    S24 (PART XV) introduced a `List`-based survey range
    hard-coded to the S17 PR #17024 region
    `{(a, b) : 64 ≤ b ≤ a < 130}`. This section provides the
    parallel **Finset-based, range-parameterised** framework,
    which complements S24 in three ways:

      * `outerGuardSurveyPairs lo hi : Finset (ℕ × ℕ)` is
        parameterised by `lo, hi` rather than fixed at `(64, 130)`,
        so the same density question can be asked on
        sub-threshold (`(0, 64)`), half-threshold (`(0, 32)`),
        or extended (`(64, 200)`) ranges with the same
        infrastructure.
      * `Finset.filter` / `Finset.card` directly support standard
        Mathlib lemmas — see `outerGuardFiringCount_le_surveySize`
        (a structural ≤ bound proved by `Finset.card_filter_le`).
      * A **closed-form below-threshold theorem**
        `outerGuardFiringCount_below_threshold` discharges the
        zero-firing question for any sub-threshold survey range
        without `native_decide` — leveraging S23's
        `_below_threshold` lemma and the conjunction-of-Ico
        membership conditions.

    Both frameworks compute the same survey-size on
    `(lo, hi) = (64, 130)`: `surveyRange_length = 2211 =
    (outerGuardSurveyPairs 64 130).card`. The S25 framework adds
    structural lemmas (provable, not just `native_decide`-checked)
    that scale to a general range.

    All lemmas in this section are unconditional (0 axioms,
    0 sorries). -/

/-- Finset of survey pairs `(a, b)` with `lo ≤ b ≤ a < hi`.
    Built as the lower-triangular part of the rectangle
    `Ico lo hi × Ico lo hi`. The S17 PR #17024 family
    corresponds to `outerGuardSurveyPairs 64 130`; the entire
    sub-threshold region to `outerGuardSurveyPairs 0 64`. -/
def outerGuardSurveyPairs (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico lo hi) ×ˢ (Finset.Ico lo hi)).filter (fun p => p.2 ≤ p.1)

/-- The firing subset of the Finset survey: pairs for which the
    S23 outer guard returns `true`. Companion to S24's
    `outerGuardFiresInSurveyRange` (the `List`-based,
    `(64, 130)`-fixed version). -/
def outerGuardFiringPairs (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  (outerGuardSurveyPairs lo hi).filter
    (fun p => schonhageOuterGuardFires p.1 p.2 = true)

/-- Cardinality of the parameterised survey range. Closed form
    when `lo ≤ hi`: equal to the triangular sum
    `(hi - lo) · (hi - lo + 1) / 2`. -/
def outerGuardSurveySize (lo hi : ℕ) : ℕ :=
  (outerGuardSurveyPairs lo hi).card

/-- Number of pairs in `outerGuardSurveyPairs lo hi` for which
    the outer guard fires. The density question of interest:
    how does `outerGuardFiringCount lo hi /
    outerGuardSurveySize lo hi` behave as `(lo, hi)` varies? -/
def outerGuardFiringCount (lo hi : ℕ) : ℕ :=
  (outerGuardFiringPairs lo hi).card

/-- The firing count is bounded above by the survey size.
    Trivial from `Finset.card_filter_le`: a filtered Finset has
    cardinality at most that of its parent. -/
theorem outerGuardFiringCount_le_surveySize (lo hi : ℕ) :
    outerGuardFiringCount lo hi ≤ outerGuardSurveySize lo hi := by
  unfold outerGuardFiringCount outerGuardSurveySize
         outerGuardFiringPairs
  exact Finset.card_filter_le _ _

/-- **Closed-form zero-firing below threshold.** When the entire
    survey region sits below `hgcdThresholdSafe = 64`, every
    pair has `max a b < 64`, so the S23 outer guard returns
    `false` uniformly and the firing count is zero. Direct
    corollary of S23's `schonhageOuterGuardFires_below_threshold`,
    leveraging the Finset structure (no `native_decide`
    enumeration required). -/
theorem outerGuardFiringCount_below_threshold (lo hi : ℕ)
    (h : hi ≤ hgcdThresholdSafe) :
    outerGuardFiringCount lo hi = 0 := by
  unfold outerGuardFiringCount outerGuardFiringPairs
         outerGuardSurveyPairs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  rw [Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico, Finset.mem_Ico] at hp
  obtain ⟨⟨⟨_hlo_a, ha_hi⟩, ⟨_hlo_b, hb_hi⟩⟩, _hba⟩ := hp
  have ha : p.1 < hgcdThresholdSafe := lt_of_lt_of_le ha_hi h
  have hb : p.2 < hgcdThresholdSafe := lt_of_lt_of_le hb_hi h
  have hmax : max p.1 p.2 < hgcdThresholdSafe := max_lt ha hb
  have := schonhageOuterGuardFires_below_threshold hmax
  rw [this]
  decide

-- ═══════════════════════════════════════════════════════════════
-- PART XVII: NATIVE-DECIDE WITNESSES (Session 25)
-- ═══════════════════════════════════════════════════════════════

/-! ### Combinatorial survey-size witnesses on multiple ranges

    These checks confirm `outerGuardSurveySize` reproduces the
    closed-form triangular sum
    `(hi - lo) · (hi - lo + 1) / 2` on concrete ranges. Pure
    combinatorics — does not invoke `hgcdSafeApply`, so all
    three witnesses evaluate fast. -/

/-- Survey size on the S17 PR #17024 family
    `{(a, b) : 64 ≤ b ≤ a < 130}`: `66 · 67 / 2 = 2211`. Matches
    S24's `surveyRange_length`. -/
example : outerGuardSurveySize 64 130 = 2211 := by native_decide

/-- Survey size on the entire below-threshold region
    `{(a, b) : 0 ≤ b ≤ a < 64}`: `64 · 65 / 2 = 2080`. -/
example : outerGuardSurveySize 0 64 = 2080 := by native_decide

/-- Survey size on the half-threshold region
    `{(a, b) : 0 ≤ b ≤ a < 32}`: `32 · 33 / 2 = 528`. -/
example : outerGuardSurveySize 0 32 = 528 := by native_decide

/-! ### Sub-threshold zero-firing witnesses

    Concrete `native_decide` evaluations of
    `outerGuardFiringCount` on sub-threshold survey regions.
    By `outerGuardFiringCount_below_threshold` these MUST be
    zero; the witnesses corroborate the closed-form theorem
    end-to-end (Finset filter + S23's Boolean kernel) on
    concrete inputs. -/

/-- The entire below-threshold region has zero firings. -/
example : outerGuardFiringCount 0 64 = 0 := by native_decide

/-- The half-threshold region has zero firings. -/
example : outerGuardFiringCount 0 32 = 0 := by native_decide

/-- A narrow sub-threshold band `[60, 64)` has zero firings. -/
example : outerGuardFiringCount 60 64 = 0 := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- PART XVIII: EMPTY-RANGE STRUCTURAL LEMMAS (Session 26)
-- ═══════════════════════════════════════════════════════════════

/-! ### Empty-range characterisation

    These lemmas dispatch the **degenerate case** `hi ≤ lo`
    (empty survey range) without `native_decide` enumeration,
    complementing S25's `outerGuardFiringCount_below_threshold`
    which dispatches the sub-threshold case `hi ≤ 64`.

    Together the two closed-form theorems cover every density
    question whose answer is forced to zero by structural
    constraints: empty range OR sub-threshold range. The remaining
    open density question — calibrating
    `outerGuardFiringCount 64 hi` for `hi > 64` — necessarily
    requires `native_decide` evaluation since the firing pattern
    depends on the actual `hgcdSafeApply` recursion.

    The proofs are routine `Finset.mem_filter` + `Finset.mem_Ico`
    + `omega` unfolding, with no dependence on `hgcdSafeApply`
    or `schonhageOuterGuardFires`. -/

/-- The parameterised survey range `outerGuardSurveyPairs lo hi`
    is empty iff `hi ≤ lo`. The forward direction uses the
    Finset.Ico structure; the backward direction exhibits the
    canonical witness `(lo, lo)`. -/
theorem outerGuardSurveyPairs_eq_empty_iff (lo hi : ℕ) :
    outerGuardSurveyPairs lo hi = ∅ ↔ hi ≤ lo := by
  unfold outerGuardSurveyPairs
  refine ⟨?_, ?_⟩
  · -- Empty filter ⟹ hi ≤ lo: contrapose, exhibit (lo, lo).
    -- v4.26.0: `contrapose!` pushes `≠ ∅` to `.Nonempty`, so we build the
    -- nonempty witness directly rather than deriving a contradiction.
    contrapose!
    intro hlt
    have hlo_mem : lo ∈ Finset.Ico lo hi := by
      rw [Finset.mem_Ico]; exact ⟨le_refl _, hlt⟩
    refine ⟨(lo, lo), ?_⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hlo_mem, hlo_mem⟩, le_refl _⟩
  · -- hi ≤ lo ⟹ empty: every candidate pair fails the Ico bound.
    intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product,
        Finset.mem_Ico, Finset.mem_Ico] at hp
    obtain ⟨⟨⟨hlo_a, ha_hi⟩, _⟩, _⟩ := hp
    omega

/-- The parameterised survey size is zero iff `hi ≤ lo`. Direct
    corollary of `outerGuardSurveyPairs_eq_empty_iff` via
    `Finset.card_eq_zero`. -/
theorem outerGuardSurveySize_eq_zero_iff (lo hi : ℕ) :
    outerGuardSurveySize lo hi = 0 ↔ hi ≤ lo := by
  unfold outerGuardSurveySize
  rw [Finset.card_eq_zero, outerGuardSurveyPairs_eq_empty_iff]

/-- **Closed-form zero-firing on empty range.** When the survey
    region is empty (`hi ≤ lo`), the firing count is trivially
    zero. Direct corollary via the cardinality bound from
    `outerGuardFiringCount_le_surveySize` plus
    `outerGuardSurveySize_eq_zero_iff`. -/
theorem outerGuardFiringCount_eq_zero_of_empty (lo hi : ℕ)
    (h : hi ≤ lo) : outerGuardFiringCount lo hi = 0 := by
  have hsize : outerGuardSurveySize lo hi = 0 :=
    (outerGuardSurveySize_eq_zero_iff lo hi).mpr h
  have hle := outerGuardFiringCount_le_surveySize lo hi
  omega

/-- The empty-range zero-firing theorem in iff form: firing count
    is zero on a degenerate range iff that range is degenerate.
    Note this is a one-direction iff specialisation; the
    converse direction "firing count zero ⟹ hi ≤ lo" is FALSE
    in general (e.g. firing count is also zero on sub-threshold
    ranges). The companion theorem `outerGuardSurveySize_eq_zero_iff`
    captures the actual two-way equivalence on the survey side. -/
theorem outerGuardFiringCount_eq_zero_of_size_zero (lo hi : ℕ)
    (hsize : outerGuardSurveySize lo hi = 0) :
    outerGuardFiringCount lo hi = 0 := by
  have hle := outerGuardFiringCount_le_surveySize lo hi
  omega

/-! ### Concrete empty-range witnesses

    Sanity checks confirming the empty-range theorems on
    degenerate inputs. These do not invoke `hgcdSafeApply`, so
    they evaluate fast. -/

/-- The flat range `[64, 64)` has size zero. -/
example : outerGuardSurveySize 64 64 = 0 := by
  rw [outerGuardSurveySize_eq_zero_iff]

/-- The reversed range `[130, 64)` has size zero. -/
example : outerGuardSurveySize 130 64 = 0 := by
  rw [outerGuardSurveySize_eq_zero_iff]; omega

/-- The flat range `[64, 64)` has zero firings. -/
example : outerGuardFiringCount 64 64 = 0 :=
  outerGuardFiringCount_eq_zero_of_empty 64 64 (le_refl _)

-- ═══════════════════════════════════════════════════════════════
-- PART XIX: TRIANGULAR CARDINALITY (Session 27)
-- ═══════════════════════════════════════════════════════════════

/-! ### Closed-form survey-size formula (structural)

    S25 (PART XVI) documented `outerGuardSurveySize lo hi` as the
    triangular sum `(hi - lo) · (hi - lo + 1) / 2`, and S25 PART
    XVII established the formula on three concrete ranges via
    `native_decide`. This section closes the gap with a fully
    structural proof.

    Strategy:
      * Recurrence (`outerGuardSurveySize_succ`): extending the
        survey range from `hi` to `hi + 1` (when `lo ≤ hi`) adds
        exactly the row `{(hi, b) | b ∈ Ico lo (hi + 1)}`, so the
        size grows by `hi + 1 - lo`. Proved by `ext` + Finset
        case-analysis with `omega`.
      * Closed form (`outerGuardSurveySize_triangular`): induction
        on the range width via `Nat.le_induction`, with the
        algebraic identity
        `m · (m + 1) / 2 + (m + 1) = (m + 1) · (m + 2) / 2`
        discharged by exhibiting an explicit `2 ∣ m · (m + 1)`
        witness and reducing via `omega`.

    Net contribution: the three S25 `native_decide` size witnesses
    (`528`, `2080`, `2211`) are now corollaries of one structural
    theorem, and the same closed form applies to every `(lo, hi)`
    with `lo ≤ hi` without any `native_decide` enumeration. -/

/-- **One-step recurrence for `outerGuardSurveySize`.** Extending
    the survey range from `hi` to `hi + 1` (with `lo ≤ hi`) adds
    exactly the new row `{(hi, b) | b ∈ Ico lo (hi + 1)}`, of
    cardinality `hi + 1 - lo`.

    Decomposition: the new survey set is the disjoint union of
    the old survey set (pairs with `a < hi`) and the new row
    (pairs with `a = hi` and `b ∈ [lo, hi + 1)`). The disjointness
    follows from `a < hi` (old) vs `a = hi` (new); the row's
    cardinality follows from `Finset.card_image_of_injective`
    applied to the injection `b ↦ (hi, b)`. -/
theorem outerGuardSurveySize_succ (lo hi : ℕ) (h : lo ≤ hi) :
    outerGuardSurveySize lo (hi + 1) =
      outerGuardSurveySize lo hi + (hi + 1 - lo) := by
  unfold outerGuardSurveySize outerGuardSurveyPairs
  set newRow := (Finset.Ico lo (hi + 1)).image (fun b => (hi, b)) with hnewRow
  have hunion :
      ((Finset.Ico lo (hi + 1)) ×ˢ (Finset.Ico lo (hi + 1))).filter
          (fun p => p.2 ≤ p.1) =
        ((Finset.Ico lo hi) ×ˢ (Finset.Ico lo hi)).filter
            (fun p => p.2 ≤ p.1) ∪ newRow := by
    ext ⟨a, b⟩
    simp only [hnewRow, Finset.mem_filter, Finset.mem_product,
               Finset.mem_Ico, Finset.mem_union, Finset.mem_image,
               Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha_lo, ha_hi⟩, hb_lo, hb_hi⟩, hba⟩
      by_cases hcase : a < hi
      · left
        refine ⟨⟨⟨ha_lo, hcase⟩, hb_lo, ?_⟩, hba⟩
        omega
      · push_neg at hcase
        have ha_eq : a = hi := by omega
        right
        exact ⟨b, ⟨hb_lo, hb_hi⟩, ha_eq.symm, rfl⟩
    · rintro (⟨⟨⟨ha_lo, ha_hi⟩, hb_lo, hb_hi⟩, hba⟩ |
              ⟨b', ⟨hb'_lo, hb'_hi⟩, ha_eq, hb_eq⟩)
      · refine ⟨⟨⟨ha_lo, by omega⟩, hb_lo, by omega⟩, hba⟩
      · subst ha_eq; subst hb_eq
        refine ⟨⟨⟨h, by omega⟩, hb'_lo, hb'_hi⟩, ?_⟩
        omega
  have hdisj :
      Disjoint
        (((Finset.Ico lo hi) ×ˢ (Finset.Ico lo hi)).filter
            (fun p => p.2 ≤ p.1))
        newRow := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    rw [hnewRow] at h2
    simp only [Finset.mem_filter, Finset.mem_product,
               Finset.mem_Ico] at h1
    simp only [Finset.mem_image, Prod.mk.injEq] at h2
    obtain ⟨⟨⟨_, ha_hi⟩, _, _⟩, _⟩ := h1
    obtain ⟨_, _, ha_eq, _⟩ := h2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hnew_card : newRow.card = hi + 1 - lo := by
    rw [hnewRow,
        Finset.card_image_of_injective _
          (fun a₁ a₂ heq => (Prod.mk.inj heq).2)]
    exact Nat.card_Ico ..
  rw [hnew_card]

/-- **Closed-form triangular cardinality.** The parameterised
    survey size `outerGuardSurveySize lo hi` equals the triangular
    sum `(hi - lo) · (hi - lo + 1) / 2` for all `lo ≤ hi`.

    By induction on the range width via `Nat.le_induction`. The
    base case `hi = lo` reduces to `0 = 0 · 1 / 2 = 0` via S26's
    `outerGuardSurveySize_eq_zero_iff`. The successor step uses
    `outerGuardSurveySize_succ` to add `(k + 1 - lo)` to the
    inductive value, and discharges the arithmetic identity
    `m · (m + 1) / 2 + (m + 1) = (m + 1) · (m + 2) / 2` (where
    `m = k - lo`) via explicit divisibility witnesses for
    `2 ∣ m · (m + 1)` and `2 ∣ (m + 1) · (m + 2)`, plus `omega`. -/
theorem outerGuardSurveySize_triangular (lo hi : ℕ) (h : lo ≤ hi) :
    outerGuardSurveySize lo hi = (hi - lo) * (hi - lo + 1) / 2 := by
  induction hi, h using Nat.le_induction with
  | base =>
    rw [(outerGuardSurveySize_eq_zero_iff lo lo).mpr le_rfl, Nat.sub_self]
  | succ k hk ih =>
    rw [outerGuardSurveySize_succ lo k hk, ih]
    have h1 : k + 1 - lo = (k - lo) + 1 := Nat.succ_sub hk
    rw [h1]
    set m := k - lo
    -- Goal: m * (m + 1) / 2 + (m + 1) = (m + 1) * ((m + 1) + 1) / 2
    -- Strategy: explicit witnesses for 2 ∣ m·(m+1) and
    -- 2 ∣ (m+1)·(m+2); then `omega` closes.
    have hdiv : 2 ∣ m * (m + 1) := by
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j * (2 * j + 1), by rw [hj]; ring⟩
      · exact ⟨(2 * j + 1) * (j + 1), by rw [hj]; ring⟩
    have hdiv' : 2 ∣ (m + 1) * ((m + 1) + 1) := by
      rcases Nat.even_or_odd (m + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j * (2 * j + 1), by rw [hj]; ring⟩
      · exact ⟨(2 * j + 1) * (j + 1), by rw [hj]; ring⟩
    obtain ⟨x, hx⟩ := hdiv
    obtain ⟨y, hy⟩ := hdiv'
    have hlhs : m * (m + 1) / 2 = x := by
      rw [hx]; exact Nat.mul_div_cancel_left x (by decide : (0 : ℕ) < 2)
    have hrhs : (m + 1) * ((m + 1) + 1) / 2 = y := by
      rw [hy]; exact Nat.mul_div_cancel_left y (by decide : (0 : ℕ) < 2)
    have h_alg : (m + 1) * ((m + 1) + 1) = m * (m + 1) + 2 * (m + 1) := by
      ring
    omega

/-! ### Concrete survey-size witnesses (structural)

    The S25 PART XVII `native_decide` survey-size witnesses are
    now structural corollaries of the closed-form triangular
    formula. Identical numerical content; the proofs no longer
    rely on `native_decide` enumeration over `Finset.Ico`. -/

/-- Survey size on the S17 PR #17024 family (lo = 64, hi = 130):
    `66 · 67 / 2 = 2211`. Structural derivation; matches S24's
    `surveyRange_length` and the S25 PART XVII witness. -/
theorem outerGuardSurveySize_64_130 :
    outerGuardSurveySize 64 130 = 2211 := by
  rw [outerGuardSurveySize_triangular 64 130 (by decide)]

/-- Survey size on the entire below-threshold region
    (lo = 0, hi = 64): `64 · 65 / 2 = 2080`. -/
theorem outerGuardSurveySize_0_64 :
    outerGuardSurveySize 0 64 = 2080 := by
  rw [outerGuardSurveySize_triangular 0 64 (by decide)]

/-- Survey size on the half-threshold region (lo = 0, hi = 32):
    `32 · 33 / 2 = 528`. -/
theorem outerGuardSurveySize_0_32 :
    outerGuardSurveySize 0 32 = 528 := by
  rw [outerGuardSurveySize_triangular 0 32 (by decide)]

/-! ### Bridge to S24's List-based survey

    The S24 (PART XV) `List`-based `surveyRange` and the S25
    (PART XVI) `Finset`-based `outerGuardSurveyPairs 64 130` both
    enumerate the lower-triangular set
    `{(a, b) : 64 ≤ b ≤ a < 130}` with cardinality 2211. This
    bridge theorem makes the equality explicit, derived from the
    structural closed form rather than `native_decide` on the
    underlying enumeration. -/

/-- **Bridge: S24 List length = S25 Finset cardinality on
    (64, 130).** Both frameworks enumerate the same
    lower-triangular range; their cardinalities agree at 2211. -/
theorem surveyRange_length_eq_outerGuardSurveySize :
    surveyRange.length = outerGuardSurveySize 64 130 := by
  rw [surveyRange_length, outerGuardSurveySize_64_130]

-- ═══════════════════════════════════════════════════════════════
-- PART XX: INNER-GUARD ABORT ⇒ OUTER-GUARD FAILURE (Session 29)
-- ═══════════════════════════════════════════════════════════════

/-! ### Inner-guard abort ⇒ outer-guard failure (above threshold)

    `s28b-inner-guard-equivalence-spec.md` (researcher-13, 2026-05-09;
    PR #17598) proposes the equivalence: on above-threshold inputs
    `(a, b)`, the outer guard `schonhageOuterGuardFires a b` fails to
    fire **iff** the inner `if max u v < max a b` of `hgcdMatrixSafe`
    takes the abort branch — i.e. `max u v ≥ max a b`, where `(u, v)`
    is the natAbs-pair of `M_inner.apply (a, b)` and `M_inner` is the
    inner recursive call.

    This session implements the **inner-abort ⇒ outer-fails** direction
    of that equivalence, building on the S28c packaging lemma
    `schonhageOuterGuardFires_above_aborts_iff` (PART XIII). The
    forward direction (compose ⇒ outer-fires) requires a non-expansion
    lemma for `hgcdMatrixSafe.apply` under composition — sketched in
    §5.2 of the spec — and is deferred to a future session.

    Significance. The canonical S28a witnesses `(130, 89)` and
    `(107, 85)` (PART XIV) are now structural corollaries of the
    inner-abort hypothesis rather than black-box `native_decide` facts
    on `schonhageOuterGuardFires`. The architectural refinement is
    that the ROOT CAUSE of outer-failure for these pairs is identified
    (the inner recursion's column-output exceeds the input bound)
    rather than merely observed at the kernel level. -/

/-- **Inner-guard abort ⇒ outer-guard failure** (above threshold).

    Above threshold (`hab`), if the inner-guard abort branch of
    `hgcdMatrixSafe (a + b + 1) a b` is taken — i.e., the natAbs-pair
    `(u, v)` of `M_inner.apply (a, b)` satisfies `max a b ≤ max u v`
    (`hge`) — then `schonhageOuterGuardFires a b = false`.

    Proof. Under `hab` and `hge`, `hgcdMatrixSafe_succ` reduces
    `hgcdMatrixSafeOf a b` to `M_inner` directly (the `else` branch of
    the inner `if`). Hence `hgcdSafeApply a b = M_inner.apply (a, b)`,
    whose natAbs-pair is exactly the `(u, v)` from `hge`. The
    conclusion follows by the S28c packaging lemma
    `schonhageOuterGuardFires_above_aborts_iff`. -/
theorem hgcdMatrixSafe_inner_abort_imp_outer_fails (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hge : max a b ≤
      max ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs) :
    schonhageOuterGuardFires a b = false := by
  -- Step 1: under (hab, hge), hgcdMatrixSafeOf a b = M_inner.
  have hMatrix : hgcdMatrixSafeOf a b
      = hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b) := by
    unfold hgcdMatrixSafeOf
    rw [hgcdMatrixSafe_succ, if_neg hab]
    -- After if_neg the RHS is the let-bundled inner if; beta-reduce
    -- the lets (same dsimp pattern as `hgcdMatrixSafe_det_unit`),
    -- then commit to the abort branch via if_neg on the inner if.
    dsimp only
    rw [if_neg (Nat.not_lt.mpr hge)]
  -- Step 2: hgcdSafeApply a b unfolds to M_inner.apply (a, b).
  have hApply : hgcdSafeApply a b
      = (hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ) := by
    unfold hgcdSafeApply
    rw [hMatrix]
  -- Step 3: bridge via the S28c packaging lemma.
  rw [schonhageOuterGuardFires_above_aborts_iff hab, hApply]
  exact hge

/-- **Direct witness: `(130, 89)` outer-fails.**

    The S28a `(130, 89)` outer-fails fact (PART XIV) discharged
    directly by `native_decide` on the full Boolean. The structural
    inner-abort route (`hgcdMatrixSafe_inner_abort_imp_outer_fails`)
    does not apply here: a hand-trace through `lehmerCofactors` on
    the shifted pair `(8, 5)` shows `M_inner = ⟨-1, 2, 2, -3⟩`,
    `M_inner.apply (130, 89) = (48, -7)`, and `natAbs.max = 48 < 130`
    — so the inner-abort hypothesis is arithmetically false at this
    pair. The CONCLUSION still holds (the algorithm takes the
    compose branch: `M_outer = ⟨1, -1, -6, 7⟩` over `(48, 7)` gives
    `(55, -337)`, `natAbs.max = 337 > 130`). See PR #19156 §8 for
    the full hand-trace. -/
example : schonhageOuterGuardFires 130 89 = false := by native_decide

/-- **Structural witness: `(107, 85)` outer-fails via inner-abort.**

    The `(107, 85)` worst-case S28a witness (PART XIV) likewise
    recovers as a corollary of inner-abort, with the inner-abort
    inequality `native_decide`-checked. -/
example : schonhageOuterGuardFires 107 85 = false :=
  hgcdMatrixSafe_inner_abort_imp_outer_fails 107 85
    (by decide) (by native_decide)

-- ═══════════════════════════════════════════════════════════════
-- PART XXI: COMPOSE-BRANCH DECOMPOSITION (Session 31)
-- ═══════════════════════════════════════════════════════════════

/-! ### Compose-branch matrix / apply decomposition

    PART XX (S30) implemented the **inner-abort ⇒ outer-fails**
    direction of the `s28b-inner-guard-equivalence-spec.md` §3
    equivalence: when the inner-guard abort branch of
    `hgcdMatrixSafe (a + b + 1) a b` is taken, the resulting
    `schonhageOuterGuardFires a b` is `false`.

    This session takes the structural step toward the converse
    direction (**compose ⇒ outer-fires**, spec §5.2). The full
    converse requires a non-expansion lemma
    `max ((M.mul N).apply a b).natAbs ≤ max (N.apply a b).natAbs`
    for general unimodular `M, N` — an open question per the
    spec. As a deliberate prerequisite, this section provides
    three building-block lemmas that are sorry-free, independent
    of the non-expansion question, and immediately reusable in any
    future closure of S31:

    1. `cofactor_mul_apply` — restated locally so this file does
       not need to import `BinaryGcdOQ03OQ02.lean` (which carries
       a 2000+ line preamble unrelated to PathA's purpose). The
       canonical statement at `BinaryGcdOQ03OQ02.lean:77` (in the
       `HGcd` namespace) is reproduced verbatim here under the
       `HGcdSafe` namespace.

    2. `hgcdMatrixSafeOf_compose_branch` — the **matrix-level**
       compose-branch decomposition. Mirror of S30's `hMatrix`
       local lemma, but for the inner-fires branch
       (`max u v < max a b`) rather than the inner-aborts branch.

    3. `hgcdSafeApply_compose_branch` — the **apply-level**
       compose-branch decomposition. Builds on (1) and (2): the
       column output `hgcdSafeApply a b` equals the outer matrix
       `hgcdMatrixSafe (a + b) u v` applied to the inner's column
       output `M_inner.apply (a, b)`.

    The S30 abort-branch theorem is recovered structurally by
    swapping `if_pos hlt` ↦ `if_neg (Nat.not_lt.mpr hge)` in
    `hgcdMatrixSafeOf_compose_branch`'s proof; the two are
    structurally dual.

    These three lemmas do **not** prove the converse direction by
    themselves. The compose-branch's `apply` output is bounded
    by the outer matrix's behaviour on the *inner's* intermediate
    pair, not by the original `(a, b)`. Closing the converse
    requires showing
    `max (outerMat.apply (innerOut.1) (innerOut.2)).natAbs
        ≤ max innerOut.1.natAbs innerOut.2.natAbs`,
    which is the spec §5.2 non-expansion conjecture. -/

/-- **Cofactor multiplication composes the `apply` action.**

    For any two cofactor matrices `M, N` and integers `a, b`,
    `(M.mul N).apply a b = M.apply (N.apply a b).1 (N.apply a b).2`.

    Restated locally in `HGcdSafe` so PathA does not need to
    import `BinaryGcdOQ03OQ02.lean`. Identical to the canonical
    version at `BinaryGcdOQ03OQ02.lean:77` (which lives in the
    `HGcd` namespace).

    Proof: unfold both `CofactorMatrix.mul` and
    `CofactorMatrix.apply`; the two coordinates of the resulting
    pair match by `ring` since cofactor multiplication is exactly
    the row-by-column matrix product. -/
theorem cofactor_mul_apply (M N : CofactorMatrix) (a b : ℤ) :
    (M.mul N).apply a b =
      M.apply (N.apply a b).1 (N.apply a b).2 := by
  simp only [CofactorMatrix.mul, CofactorMatrix.apply, Prod.mk.injEq]
  refine ⟨?_, ?_⟩ <;> ring

/-- **Compose-branch matrix decomposition.**

    Above threshold (`hab`), if the inner-guard *compose* branch
    of `hgcdMatrixSafe (a + b + 1) a b` is taken — i.e., the
    natAbs pair `(u, v)` of `M_inner.apply (a, b)` satisfies
    `max u v < max a b` (`hlt`) — then `hgcdMatrixSafeOf a b`
    equals the **composed matrix**
    `(hgcdMatrixSafe (a + b) u v).mul M_inner`, where
    `M_inner := hgcdMatrixSafe (a + b) (a / 2 ^ s) (b / 2 ^ s)`
    is the inner recursion.

    Dual to the S30 `hgcdMatrixSafe_inner_abort_imp_outer_fails`
    `hMatrix` local lemma, which discharges the abort branch via
    `if_neg`. The same `dsimp only` + `if_*` pattern from S18's
    `hgcdMatrixSafe_det_unit` `let`-handling reduces the
    `hgcdMatrixSafe_succ` RHS to the inner if's then-branch.

    Proof structure mirrors S30: unfold `hgcdMatrixSafeOf`,
    rewrite `hgcdMatrixSafe_succ` and `if_neg hab` to pin the
    outer threshold dispatch to the recursive branch, `dsimp
    only` to beta-reduce the introduced `let` bindings, then
    `if_pos hlt` to commit to the inner-fires branch. -/
theorem hgcdMatrixSafeOf_compose_branch (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hlt :
      max
        ((hgcdMatrixSafe (a + b)
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe (a + b)
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs
        < max a b) :
    hgcdMatrixSafeOf a b
      = (hgcdMatrixSafe (a + b)
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).mul
        (hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)) := by
  unfold hgcdMatrixSafeOf
  rw [hgcdMatrixSafe_succ, if_neg hab]
  dsimp only
  rw [if_pos hlt]

/-- **Compose-branch `apply` decomposition.**

    Builds on `hgcdMatrixSafeOf_compose_branch` and
    `cofactor_mul_apply`: in the inner-fires branch, the column
    output `hgcdSafeApply a b` equals the outer matrix
    `hgcdMatrixSafe (a + b) u v` applied to the inner's column
    output `M_inner.apply (a, b)`.

    Significance for S31: this is the **forward bridge** for the
    compose ⇒ outer-fires direction. To conclude the outer guard
    fires (`schonhageOuterGuardFires a b = true`), we need
    `max .1.natAbs .2.natAbs < max a b` for `hgcdSafeApply a b`.
    The compose-branch hypothesis `hlt` is on the *inner's*
    column pair, not the outer composite's. The remaining gap —
    that the outer matrix's action on the inner's output does not
    expand `max` beyond `max u v` — is the non-expansion
    conjecture noted in the S31 spec §5.2. -/
theorem hgcdSafeApply_compose_branch (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hlt :
      max
        ((hgcdMatrixSafe (a + b)
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe (a + b)
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs
        < max a b) :
    hgcdSafeApply a b
      = (hgcdMatrixSafe (a + b)
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).apply
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2 := by
  unfold hgcdSafeApply
  rw [hgcdMatrixSafeOf_compose_branch a b hab hlt]
  exact cofactor_mul_apply _ _ _ _

-- ═══════════════════════════════════════════════════════════════
-- PART XXII: GENERAL NON-EXPANSION COUNTEREXAMPLE (Session 33)
-- ═══════════════════════════════════════════════════════════════

/-! ### Lean witness for S32's general non-expansion refutation

    `s32-non-expansion-analysis.md` (PR #17720, S32, markdown
    only) refuted the general non-expansion lemma cited as
    spec §5.2 sub-task (b) — the conjecture that for arbitrary
    unimodular `M, N : CofactorMatrix`,
    `max ((M.mul N).apply a b).natAbs ≤ max (N.apply a b).natAbs`.
    The refutation was algebraic (worked-out two-matrix table)
    but uncompiled.

    This section commits the counterexample to Lean. Take
    `M := ⟨2, 1, 1, 1⟩` (det = 2·1 − 1·1 = 1) and
    `N := CofactorMatrix.id` (det = 1, with `N.apply 1 0 = (1, 0)`
    so its `max.natAbs = 1`). Then `M.mul N = M = ⟨2, 1, 1, 1⟩`
    and `(M.mul N).apply 1 0 = (2, 1)` so its `max.natAbs = 2`.
    Hence `2 ≤ 1` fails, refuting the general non-expansion
    inequality.

    This closes the spec §5.2 sub-task (b) **first disjunct**
    (the general lemma) with a Lean-verified negative answer.
    Future S32b/S32c work toward closing the converse direction
    of the S28b equivalence must therefore route through the
    `hgcdMatrixSafe`-specific conditional form (§5 of the S32
    analysis), not the general unimodular form.

    Build: `decide` on tiny ℤ literals (no `native_decide`,
    no recursion). Adds 0 axioms, 0 sorries, 0 definitions. -/

/-- **Counterexample to the general non-expansion lemma.**

    There exist unimodular cofactor matrices `M, N` and a
    pair `(a, b) : ℤ × ℤ` such that
    `max ((M.mul N).apply a b).natAbs > max (N.apply a b).natAbs`.

    Witness: `M := ⟨2, 1, 1, 1⟩`, `N := CofactorMatrix.id`,
    `(a, b) := (1, 0)`. Then `M.det = N.det = 1` and
    `(M.mul N).apply 1 0 = (2, 1)` while `N.apply 1 0 = (1, 0)`,
    so `max 2 1 = 2 > 1 = max 1 0`.

    Refutes the general form of the spec §5.2 sub-task (b)
    non-expansion conjecture (cf. `s32-non-expansion-analysis.md`
    §1, PR #17720). -/
theorem cofactor_general_non_expansion_counterexample :
    let M : CofactorMatrix := ⟨2, 1, 1, 1⟩
    let N : CofactorMatrix := CofactorMatrix.id
    M.det = 1 ∧ N.det = 1 ∧
    ¬ (max ((M.mul N).apply 1 0).1.natAbs ((M.mul N).apply 1 0).2.natAbs
       ≤ max (N.apply 1 0).1.natAbs (N.apply 1 0).2.natAbs) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- Self-narrating decompositions of the counterexample (the two
    `apply` outputs whose `max.natAbs` values witness the gap). -/
example :
    let M : CofactorMatrix := ⟨2, 1, 1, 1⟩
    let N : CofactorMatrix := CofactorMatrix.id
    (M.mul N).apply 1 0 = (2, 1) := by decide

example : (CofactorMatrix.id.apply 1 0) = (1, 0) := by decide

-- ═══════════════════════════════════════════════════════════════
-- PART XXIII: ABORT-BRANCH DECOMPOSITION (Session 34, dual of PART XXI)
-- ═══════════════════════════════════════════════════════════════

/-! ### Abort-branch matrix / apply decomposition

    PART XXI (S31) exposed the compose-branch decomposition of
    `hgcdMatrixSafeOf` and `hgcdSafeApply` as standalone theorems:
    above threshold (`hab`) and inner-fires (`hlt : max u v < max a b`),
    `hgcdMatrixSafeOf a b = (hgcdMatrixSafe (a+b) u v).mul M_inner`
    and `hgcdSafeApply a b` is the outer matrix's `apply` action on
    the inner's column output.

    The complementary structural lemmas — the **abort-branch**
    forms used internally inside `hgcdMatrixSafe_inner_abort_imp_outer_fails`
    (PART XX, S30) as local `hMatrix` / `hApply` `have` blocks —
    were not previously exposed as top-level theorems. This section
    promotes them so any future iteration (S32b non-expansion,
    S32c the full S28b equivalence, etc.) can reference the abort
    decomposition directly rather than reproducing the
    `unfold + hgcdMatrixSafe_succ + if_neg + dsimp + if_neg` pattern.

    The proof code is exactly the body of S30's hMatrix/hApply
    local `have` blocks (`BinaryGcdOQ03OQ02PathA.lean` PART XX),
    with `if_pos hlt` replaced by `if_neg (Nat.not_lt.mpr hge)`.

    Together with PART XXI's compose-branch theorems, the abort
    and compose decompositions partition the above-threshold
    behaviour of `hgcdMatrixSafeOf`:

    * compose branch (PART XXI): `max u v < max a b` ⇒
      `hgcdMatrixSafeOf a b = (hgcdMatrixSafe (a+b) u v).mul M_inner`.
    * abort branch (PART XXIII, this section): `max a b ≤ max u v` ⇒
      `hgcdMatrixSafeOf a b = M_inner`.

    No new axioms or sorries; net +50 lines (2 theorems with
    docstrings). -/

/-- **Abort-branch matrix decomposition.**

    Above threshold (`hab`), if the inner-guard *aborts* — i.e.,
    the natAbs pair `(u, v)` of `M_inner.apply (a, b)` satisfies
    `max a b ≤ max u v` (`hge`, the negation of the size-reduction
    guard) — then `hgcdMatrixSafeOf a b` collapses to the inner
    recursion `M_inner := hgcdMatrixSafe (a + b) (a / 2^s) (b / 2^s)`
    itself, without the outer composition.

    Dual to PART XXI's `hgcdMatrixSafeOf_compose_branch`. Together
    the two theorems partition the above-threshold behaviour of
    `hgcdMatrixSafeOf` into the two possible cases of the inner
    size-reduction guard.

    This is the same matrix-level equation discharged by the
    `hMatrix` local `have` block in
    `hgcdMatrixSafe_inner_abort_imp_outer_fails` (PART XX, S30).
    Exposing it as a top-level theorem makes the abort-branch
    reduction reusable without re-deriving the
    `unfold + hgcdMatrixSafe_succ + if_neg + dsimp + if_neg`
    pattern at every use site. -/
theorem hgcdMatrixSafeOf_abort_branch (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hge :
      max a b ≤
        max
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs) :
    hgcdMatrixSafeOf a b
      = hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b) := by
  unfold hgcdMatrixSafeOf
  rw [hgcdMatrixSafe_succ, if_neg hab]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr hge)]

/-- **Abort-branch `apply` decomposition.**

    Builds on `hgcdMatrixSafeOf_abort_branch`: in the inner-abort
    branch, the column output `hgcdSafeApply a b` equals
    `M_inner.apply (a, b)` directly, without the outer composition.

    Dual to PART XXI's `hgcdSafeApply_compose_branch`. Same
    `apply`-level equation derived inside the `hApply` local
    `have` block of S30's
    `hgcdMatrixSafe_inner_abort_imp_outer_fails` (PART XX).
    The hypothesis `hge` is exactly the inner-abort hypothesis
    used by S30's S28c packaging step.

    Significance for S32b/c: pairs with
    `hgcdSafeApply_compose_branch` to give a complete
    case-distinction API on the inner guard, so the converse
    direction of the S28b equivalence can be stated as a clean
    `iff` rather than two separate forward arguments. -/
theorem hgcdSafeApply_abort_branch (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hge :
      max a b ≤
        max
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs) :
    hgcdSafeApply a b
      = (hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ) := by
  unfold hgcdSafeApply
  rw [hgcdMatrixSafeOf_abort_branch a b hab hge]

-- ═══════════════════════════════════════════════════════════════
-- PART XXIV: OUTER-FIRES ⇒ INNER-FIRES (Session 36, → direction of S32c)
-- ═══════════════════════════════════════════════════════════════

/-! ### Outer-guard fires ⇒ inner-guard fires (above threshold)

    Direct contrapositive packaging of S30's
    `hgcdMatrixSafe_inner_abort_imp_outer_fails` (PART XX):

    * S30 (`inner-aborts ⇒ outer-fails`): above threshold, if the
      inner-guard abort branch is taken (`max a b ≤ max u v`),
      then `schonhageOuterGuardFires a b = false`.
    * Contrapositive (`outer-fires ⇒ inner-fires`, this section):
      above threshold, if `schonhageOuterGuardFires a b = true`,
      then the inner-guard fires (`max u v < max a b`).

    This is the **`→` direction of the S28b equivalence**
    `schonhageOuterGuardFires_above_iff_inner_fires` referenced
    in `s32-non-expansion-analysis.md` §6 / state.md's S32c
    next-action item. The harder converse direction
    (`← inner-fires ⇒ outer-fires`) is the non-expansion-bearing
    half (= S32b deliverable, deferred per state.md), so we
    package the easy direction separately rather than waiting for
    both halves.

    Significance. With this packaging, the iff form's `→`
    direction can be cited as a single named theorem, without
    re-deriving the contrapositive at each use site. Combined
    with the S31 `_compose_branch` and S34 `_abort_branch`
    decompositions, this completes the **outer-fires case** of
    the case-analysis API: above threshold + outer-fires forces
    the inner-fires hypothesis, which in turn lets one apply
    `hgcdSafeApply_compose_branch` to unfold `hgcdSafeApply a b`
    as the outer matrix's action on the inner column output.

    Build: pure forward reasoning from S30 by `by_contra` +
    `push_neg`; no `native_decide`, no recursion. -/

/-- **Outer-guard fires ⇒ inner-guard fires** (above threshold).

    Above threshold (`hab`), if the outer guard
    `schonhageOuterGuardFires a b` returns `true`, then the inner
    guard must have fired — i.e., the natAbs-pair `(u, v)` of
    `M_inner.apply (a, b)` (where `M_inner := hgcdMatrixSafe
    (a + b) (a / 2^s) (b / 2^s)`) satisfies `max u v < max a b`.

    Direct contrapositive of S30's
    `hgcdMatrixSafe_inner_abort_imp_outer_fails`: if instead
    `max a b ≤ max u v` (inner-aborts hypothesis), S30 forces
    `outerGuardFires = false`, contradicting `hfires`. -/
theorem schonhageOuterGuardFires_above_imp_inner_fires {a b : ℕ}
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    max
      ((hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
      ((hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs
      < max a b := by
  by_contra hge
  push_neg at hge
  have hfails :=
    hgcdMatrixSafe_inner_abort_imp_outer_fails a b hab hge
  rw [hfails] at hfires
  exact Bool.noConfusion hfires

-- ═══════════════════════════════════════════════════════════════
-- PART XXV: OUTER-FIRES PACKAGING (Session 37)
-- ═══════════════════════════════════════════════════════════════

/-! ### Outer-fires decomposition (matrix + apply)

    PART XXIV (S36) proved the `→` direction of the S28b
    equivalence: above threshold + outer-fires ⇒ inner-fires.
    PART XXI (S31) proved the compose-branch decomposition: above
    threshold + inner-fires ⇒ `hgcdMatrixSafeOf` factors as
    `M_outer.mul M_inner` and `hgcdSafeApply` is the outer
    matrix's `apply` on the inner column output.

    This section composes the two into single named theorems that
    bypass the manual inner-fires step at use sites. Above
    threshold + outer-fires now directly yields the
    matrix and apply level compose decomposition.

    Significance. Together with PART XXIII's
    `hgcdMatrixSafeOf_abort_branch` / `hgcdSafeApply_abort_branch`
    (which discharge the inner-aborts case as an outer-fails
    corollary by S30), this completes the case-analysis API on the
    outer guard: any reasoning that case-splits on
    `schonhageOuterGuardFires a b` can now dispatch the
    `true`-branch directly to the compose decomposition without
    re-deriving the inner-fires hypothesis at each call site.

    Build: pure forward composition (apply S36, then S31). No new
    axioms, no new sorries, no native_decide, no recursion. -/

/-- **Outer-fires matrix decomposition.**

    Above threshold (`hab`), if the outer guard
    `schonhageOuterGuardFires a b` fires (`hfires`), then
    `hgcdMatrixSafeOf a b` factors as the composed matrix
    `(hgcdMatrixSafe (a + b) u v).mul M_inner`, where
    `M_inner := hgcdMatrixSafe (a + b) (a / 2^s) (b / 2^s)` is the
    inner recursion and `(u, v)` is the natAbs of the inner's
    column output `M_inner.apply (a, b)`.

    Composes S36's `schonhageOuterGuardFires_above_imp_inner_fires`
    (PART XXIV) with S31's `hgcdMatrixSafeOf_compose_branch`
    (PART XXI). Removes the manual inner-fires step from any use
    site that already has the outer-fires hypothesis on hand. -/
theorem hgcdMatrixSafeOf_of_outerFires {a b : ℕ}
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    hgcdMatrixSafeOf a b
      = (hgcdMatrixSafe (a + b)
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).mul
        (hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)) :=
  hgcdMatrixSafeOf_compose_branch a b hab
    (schonhageOuterGuardFires_above_imp_inner_fires hab hfires)

/-- **Outer-fires `apply` decomposition.**

    Above threshold (`hab`), if the outer guard
    `schonhageOuterGuardFires a b` fires (`hfires`), then
    `hgcdSafeApply a b` equals the outer matrix
    `hgcdMatrixSafe (a + b) u v` applied to the inner's column
    output `M_inner.apply (a, b)` (as integers; `(u, v)` is the
    natAbs of that pair).

    Composes S36's `schonhageOuterGuardFires_above_imp_inner_fires`
    (PART XXIV) with S31's `hgcdSafeApply_compose_branch`
    (PART XXI). The outer-fires hypothesis carries enough
    information to fully unfold the column output without re-
    deriving inner-fires. -/
theorem hgcdSafeApply_of_outerFires {a b : ℕ}
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    hgcdSafeApply a b
      = (hgcdMatrixSafe (a + b)
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).apply
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2 :=
  hgcdSafeApply_compose_branch a b hab
    (schonhageOuterGuardFires_above_imp_inner_fires hab hfires)

-- ═══════════════════════════════════════════════════════════════
-- PART XXVI: SCHÖNHAGE STEP IN COMPOSE COORDINATES (Session 38)
-- ═══════════════════════════════════════════════════════════════

/-! ### One Schönhage fuel step expressed in `M_outer · M_inner` coordinates

    PART XXV (S37) packaged the outer-fires case at the matrix and
    `apply` levels: above threshold + outer-fires implies
    `hgcdSafeApply a b = M_outer.apply (M_inner.apply (a, b))`, where
    `M_inner := hgcdMatrixSafe (a + b) (a / 2^s) (b / 2^s)` and
    `M_outer := hgcdMatrixSafe (a + b) u v` with
    `(u, v) := (M_inner.apply (a, b)).natAbs`.

    This section composes that `apply`-level equation with two
    `schonhageGcd`-step facts already available on
    `origin/main` to obtain the **compose-coordinate forms** that
    downstream inductive arguments about `schonhageGcd` actually
    consume:

    * `compose_apply_natAbs_strict_decrease_of_outerFires` — the
      per-step strict size-reduction bound on the **composed**
      column output `M_outer.apply (M_inner.apply (a, b))`.
      Composes `schonhageOuterGuardFires_strict_decrease`
      (PART XIII, S23) with `hgcdSafeApply_of_outerFires`
      (PART XXV, S37): rewriting the `_strict_decrease` bound
      via S37 exposes the same strict inequality on the
      compose-coordinate column output, removing the intermediate
      `hgcdSafeApply` abstraction.

    * `schonhageGcd_succ_recurse_via_compose` — one fuel step
      of `schonhageGcd` expressed as a recursion on the
      compose-coordinate natAbs pair. Composes
      `schonhageGcd_succ_recurse_of_fires` (PART XIII, S23) with
      `hgcdSafeApply_of_outerFires` (PART XXV, S37): rewriting the
      `schonhageGcd` recursion equation via S37 exposes the
      `M_outer.apply (M_inner.apply (a, b))` natAbs pair as the
      recursion target.

    Significance. Together with PART XXV, this completes the
    outer-fires-branch case-analysis API in **two coordinate
    systems**: the high-level `hgcdSafeApply` form (PART XIII +
    PART XXV) and the structural `M_outer.apply (M_inner.apply
    (a, b))` form (this section). Future iterations that need to
    reason about the **two-level matrix recursion** behind the
    fuel step — for example, the conditional non-expansion
    analysis sketched in `s32-non-expansion-analysis.md` §5 — can
    cite the compose-coordinate forms directly rather than
    re-deriving the `hgcdSafeApply` ↔ `M_outer.apply (M_inner.apply
    (a, b))` rewrite at each use site.

    Build: pure forward rewrites against already-proved S22 / S23 /
    S37 lemmas. No `native_decide`, no recursion, no new axioms,
    no new sorries, no new definitions. -/

/-- **Strict size-reduction on the compose-coordinate column output.**

    Above threshold (`hab`) and outer-fires (`hfires`), the
    composed column output `M_outer.apply (M_inner.apply (a, b))`
    has natAbs pair strictly smaller (in `max`) than `(a, b)`:

    ```
    max ((M_outer.apply (M_inner.apply (a, b))).1.natAbs)
        ((M_outer.apply (M_inner.apply (a, b))).2.natAbs)
      < max a b
    ```

    where
    `M_inner := hgcdMatrixSafe (a + b) (a / 2^s) (b / 2^s)` and
    `M_outer := hgcdMatrixSafe (a + b) u v` with
    `(u, v) := (M_inner.apply (a, b)).natAbs` (per the S37
    decomposition).

    Direct rewrite of S23's
    `schonhageOuterGuardFires_strict_decrease` via S37's
    `hgcdSafeApply_of_outerFires`: the underlying inequality is
    already proved on `hgcdSafeApply a b`; rewriting via the
    compose decomposition substitutes the explicit compose form on
    both sides of the `< max a b` bound.

    Significance. The S23 strict-decrease lemma is phrased on the
    abstracted column output `hgcdSafeApply a b`; this corollary
    re-expresses the bound on the **structurally explicit**
    `M_outer.apply (M_inner.apply (a, b))` form, exposing the
    per-step decrease as a property of the two-level matrix
    recursion. This is the natural input for any future analysis
    of compose-coordinate non-expansion (`s32-non-expansion-
    analysis.md` §5–§6). -/
theorem compose_apply_natAbs_strict_decrease_of_outerFires {a b : ℕ}
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    max
      ((hgcdMatrixSafe (a + b)
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).apply
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2).1.natAbs
      ((hgcdMatrixSafe (a + b)
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).apply
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2).2.natAbs
      < max a b := by
  rw [← hgcdSafeApply_of_outerFires hab hfires]
  exact schonhageOuterGuardFires_strict_decrease hfires

/-- **One `schonhageGcd` fuel step expressed in compose coordinates.**

    Above threshold (`hab`) and outer-fires (`hfires`), one fuel
    step of `schonhageGcd` recurses on the natAbs pair of the
    composed column output `M_outer.apply (M_inner.apply (a, b))`:

    ```
    schonhageGcd (f + 1) a b
      = schonhageGcd f
          ((M_outer.apply (M_inner.apply (a, b))).1.natAbs)
          ((M_outer.apply (M_inner.apply (a, b))).2.natAbs)
    ```

    where M_inner and M_outer are as in S37 / PART XXV.

    Direct rewrite of S23's `schonhageGcd_succ_recurse_of_fires`
    via S37's `hgcdSafeApply_of_outerFires`: S23 phrases the
    recursion target on `hgcdSafeApply a b`; the rewrite
    substitutes the compose-coordinate form so the recursion
    target is explicit in the two-level matrix coordinates. -/
theorem schonhageGcd_succ_recurse_via_compose (f a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    schonhageGcd (f + 1) a b =
      schonhageGcd f
        ((hgcdMatrixSafe (a + b)
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).apply
              ((hgcdMatrixSafe (a + b)
                  (a / 2 ^ hgcdShiftSafe a b)
                  (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1
              ((hgcdMatrixSafe (a + b)
                  (a / 2 ^ hgcdShiftSafe a b)
                  (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2).1.natAbs
        ((hgcdMatrixSafe (a + b)
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
            ((hgcdMatrixSafe (a + b)
                (a / 2 ^ hgcdShiftSafe a b)
                (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).apply
              ((hgcdMatrixSafe (a + b)
                  (a / 2 ^ hgcdShiftSafe a b)
                  (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1
              ((hgcdMatrixSafe (a + b)
                  (a / 2 ^ hgcdShiftSafe a b)
                  (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2).2.natAbs := by
  rw [schonhageGcd_succ_recurse_of_fires f a b hfires,
      hgcdSafeApply_of_outerFires hab hfires]

-- ═══════════════════════════════════════════════════════════════
-- PART XXVII: FUEL-ZERO NON-EXPANSION BASE CASE (Session 39)
-- ═══════════════════════════════════════════════════════════════

/-! ### Fuel-zero base case for the NE-self / NE-cond induction

    `s32-non-expansion-analysis.md` §3–§5 sketches an inductive
    proof of the conditional non-expansion property (NE-cond)
    for `hgcdMatrixSafe`. The induction is on the fuel parameter
    `f`. This section establishes the **fuel-zero base case**:
    at `f = 0`, `hgcdMatrixSafe 0 a b` is the identity matrix
    `CofactorMatrix.id`, so applying it to `(a : ℤ, b : ℤ)`
    yields the pair `(a : ℤ, b : ℤ)` unchanged. Hence the natAbs
    pair of the output equals `(a, b)` and the natAbs max equals
    `max a b` (with EQUALITY, not just `≤`).

    Four lemmas are exposed:

    * `cofactor_id_apply` — `CofactorMatrix.id.apply a b = (a, b)`
      for any integer pair. Trivial unfold; used as a building
      block by the other three and reusable at any call site
      that needs the identity-matrix evaluation in closed form.

    * `hgcdMatrixSafe_zero_apply` — the apply form at fuel 0,
      composing `hgcdMatrixSafe_zero` with `cofactor_id_apply`.

    * `hgcdMatrixSafe_zero_natAbs_max_eq` — the natAbs-max
      equality at fuel 0. The natAbs of a natural-number cast
      to ℤ collapses to the original natural via
      `Int.natAbs_natCast`, so the max of the two natAbs
      components equals `max a b` exactly.

    * `hgcdMatrixSafe_zero_natAbs_max_le` — the `≤` corollary,
      packaged in the form that successor inductive proofs of
      NE-self typically expect (`max .natAbs ≤ max a b` rather
      than equality).

    **What this does NOT prove.** The inductive step
    (fuel `f → f + 1`) is the open S32b problem
    (`s32-non-expansion-analysis.md` §6). Specifically:

    * Below threshold (`max a b < 64`),
      `hgcdMatrixSafe (f + 1) a b` reduces to a
      `lehmerCofactors`-derived matrix; bounding its apply
      natAbs requires reasoning through the Euclidean step
      machine (`lehmerInnerStep`).
    * Above threshold, the inner-guard branch determines
      which sub-recursion to take, and the inner-abort branch
      can produce `hgcdSafeApply a b` outputs whose natAbs
      max EXCEEDS `max a b` — exactly the S28a
      `(130, 89)` / `(107, 85)` phenomenon (PART XIV). This is
      why NE-self in its full unconditional form is FALSE
      (spec §4) and the spec proposes the weaker NE-cond
      conditional form (spec §5).

    Significance / honesty. Per the file convention
    `hgcdMatrixSafeOf a b := hgcdMatrixSafe (a + b + 1) a b`,
    the fuel-zero case is NEVER reached by the top-level entry
    point — `hgcdMatrixSafeOf` always supplies fuel `≥ 1`. The
    fuel-zero lemmas here are therefore not load-bearing for
    any current top-level theorem; they are PURELY the
    structural base case of any future inductive proof of
    NE-self / NE-cond. Packaging them cleanly here removes one
    boilerplate step from successor iterations targeting S32b /
    S32c.

    Build: pure unfolds and `Int.natAbs_natCast`. No
    `native_decide`, no recursion, no new axioms, no new
    sorries, no new definitions. -/

/-- **Identity-matrix `apply` is the identity function.**

    `CofactorMatrix.id = ⟨1, 0, 0, 1⟩` (from
    `BinaryGcdOQ03.lean:48`) so applying it to `(a, b)` yields
    `(1·a + 0·b, 0·a + 1·b) = (a, b)`. Proof is `simp` on the
    unfolds of `CofactorMatrix.id` and `CofactorMatrix.apply`.

    This is a general-purpose helper: any reasoning that
    encounters `CofactorMatrix.id.apply` (e.g. the fuel-zero
    case of `hgcdMatrixSafe`, or the `(M.mul id)` and
    `(id.mul N)` corollaries of `cofactor_mul_apply` at PART
    XXI) can rewrite via this lemma to expose the identity-
    function form directly. -/
theorem cofactor_id_apply (a b : ℤ) :
    CofactorMatrix.id.apply a b = (a, b) := by
  simp [CofactorMatrix.id, CofactorMatrix.apply]

/-- **Fuel-zero `apply` equation.**

    At fuel `0`, `hgcdMatrixSafe` returns the identity matrix
    (`hgcdMatrixSafe_zero`, PART II line 146), so its `apply`
    action on `(a : ℤ, b : ℤ)` returns `((a : ℤ), (b : ℤ))`
    unchanged. Direct composition of `hgcdMatrixSafe_zero`
    with `cofactor_id_apply`. -/
theorem hgcdMatrixSafe_zero_apply (a b : ℕ) :
    (hgcdMatrixSafe 0 a b).apply (a : ℤ) (b : ℤ) = ((a : ℤ), (b : ℤ)) := by
  rw [hgcdMatrixSafe_zero]
  exact cofactor_id_apply (a : ℤ) (b : ℤ)

/-- **Fuel-zero natAbs-max equality.**

    At fuel `0`, the natAbs max of the apply output equals
    `max a b` exactly. (Equality, not just `≤` — the apply is
    the identity function on the input pair, and the natAbs of
    a natural-number cast to ℤ is the original natural by
    `Int.natAbs_natCast`.)

    This is the NE-self base case in its strongest form
    (equality), suitable as the `induction.zero` step for any
    successor proof of NE-self / NE-cond by induction on fuel. -/
theorem hgcdMatrixSafe_zero_natAbs_max_eq (a b : ℕ) :
    max ((hgcdMatrixSafe 0 a b).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe 0 a b).apply (a : ℤ) (b : ℤ)).2.natAbs
      = max a b := by
  rw [hgcdMatrixSafe_zero_apply]
  simp [Int.natAbs_natCast]

/-- **Fuel-zero non-expansion (`≤` corollary).**

    The `≤` form of `hgcdMatrixSafe_zero_natAbs_max_eq`,
    packaged separately so callers needing the inequality
    directly do not have to rewrite through equality. This is
    the literal NE-self statement at fuel `0`.

    Trivially equivalent to the equality form; exposed
    separately because the NE-self / NE-cond induction
    framework (`s32-non-expansion-analysis.md` §3–§5) phrases
    its goal as `≤`, not equality. -/
theorem hgcdMatrixSafe_zero_natAbs_max_le (a b : ℕ) :
    max ((hgcdMatrixSafe 0 a b).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe 0 a b).apply (a : ℤ) (b : ℤ)).2.natAbs
      ≤ max a b :=
  (hgcdMatrixSafe_zero_natAbs_max_eq a b).le

-- ═══════════════════════════════════════════════════════════════
-- PART XXVIII: MUL-IDENTITY APPLY COROLLARIES (Session 40)
-- ═══════════════════════════════════════════════════════════════

/-! ### Mul-identity corollaries of `cofactor_mul_apply`

    S39's `cofactor_id_apply` docstring (line 2366–2369) flagged
    `(M.mul id)` and `(id.mul N)` apply corollaries as natural
    follow-ups: any reasoning that produces a composed cofactor
    matrix with `CofactorMatrix.id` on one side can collapse the
    spurious identity factor via `cofactor_mul_apply` +
    `cofactor_id_apply`.

    Two named theorems are exposed here:

    * `cofactor_mul_id_apply` — `(M.mul CofactorMatrix.id).apply
      a b = M.apply a b`. Right-identity form. Proof: rewrite via
      `cofactor_mul_apply` (PART XX) to expose
      `M.apply (CofactorMatrix.id.apply a b).1 (CofactorMatrix.id.apply a b).2`,
      then rewrite via `cofactor_id_apply` (PART XXVII) to
      collapse the inner `.apply` to the pair `(a, b)`. The
      remaining projection reduction is definitional.

    * `cofactor_id_mul_apply` — `(CofactorMatrix.id.mul N).apply
      a b = N.apply a b`. Left-identity form. Same `rw` chain;
      after the rewrites, the goal reduces by `Prod` structure
      eta (`((N.apply a b).1, (N.apply a b).2) = N.apply a b`).

    **Why useful.** The fuel-zero unfoldings introduced in PART
    XXVII (S39) produce `CofactorMatrix.id`-factors via
    `hgcdMatrixSafe_zero`. When such an `id` factor appears
    multiplied with another cofactor matrix — e.g. inside a
    fuel-step unfolding where one of the recursive calls hits
    the `f = 0` base case — these corollaries let downstream
    sessions collapse the spurious factor in one line, instead
    of unfolding `CofactorMatrix.mul` + `CofactorMatrix.apply`
    every time.

    No new axioms, no new sorries, no new definitions, no
    `native_decide`. Both proofs are single-line `rw` chains
    against already-merged S20/S39 lemmas. -/

/-- **Right `CofactorMatrix.id` collapse for `cofactor_mul_apply`.**

    `(M.mul CofactorMatrix.id).apply a b = M.apply a b`. Proof:
    `cofactor_mul_apply` (PART XX) rewrites the LHS to
    `M.apply (CofactorMatrix.id.apply a b).1 (CofactorMatrix.id.apply a b).2`;
    `cofactor_id_apply` (PART XXVII) rewrites the inner
    `CofactorMatrix.id.apply a b` to the pair `(a, b)`; the
    surrounding `Prod` projections then reduce definitionally
    to give `M.apply a b`. -/
theorem cofactor_mul_id_apply (M : CofactorMatrix) (a b : ℤ) :
    (M.mul CofactorMatrix.id).apply a b = M.apply a b := by
  rw [cofactor_mul_apply, cofactor_id_apply]

/-- **Left `CofactorMatrix.id` collapse for `cofactor_mul_apply`.**

    `(CofactorMatrix.id.mul N).apply a b = N.apply a b`. Proof:
    `cofactor_mul_apply` (PART XX) rewrites the LHS to
    `CofactorMatrix.id.apply (N.apply a b).1 (N.apply a b).2`;
    `cofactor_id_apply` (PART XXVII) rewrites this to the pair
    `((N.apply a b).1, (N.apply a b).2)`; Lean 4's structure
    eta for `Prod` makes this definitionally equal to
    `N.apply a b`. -/
theorem cofactor_id_mul_apply (N : CofactorMatrix) (a b : ℤ) :
    (CofactorMatrix.id.mul N).apply a b = N.apply a b := by
  rw [cofactor_mul_apply, cofactor_id_apply]

-- ═══════════════════════════════════════════════════════════════
-- PART XXIX: FUEL-ONE ABOVE-THRESHOLD COLLAPSE (Session 41)
-- ═══════════════════════════════════════════════════════════════

/-! ### Fuel-one above-threshold collapse for `hgcdMatrixSafe`

    PART XXVII (S39) established the fuel-zero base case
    (`hgcdMatrixSafe 0 a b = CofactorMatrix.id`, plus `apply` and
    natAbs-max forms). PART XXVIII (S40) added
    `cofactor_mul_id_apply` and `cofactor_id_mul_apply` for
    collapsing spurious identity factors produced by
    `cofactor_mul_apply` rewriting.

    This PART chains both into a clean fuel-one above-threshold
    collapse: at `f = 1` with `max a b ≥ hgcdThresholdSafe`
    (the recursive case of `hgcdMatrixSafe_succ`), the recursion
    bottoms out immediately:

    1. `M_inner := hgcdMatrixSafe 0 (a / 2^s) (b / 2^s) =
       CofactorMatrix.id` (by `hgcdMatrixSafe_zero`).
    2. `(M_inner.apply ↑a ↑b) = (↑a, ↑b)` (by S39
       `cofactor_id_apply`).
    3. `(u, v) := ((↑a, ↑b).1.natAbs, (↑a, ↑b).2.natAbs) =
       (a, b)` (by `Int.natAbs_natCast`).
    4. The inner size-reduction guard `max u v < max a b`
       becomes `max a b < max a b`, which is FALSE by
       `lt_irrefl`.
    5. The abort branch fires, returning `M_inner =
       CofactorMatrix.id`.

    Hence `hgcdMatrixSafe 1 a b = CofactorMatrix.id` whenever
    `max a b ≥ hgcdThresholdSafe`.

    Four named theorems are exposed:

    * `hgcdMatrixSafe_one_above_threshold` — the matrix-level
      collapse: `hgcdMatrixSafe 1 a b = CofactorMatrix.id` for
      `max a b ≥ hgcdThresholdSafe`. Direct combination of
      `hgcdMatrixSafe_succ`, `if_neg hab`, `hgcdMatrixSafe_zero`,
      `cofactor_id_apply`, `Int.natAbs_natCast`, and
      `lt_irrefl`.

    * `hgcdMatrixSafe_one_above_threshold_apply` — apply form,
      `(hgcdMatrixSafe 1 a b).apply ↑a ↑b = (↑a, ↑b)`. Direct
      composition of the matrix collapse with
      `cofactor_id_apply`.

    * `hgcdMatrixSafe_one_above_threshold_natAbs_max_eq` —
      natAbs-max equality, the strongest non-expansion statement
      at fuel `1` above threshold (equality, not just `≤`).
      Matches the strength of the S39 fuel-zero analogue.

    * `hgcdMatrixSafe_one_above_threshold_natAbs_max_le` — `≤`
      corollary, the NE-cond form at fuel `1` above threshold.
      Provided in the same packaging convention as PART XXVII's
      `hgcdMatrixSafe_zero_natAbs_max_le`.

    **What this does NOT prove.** Fuel-one BELOW threshold
    (`max a b < hgcdThresholdSafe`) reduces via
    `hgcdMatrixSafe_small` (PART V) to
    `lehmerCofactors hgcdThresholdSafe a b CofactorMatrix.id`;
    that case is handled by the parent file's
    `lehmerCofactors_id_apply_le` (PART V.5) machinery in
    `BinaryGcdOQ03OQ02.lean`. Fuel ≥ 2 above threshold remains
    the open S32b inductive step
    (`s32-non-expansion-analysis.md` §6).

    **Why useful.** This is the smallest non-trivial fuel level
    at which the above-threshold abort branch fires. Together
    with the fuel-zero base case (PART XXVII), it provides
    closed-form evaluation of `hgcdMatrixSafe` on every input
    `(a, b)` for which the recursion bottoms out within one
    above-threshold step. As a side benefit, the apply form
    `(hgcdMatrixSafe 1 a b).apply ↑a ↑b = (↑a, ↑b)` is the
    fuel-1 analogue of `hgcdMatrixSafe_zero_apply` and slots
    into the same induction template the S32b proof program
    expects for the f → f + 1 step.

    Build: pure unfolds + `cofactor_id_apply` +
    `Int.natAbs_natCast` + `lt_irrefl`. No `native_decide`, no
    recursion, no new axioms, no new sorries, no new
    definitions. -/

/-- **Fuel-one above-threshold matrix collapse.**

    At fuel `1` with `max a b ≥ hgcdThresholdSafe` (i.e.
    `¬ max a b < hgcdThresholdSafe`), `hgcdMatrixSafe 1 a b`
    enters the recursive branch, the inner recursion bottoms
    out at fuel `0` (giving `CofactorMatrix.id`), the inner
    guard fails (`max a b < max a b` is false), and the abort
    branch returns `M_inner = CofactorMatrix.id`.

    Proof: unfold via `hgcdMatrixSafe_succ` + `if_neg hab`,
    reduce the inner `hgcdMatrixSafe 0` via
    `hgcdMatrixSafe_zero`, reduce the `id.apply ↑a ↑b` via
    `cofactor_id_apply`, collapse `natAbs ∘ Nat.cast` via
    `Int.natAbs_natCast`, then `if_neg (lt_irrefl _)` discharges
    the inner guard. -/
theorem hgcdMatrixSafe_one_above_threshold (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe) :
    hgcdMatrixSafe 1 a b = CofactorMatrix.id := by
  show hgcdMatrixSafe (0 + 1) a b = CofactorMatrix.id
  rw [hgcdMatrixSafe_succ, if_neg hab]
  dsimp only
  simp only [hgcdMatrixSafe_zero, cofactor_id_apply]
  simp [Int.natAbs_natCast]

/-- **Fuel-one above-threshold `apply` equation.**

    At fuel `1` with `max a b ≥ hgcdThresholdSafe`,
    `hgcdMatrixSafe 1 a b` collapses to `CofactorMatrix.id`
    (`hgcdMatrixSafe_one_above_threshold`), so its `apply`
    action on `(a : ℤ, b : ℤ)` returns `((a : ℤ), (b : ℤ))`
    unchanged. Direct composition of
    `hgcdMatrixSafe_one_above_threshold` with
    `cofactor_id_apply`. -/
theorem hgcdMatrixSafe_one_above_threshold_apply (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe) :
    (hgcdMatrixSafe 1 a b).apply (a : ℤ) (b : ℤ) = ((a : ℤ), (b : ℤ)) := by
  rw [hgcdMatrixSafe_one_above_threshold a b hab]
  exact cofactor_id_apply (a : ℤ) (b : ℤ)

/-- **Fuel-one above-threshold natAbs-max equality.**

    At fuel `1` above threshold, the natAbs max of the apply
    output equals `max a b` exactly. (Equality, not just `≤` —
    the apply collapses to the identity function on the input
    pair, and the natAbs of a natural-number cast to ℤ is the
    original natural by `Int.natAbs_natCast`.)

    This is the NE-self statement in its strongest form at
    fuel `1` above threshold, suitable as the `induction.succ`
    step at `f = 0` for any successor proof of NE-self / NE-cond
    by induction on fuel. -/
theorem hgcdMatrixSafe_one_above_threshold_natAbs_max_eq (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe) :
    max ((hgcdMatrixSafe 1 a b).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe 1 a b).apply (a : ℤ) (b : ℤ)).2.natAbs
      = max a b := by
  rw [hgcdMatrixSafe_one_above_threshold_apply a b hab]
  simp [Int.natAbs_natCast]

/-- **Fuel-one above-threshold non-expansion (`≤` corollary).**

    The `≤` form of
    `hgcdMatrixSafe_one_above_threshold_natAbs_max_eq`,
    packaged separately so callers needing the inequality
    directly do not have to rewrite through equality. This is
    the literal NE-self statement at fuel `1` above threshold.

    Trivially equivalent to the equality form; exposed
    separately because the NE-self / NE-cond induction
    framework (`s32-non-expansion-analysis.md` §3–§5) phrases
    its goal as `≤`, not equality. -/
theorem hgcdMatrixSafe_one_above_threshold_natAbs_max_le (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe) :
    max ((hgcdMatrixSafe 1 a b).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe 1 a b).apply (a : ℤ) (b : ℤ)).2.natAbs
      ≤ max a b :=
  (hgcdMatrixSafe_one_above_threshold_natAbs_max_eq a b hab).le

-- ═══════════════════════════════════════════════════════════════
-- PART XXX: FUEL-GENERIC COMPOSE/ABORT BRANCHES (Session 42)
-- ═══════════════════════════════════════════════════════════════

/-! ### Fuel-generic compose-branch and abort-branch decompositions

    PART XXI (S31, PR #17683) introduced `hgcdMatrixSafeOf_compose_branch`
    and `hgcdSafeApply_compose_branch`, and PART XXIII (S34, PR #17771)
    introduced the dual `hgcdMatrixSafeOf_abort_branch` and
    `hgcdSafeApply_abort_branch`. Both pairs are stated at the
    **specific fuel `a + b`** (since `hgcdMatrixSafeOf a b =
    hgcdMatrixSafe (a + b + 1) a b`).

    This PART exposes the **fuel-generic** versions:
    `hgcdMatrixSafe (f + 1) a b = …` and
    `(hgcdMatrixSafe (f + 1) a b).apply (↑a) (↑b) = …` for an
    **arbitrary** fuel parameter `f : ℕ`. The proofs are
    structurally identical to the `_Of` variants — they just drop
    the `unfold hgcdMatrixSafeOf` step (since the inner-fuel is now
    abstract rather than `a + b`).

    **Why useful.** The fuel-zero base case (PART XXVII, S39) and
    fuel-one above-threshold collapse (PART XXIX, S41) discharge
    the recursion at fuel `0` and fuel `1`. Any inductive proof of
    non-expansion at fuel `f + 1` (the open NE-cond / NE-self
    program of `s32-non-expansion-analysis.md` §3–§6) needs to
    unfold the recursion at the **abstract successor fuel** `f + 1`,
    not just at `(a + b) + 1`. The existing `_Of` variants pin the
    fuel, so they cannot serve as the induction.succ template
    directly; this PART supplies the missing fuel-generic forms.

    The `_Of` variants in PART XXI / PART XXIII are recovered as
    corollaries at `f := a + b` (their stated form). They are kept
    intact to avoid downstream churn; the new generic theorems
    sit alongside them.

    **Four named theorems** (all conditioned on `hab : ¬ max a b <
    hgcdThresholdSafe`, the above-threshold dispatch):

    * `hgcdMatrixSafe_compose_branch (f a b : ℕ)` — matrix-level
      compose: `hgcdMatrixSafe (f + 1) a b =
        (hgcdMatrixSafe f u v).mul M_inner`, where
      `M_inner := hgcdMatrixSafe f (a / 2 ^ s) (b / 2 ^ s)` and
      `(u, v) := natAbs of M_inner.apply (↑a, ↑b)`.

    * `hgcdMatrixSafe_apply_compose_branch (f a b : ℕ)` — apply
      form: `(hgcdMatrixSafe (f + 1) a b).apply (↑a) (↑b) =
        (hgcdMatrixSafe f u v).apply M_inner.apply.1 M_inner.apply.2`.
      Composes the matrix-level compose with `cofactor_mul_apply`.

    * `hgcdMatrixSafe_abort_branch (f a b : ℕ)` — matrix-level
      abort: `hgcdMatrixSafe (f + 1) a b = M_inner` (the inner
      recursion is passed through, no outer composition).

    * `hgcdMatrixSafe_apply_abort_branch (f a b : ℕ)` — apply
      form: `(hgcdMatrixSafe (f + 1) a b).apply (↑a) (↑b) =
        M_inner.apply (↑a) (↑b)`. Direct corollary of the
      matrix-level abort.

    Build: pure `rw [hgcdMatrixSafe_succ, if_neg hab]` + `dsimp
    only` + `if_pos`/`if_neg` on the inner guard, mirroring the
    `_Of` proofs. No new axioms, no new sorries, no new
    definitions. -/

/-- **Fuel-generic compose-branch matrix decomposition.**

    Generalises `hgcdMatrixSafeOf_compose_branch` (PART XXI, S31,
    fuel `a + b`) to arbitrary fuel `f : ℕ`. Above threshold
    (`hab`), if the inner-guard *compose* branch fires
    (`hlt : max u v < max a b` for `(u, v)` the natAbs pair of
    `M_inner.apply (↑a, ↑b)`), then `hgcdMatrixSafe (f + 1) a b`
    equals the composed matrix `(hgcdMatrixSafe f u v).mul
    M_inner`.

    Specialises to `hgcdMatrixSafeOf_compose_branch` at
    `f := a + b` (since `hgcdMatrixSafeOf a b = hgcdMatrixSafe
    (a + b + 1) a b`).

    Proof: identical to the `_Of` version sans the
    `unfold hgcdMatrixSafeOf` opener; the rest is
    `rw [hgcdMatrixSafe_succ, if_neg hab]` + `dsimp only` +
    `if_pos hlt`. -/
theorem hgcdMatrixSafe_compose_branch (f a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hlt :
      max
        ((hgcdMatrixSafe f
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe f
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs
        < max a b) :
    hgcdMatrixSafe (f + 1) a b
      = (hgcdMatrixSafe f
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).mul
        (hgcdMatrixSafe f
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)) := by
  rw [hgcdMatrixSafe_succ, if_neg hab]
  dsimp only
  rw [if_pos hlt]

/-- **Fuel-generic compose-branch `apply` decomposition.**

    Generalises `hgcdSafeApply_compose_branch` (PART XXI, S31,
    fuel `a + b`) to arbitrary fuel `f : ℕ`. Above threshold and in
    the compose branch, `(hgcdMatrixSafe (f + 1) a b).apply (↑a)
    (↑b)` equals the outer matrix `hgcdMatrixSafe f u v` applied
    to the inner's column output `M_inner.apply (↑a) (↑b)`.

    Specialises to `hgcdSafeApply_compose_branch` at `f := a + b`
    (since `hgcdSafeApply a b = (hgcdMatrixSafeOf a b).apply (↑a)
    (↑b) = (hgcdMatrixSafe (a + b + 1) a b).apply (↑a) (↑b)`).

    Proof: rewrite the matrix via `hgcdMatrixSafe_compose_branch`,
    then `exact cofactor_mul_apply _ _ _ _` to distribute the
    apply over the multiplicative composition. -/
theorem hgcdMatrixSafe_apply_compose_branch (f a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hlt :
      max
        ((hgcdMatrixSafe f
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
        ((hgcdMatrixSafe f
            (a / 2 ^ hgcdShiftSafe a b)
            (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs
        < max a b) :
    (hgcdMatrixSafe (f + 1) a b).apply (a : ℤ) (b : ℤ)
      = (hgcdMatrixSafe f
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs).apply
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2 := by
  rw [hgcdMatrixSafe_compose_branch f a b hab hlt]
  exact cofactor_mul_apply _ _ _ _

/-- **Fuel-generic abort-branch matrix decomposition.**

    Generalises `hgcdMatrixSafeOf_abort_branch` (PART XXIII, S34,
    fuel `a + b`) to arbitrary fuel `f : ℕ`. Above threshold
    (`hab`), if the inner-guard *aborts* (`hge : max a b ≤ max u v`,
    the negation of the size-reduction guard), then
    `hgcdMatrixSafe (f + 1) a b` collapses to the inner recursion
    `M_inner` directly, without outer composition.

    Specialises to `hgcdMatrixSafeOf_abort_branch` at `f := a + b`.

    Proof: `rw [hgcdMatrixSafe_succ, if_neg hab]` + `dsimp only` +
    `if_neg (Nat.not_lt.mpr hge)`. -/
theorem hgcdMatrixSafe_abort_branch (f a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hge :
      max a b ≤
        max
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs) :
    hgcdMatrixSafe (f + 1) a b
      = hgcdMatrixSafe f
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b) := by
  rw [hgcdMatrixSafe_succ, if_neg hab]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr hge)]

/-- **Fuel-generic abort-branch `apply` decomposition.**

    Generalises `hgcdSafeApply_abort_branch` (PART XXIII, S34,
    fuel `a + b`) to arbitrary fuel `f : ℕ`. In the inner-abort
    branch, `(hgcdMatrixSafe (f + 1) a b).apply (↑a) (↑b)` equals
    `M_inner.apply (↑a) (↑b)` directly.

    Specialises to `hgcdSafeApply_abort_branch` at `f := a + b`.

    Proof: rewrite the matrix via `hgcdMatrixSafe_abort_branch`. -/
theorem hgcdMatrixSafe_apply_abort_branch (f a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hge :
      max a b ≤
        max
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe f
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs) :
    (hgcdMatrixSafe (f + 1) a b).apply (a : ℤ) (b : ℤ)
      = (hgcdMatrixSafe f
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ) := by
  rw [hgcdMatrixSafe_abort_branch f a b hab hge]

-- ═══════════════════════════════════════════════════════════════
-- PART XXXI: FIRING-COUNT ROW RECURRENCE + MONOTONICITY (Session 47)
-- ═══════════════════════════════════════════════════════════════

/-! ### Firing-count refinements (B.1 + B.3 per S46 PREP)

    S25 PART XVI introduced `outerGuardFiringCount`; S25 PART XVII +
    S26 PART XVIII established the structural empty/sub-threshold zero
    closures. S27 PART XIX closed the **survey-size** side with a row
    recurrence + closed-form triangular cardinality
    (`outerGuardSurveySize_succ` / `_triangular`). This section closes
    the analogous **firing-count** side: a row recurrence
    (`outerGuardFiringCount_succ`), a monotonicity corollary
    (`outerGuardFiringCount_mono_hi`), and a closed-form numeric
    upper bound (`outerGuardFiringCount_le_triangular`).

    All proofs are unconditional (0 axioms, 0 sorries) and structural
    (no `native_decide` enumeration). The row recurrence mirrors the
    S27 PART XIX `_succ` decomposition with the
    `schonhageOuterGuardFires` flag carried through the
    `Finset.filter` chain unchanged. -/

/-- **One-step recurrence for `outerGuardFiringCount`.** Extending the
    survey range from `hi` to `hi + 1` (with `lo ≤ hi`) adds exactly
    the firings in the new row `{(hi, b) | b ∈ [lo, hi + 1)}`, of
    cardinality `#{b ∈ [lo, hi + 1) | schonhageOuterGuardFires hi b}`.

    Mirrors `outerGuardSurveySize_succ` (T7); identical Finset-disjoint
    -union decomposition, with the inner `Finset.filter` on
    `schonhageOuterGuardFires` flowing through unchanged. -/
theorem outerGuardFiringCount_succ (lo hi : ℕ) (h : lo ≤ hi) :
    outerGuardFiringCount lo (hi + 1) =
      outerGuardFiringCount lo hi +
        ((Finset.Ico lo (hi + 1)).filter
          (fun b => schonhageOuterGuardFires hi b = true)).card := by
  unfold outerGuardFiringCount outerGuardFiringPairs outerGuardSurveyPairs
  set newRow := ((Finset.Ico lo (hi + 1)).filter
    (fun b => schonhageOuterGuardFires hi b = true)).image
    (fun b => (hi, b)) with hnewRow
  have hunion :
      (((Finset.Ico lo (hi + 1)) ×ˢ (Finset.Ico lo (hi + 1))).filter
          (fun p => p.2 ≤ p.1)).filter
            (fun p => schonhageOuterGuardFires p.1 p.2 = true) =
        (((Finset.Ico lo hi) ×ˢ (Finset.Ico lo hi)).filter
            (fun p => p.2 ≤ p.1)).filter
              (fun p => schonhageOuterGuardFires p.1 p.2 = true) ∪ newRow := by
    ext ⟨a, b⟩
    simp only [hnewRow, Finset.mem_filter, Finset.mem_product,
               Finset.mem_Ico, Finset.mem_union, Finset.mem_image,
               Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨ha_lo, ha_hi⟩, hb_lo, hb_hi⟩, hba⟩, hfires⟩
      by_cases hcase : a < hi
      · left
        exact ⟨⟨⟨⟨ha_lo, hcase⟩, hb_lo, by omega⟩, hba⟩, hfires⟩
      · push_neg at hcase
        have ha_eq : a = hi := by omega
        right
        refine ⟨b, ⟨⟨hb_lo, hb_hi⟩, ?_⟩, ha_eq.symm, rfl⟩
        rw [ha_eq] at hfires
        exact hfires
    · rintro (⟨⟨⟨⟨ha_lo, ha_hi⟩, hb_lo, hb_hi⟩, hba⟩, hfires⟩ |
              ⟨b', ⟨⟨hb'_lo, hb'_hi⟩, hb'_fires⟩, ha_eq, hb_eq⟩)
      · exact ⟨⟨⟨⟨ha_lo, by omega⟩, hb_lo, by omega⟩, hba⟩, hfires⟩
      · subst ha_eq
        subst hb_eq
        refine ⟨⟨⟨⟨h, by omega⟩, hb'_lo, hb'_hi⟩, ?_⟩, ?_⟩
        · omega
        · exact hb'_fires
  have hdisj :
      Disjoint
        ((((Finset.Ico lo hi) ×ˢ (Finset.Ico lo hi)).filter
            (fun p => p.2 ≤ p.1)).filter
              (fun p => schonhageOuterGuardFires p.1 p.2 = true))
        newRow := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    rw [hnewRow] at h2
    simp only [Finset.mem_filter, Finset.mem_product,
               Finset.mem_Ico] at h1
    simp only [Finset.mem_image, Prod.mk.injEq] at h2
    obtain ⟨⟨⟨⟨_, ha_hi⟩, _, _⟩, _⟩, _⟩ := h1
    obtain ⟨_, _, ha_eq, _⟩ := h2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, hnewRow,
      Finset.card_image_of_injective _
        (fun a₁ a₂ heq => (Prod.mk.inj heq).2)]

/-- **Monotonicity in `hi`.** Extending the survey range to include
    more pairs only adds firings. Direct corollary of
    `outerGuardFiringCount_succ`: the new-row firing cardinality is
    `≥ 0`. -/
theorem outerGuardFiringCount_mono_hi {lo hi₁ hi₂ : ℕ}
    (h : lo ≤ hi₁) (hle : hi₁ ≤ hi₂) :
    outerGuardFiringCount lo hi₁ ≤ outerGuardFiringCount lo hi₂ := by
  induction hi₂, hle using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have hkk : lo ≤ k := h.trans hk
    rw [outerGuardFiringCount_succ lo k hkk]
    exact ih.trans (Nat.le_add_right _ _)

/-- **Closed-form numeric upper bound on `outerGuardFiringCount`.**
    The firing count on `[lo, hi)²` is bounded by the triangular
    cardinality `(hi - lo) · (hi - lo + 1) / 2` for `lo ≤ hi`.

    Composes `outerGuardFiringCount_le_surveySize` (T1) with
    `outerGuardSurveySize_triangular` (T8). One-liner; provides a
    named entry point for the numeric bound without forcing consumers
    to apply T1 + T8 in sequence. -/
theorem outerGuardFiringCount_le_triangular (lo hi : ℕ) (h : lo ≤ hi) :
    outerGuardFiringCount lo hi ≤ (hi - lo) * (hi - lo + 1) / 2 := by
  calc outerGuardFiringCount lo hi
      ≤ outerGuardSurveySize lo hi :=
        outerGuardFiringCount_le_surveySize lo hi
    _ = (hi - lo) * (hi - lo + 1) / 2 :=
        outerGuardSurveySize_triangular lo hi h

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
   S19): a TOTAL CORRECT single-step GCD function based on Path A.
   `hgcdSafeGcd_eq_gcd` proves `hgcdSafeGcd a b = Nat.gcd a b`
   unconditionally, including on the PR #17024 counterexample
   inputs. Correctness depends only on the unimodularity invariant,
   not on size reduction.

5. **Recursive Schönhage-style GCD via iterated safe HGCD**
   (`schonhageGcd`, `schonhageGcdOf`, `schonhageGcd_eq_gcd`,
   `schonhageGcdOf_eq_gcd`, S20): a TOTAL CORRECT
   ITERATED GCD function. The body applies `hgcdSafeApply` once,
   checks whether the column-output natAbs strictly decreased
   `max a b`, and either recurses on the reduced pair or falls
   back to `Nat.gcd`. Two structural fallbacks (below-threshold
   dispatch + per-step size-reduction guard) make the function
   total. Correctness `schonhageGcd_eq_gcd a b = Nat.gcd a b`
   holds unconditionally, INDEPENDENT of whether the underlying
   `hgcdMatrixSafe` ever reduces magnitude — the OUTER guard here
   handles every pathological input by dispatching to `Nat.gcd`.

6. **API surface for `schonhageGcdOf`** (PART X, S21):
   eleven wrapper lemmas establishing that `schonhageGcdOf`
   satisfies the standard `Nat.gcd` algebraic identities — zero
   absorption, commutativity, associativity, divisibility, the
   universal property, and zero-vanishing. Plus
   `schonhageGcd_fuel_irrelevant`, which packages the corollary
   that the fuel parameter is semantically irrelevant: every
   choice of fuel yields `Nat.gcd a b`. With S21 in place the
   verified Schönhage GCD is a drop-in replacement for `Nat.gcd`
   with respect to all standard rewriting tactics.

7. **Extended algebraic identities + empirical witnesses**
   (PART XI–XII, S22, this PR): six further wrapper lemmas
   covering `Nat.gcd` identities not packaged in S21 — the
   universal property as an iff (`schonhageGcdOf_dvd_iff`), the
   two multiplicative laws (`_mul_left`, `_mul_right`), strict
   positivity from either input (`_pos_of_pos_left`,
   `_pos_of_pos_right`), and the concrete Fibonacci-style
   coprimality witness (`_succ_self`). PART XII adds five
   `native_decide`-checked sanity examples spanning the threshold
   edge, the S17 survey range, and beyond, which exercise the
   full Path A recursion stack rather than relying on the
   abstract correctness theorem.

**Significance of S20.** With `schonhageGcd_eq_gcd` in hand, the
verified algorithmic story for Path A is complete: a recursive
GCD function whose computational shape mirrors Schönhage's
classical recursion, proved correct on every natural input,
0 sorries, 0 axioms. The remaining gap is QUANTITATIVE — proving
that the per-step size-reduction guard fires often enough to
yield an asymptotic speedup over `Nat.gcd`. That step requires
both (a) a stronger invariant on `hgcdMatrixSafe` and (b) Mathlib
bit-complexity infrastructure that does not yet exist.

**Significance of S21.** The S21 API surface closes the
ergonomic gap: callers can use the verified Schönhage GCD with
exactly the same `simp`-style identities they would use for
`Nat.gcd`, without ever invoking the correctness theorem at the
call site. The proofs are uniformly trivial, but the lemmas are
load-bearing for downstream usability and document that the
verified function inherits the entire `Nat.gcd` theory.

**Significance of S22.** S22 completes the algebraic API
surface: the multiplicative laws, the iff form of the universal
property, strict positivity, and a concrete coprimality witness
fill out the gaps left by S21. The PART XII `native_decide`
witnesses are the first computational sanity checks that
exercise the closed-form recursion at scale — the kernel
reduces every fuel level and confirms the answer against the
reference GCD. Nothing in S22 is mathematically novel; the
contribution is the named wrapper plus end-to-end
computational verification.

**Significance of S23.** S23 extracts the OUTER size-reduction
guard from `schonhageGcd`'s recursive case as a Boolean
predicate `schonhageOuterGuardFires`. The headline theorem
`schonhageGcd_succ_via_outerGuard` reduces every reasoning step
about the recursion to a Boolean case-split on the predicate.

**Significance of S24.** S24 introduces a `List`-based survey
range hard-coded to the S17 PR #17024 family `{(a, b) : 64 ≤
b ≤ a < 130}`, with `surveyRange_length = 2211` confirming the
enumeration size, plus `outerGuardFiresInSurveyRange` /
`outerGuardAbortsInSurveyRange` density count definitions
ready for `native_decide` calibration.

**Significance of S25 (this PR).** S25 introduces the
**Finset-parameterised** density framework as a complement to
S24's `List`-based version. Three contributions:

  1. `outerGuardSurveyPairs lo hi : Finset (ℕ × ℕ)` —
     parameterised survey range, supporting the same density
     question on sub-threshold (`(0, 64)`), half-threshold
     (`(0, 32)`), or extended (`(64, 200)`) regions.

  2. `outerGuardFiringCount_le_surveySize` — a structural ≤
     bound proved via `Finset.card_filter_le`, leveraging the
     standard Mathlib API.

  3. `outerGuardFiringCount_below_threshold` — a closed-form
     theorem discharging the zero-firing question for ANY
     sub-threshold survey range. Direct corollary of S23's
     `schonhageOuterGuardFires_below_threshold` lemma
     specialised to all `(a, b)` with `max a b < 64`.

Three combinatorial survey-size witnesses (`outerGuardSurveySize
0 32 = 528`, `0 64 = 2080`, `64 130 = 2211`) confirm the
triangular-sum closed form. Three sub-threshold zero-firing
witnesses (`outerGuardFiringCount 0 32 = 0`, `0 64 = 0`,
`60 64 = 0`) corroborate the closed-form theorem on concrete
inputs. The bridge to S24 is direct: both `surveyRange.length`
and `outerGuardSurveySize 64 130` evaluate to `2211`, so the
two frameworks describe the same survey range with different
data structures (List for explicit enumeration order; Finset
for Mathlib-compatible cardinality + filter algebra).

**Path A roadmap (Session 23+):**

- Prove a structural inner-reduction theorem for
  `hgcdMatrixSafe`: characterise the input regime in which the
  inner runtime guard fires, ideally showing it fires "often"
  (e.g. on a measurable density of pairs above threshold). The
  S17 PART XIV counterexample shows the guard CAN abort, but
  empirically it succeeds on the majority of inputs in the survey
  range; quantifying that would yield a probabilistic speedup
  bound even in the absence of a Mathlib bit-complexity model.

- Quantitative bit-complexity bound: requires Mathlib
  infrastructure (fast multiplication, bit-complexity model)
  that does not yet exist. Defer until Mathlib lands these.

- Compare runtime behaviour of `schonhageGcd` against `Nat.gcd`
  on the PR #17024 counterexample family (`(130, 89)`, the
  worst case `(107, 85)`, etc.) to verify that the outer guard
  fires (rather than the iteration making progress) for those
  particular inputs.
-/
