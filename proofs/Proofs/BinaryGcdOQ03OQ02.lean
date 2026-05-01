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

  Out of scope (deferred — see `hgcdMatrix_size_reduction`):
  The bit-complexity claim O(M(n)·log n) requires a Mathlib model of
  fast multiplication and bit operations that does not yet exist.
  Filling that gap is a multi-thousand-line foundational project. The
  size-reduction lemma needed for the complexity claim is stated as
  `hgcdMatrix_size_reduction` below with a focused open question.

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
  simp [CofactorMatrix.mul, CofactorMatrix.apply]
  refine ⟨?_, ?_⟩ <;> ring

-- ═══════════════════════════════════════════════════════════════
-- PART II: RECURSIVE HGCD MATRIX (fuel-indexed, total)
-- ═══════════════════════════════════════════════════════════════

/-- The HGCD recursion threshold. Below this, fall back to the
    full Lehmer cofactor accumulation (which itself bottoms out at
    a Euclidean iteration on small approximations). -/
def hgcdThreshold : ℕ := 64

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
          let s = ⌈bits(max a b) / 2⌉
          â, b̂ = top-half-bit truncations a >> s, b >> s
          M₁ = hgcdMatrix(â, b̂)              -- top-half subproblem
          (u, v) = M₁ applied to full (a, b)   -- full-precision reduce
          M₂ = hgcdMatrix(|u|, |v|)            -- bottom-half subproblem
          return M₂ · M₁

    Termination by `fuel`: the recursive calls always pass `fuel`
    decreased by one. With `fuel = a + b + 1` (or any large enough
    bound), the algorithm always reaches its natural base. -/
def hgcdMatrix : ℕ → ℕ → ℕ → CofactorMatrix
  | 0, _, _ => CofactorMatrix.id
  | fuel + 1, a, b =>
    if max a b < hgcdThreshold then
      lehmerCofactors hgcdThreshold a b CofactorMatrix.id
    else
      let n := Nat.log 2 (max a b) + 1
      let s := n / 2
      let ahat := a / 2 ^ s
      let bhat := b / 2 ^ s
      let M₁ := hgcdMatrix fuel ahat bhat
      let uv := M₁.apply (a : ℤ) (b : ℤ)
      let M₂ := hgcdMatrix fuel uv.1.natAbs uv.2.natAbs
      M₂.mul M₁

/-- Top-level entry point: HGCD with sufficient fuel to terminate. -/
def hgcdMatrixOf (a b : ℕ) : CofactorMatrix :=
  hgcdMatrix (a + b + 1) a b

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
    simp [hgcdMatrix, CofactorMatrix.det_id]
  | succ f ih =>
    rw [hgcdMatrix]
    by_cases hsmall : max a b < hgcdThreshold
    · simp [hsmall]
      exact lehmerCofactors_det_unit hgcdThreshold a b CofactorMatrix.id
        (Or.inl CofactorMatrix.det_id)
    · simp [hsmall]
      -- Recursive case: result is M₂.mul M₁
      set s := (Nat.log 2 (max a b) + 1) / 2 with hs
      set ahat := a / 2 ^ s with hahat
      set bhat := b / 2 ^ s with hbhat
      set M₁ := hgcdMatrix f ahat bhat with hM1
      set uv := M₁.apply (a : ℤ) (b : ℤ) with huv
      set M₂ := hgcdMatrix f uv.1.natAbs uv.2.natAbs with hM2
      -- (M₂.mul M₁).det = M₂.det * M₁.det = ±1 * ±1 = ±1
      rw [CofactorMatrix.det_mul]
      have h1 : M₁.det = 1 ∨ M₁.det = -1 := ih ahat bhat
      have h2 : M₂.det = 1 ∨ M₂.det = -1 := ih uv.1.natAbs uv.2.natAbs
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
    let M := hgcdMatrix fuel a b
    Int.gcd (M.α * (a : ℤ) + M.β * (b : ℤ))
            (M.γ * (a : ℤ) + M.δ * (b : ℤ)) = Nat.gcd a b := by
  exact cofactor_apply_gcd (hgcdMatrix_det_unit fuel a b)

/-- Top-level HGCD preserves GCD. -/
theorem hgcdMatrixOf_preserves_gcd (a b : ℕ) :
    let M := hgcdMatrixOf a b
    Int.gcd (M.α * (a : ℤ) + M.β * (b : ℤ))
            (M.γ * (a : ℤ) + M.δ * (b : ℤ)) = Nat.gcd a b :=
  hgcdMatrix_preserves_gcd _ a b

-- ═══════════════════════════════════════════════════════════════
-- PART V: COMPUTATIONAL VERIFICATION (small cases)
-- ═══════════════════════════════════════════════════════════════

/-- Below threshold, HGCD reduces to one Lehmer cofactor accumulation. -/
theorem hgcdMatrix_small (fuel a b : ℕ) (h : max a b < hgcdThreshold) :
    hgcdMatrix (fuel + 1) a b =
      lehmerCofactors hgcdThreshold a b CofactorMatrix.id := by
  rw [hgcdMatrix]
  simp [h]

/-- HGCD of (0, 0) is the identity matrix (only the base case fires). -/
example : hgcdMatrix 5 0 0 = CofactorMatrix.id := by
  rw [hgcdMatrix]
  simp [hgcdThreshold, lehmerCofactors, lehmerInnerStep]

-- Verify det ±1 on small concrete inputs
example : (hgcdMatrixOf 89 55).det = 1 ∨ (hgcdMatrixOf 89 55).det = -1 :=
  hgcdMatrixOf_det_unit 89 55

example : (hgcdMatrixOf 100 75).det = 1 ∨ (hgcdMatrixOf 100 75).det = -1 :=
  hgcdMatrixOf_det_unit 100 75

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

**Architectural significance:** This file establishes that the
*operational correctness* of Schönhage's recursive HGCD reduces to
the matrix-determinant invariant already proved for Lehmer's
algorithm. The recursion structure adds no new GCD-preservation
obligation — it only redistributes work across recursion levels for
asymptotic complexity gain.

**Out of scope (deferred):**

- Bit-complexity bound O(M(n)·log n) (`hgcdMatrix_size_reduction`):
  requires Mathlib infrastructure (fast multiplication, bit-complexity
  model) that does not yet exist. The size-reduction lemma is stated
  as a placeholder; filling it requires a separate Mathlib-contribution
  initiative. See knowledge.md for the breakdown.
-/

end HGcd
