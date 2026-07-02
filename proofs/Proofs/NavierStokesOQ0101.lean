import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
# Ladyzhenskaya's 2D Interpolation Inequality — Verified Algebraic Assembly (OQ-01-01)

## The Question
Parent problem `navier-stokes-oq-01` asks whether the **Ladyzhenskaya inequality**

    ‖u‖_{L⁴(ℝ²)}  ≤  C · ‖u‖_{L²}^{1/2} · ‖∇u‖_{L²}^{1/2}

— the interpolation estimate that drives 2D Navier–Stokes regularity — can be
formalized in Lean/Mathlib.

## What Mathlib Provides (and Does Not)
As of Mathlib v4.26 there is **no** Gagliardo–Nirenberg–Sobolev inequality and
**no** Ladyzhenskaya inequality. A grep across `Mathlib/Analysis/` for
`Ladyzhenskaya`, `GagliardoNirenberg`, `gagliardo` returns nothing. The weak-
derivative / Sobolev-space API needed for the *analytic* half of the classical
proof is not available in the form required. A full formalization from first
principles is a >1000-line foundational effort (see `knowledge.md`).

## What This File Does (honestly scoped)
Ladyzhenskaya's classical proof factors cleanly into
  (A) three **analytic** facts (an integrated pointwise product bound and two
      Cauchy–Schwarz estimates), and
  (B) a purely **algebraic** assembly of those three facts into the final
      interpolation bound, including the *sharp* constant.

Part (B) is entirely elementary and is fully verified here, **0 axioms, 0
sorries**. Part (A) is exposed as explicit hypotheses — these are precisely the
lemmas Mathlib is missing, so this file doubles as a specification of the gap.

Notation for the (nonnegative) norms of a compactly-supported `u : ℝ² → ℝ`:
`n2 = ‖u‖_{L²}`, `n4 = ‖u‖_{L⁴}`, `d1 = ‖∂₁u‖_{L²}`, `d2 = ‖∂₂u‖_{L²}`,
`ng = ‖∇u‖_{L²}` with `ng² = d1² + d2²`.

## References
- O. A. Ladyzhenskaya, *The Mathematical Theory of Viscous Incompressible Flow*,
  1969 (the L⁴/L² interpolation estimate, dimension 2).
- See `Proofs/NavierStokes.lean` for the surrounding 2D enstrophy development.
-/

namespace NavierStokes.OQ0101

open scoped Real

-- ═══════════════════════════════════════════════════════════════
-- The sharp AM–GM step
-- ═══════════════════════════════════════════════════════════════

/-- The one inequality that fixes Ladyzhenskaya's constant: `d1·d2 ≤ ½(d1²+d2²)`.
    Equivalently `‖∂₁u‖·‖∂₂u‖ ≤ ½‖∇u‖²`, sharp when `d1 = d2`. -/
theorem cross_le_grad_sq (d1 d2 : ℝ) : d1 * d2 ≤ (d1 ^ 2 + d2 ^ 2) / 2 := by
  nlinarith [sq_nonneg (d1 - d2)]

-- ═══════════════════════════════════════════════════════════════
-- The algebraic assembly of Ladyzhenskaya's proof
-- ═══════════════════════════════════════════════════════════════

/-- **Algebraic assembly of Ladyzhenskaya's inequality (2D).**

From the three analytic inputs of the classical proof —
* the integrated pointwise product bound `n4⁴ ≤ 4·a·b`, where
  `a = ∫∫|u||∂₁u|` and `b = ∫∫|u||∂₂u|`;
* the Cauchy–Schwarz estimate `a ≤ n2·d1` (slicing in `x`);
* the Cauchy–Schwarz estimate `b ≤ n2·d2` (slicing in `y`);

the sharp interpolation bound

    n4⁴ ≤ 2 · n2² · (d1² + d2²)

follows by pure algebra (AM–GM). Writing `ng² = d1² + d2²` this is
`‖u‖₄⁴ ≤ 2‖u‖₂²‖∇u‖₂²`, i.e. the Ladyzhenskaya constant `C = 2^{1/4}`. -/
theorem ladyzhenskaya_assembly
    (n2 n4 d1 d2 a b : ℝ)
    (hn2 : 0 ≤ n2) (hd1 : 0 ≤ d1)
    (hb : 0 ≤ b)
    (hprod : n4 ^ 4 ≤ 4 * a * b)     -- integrated pointwise bound
    (hCS1 : a ≤ n2 * d1)             -- Cauchy–Schwarz slicing in x
    (hCS2 : b ≤ n2 * d2) :           -- Cauchy–Schwarz slicing in y
    n4 ^ 4 ≤ 2 * n2 ^ 2 * (d1 ^ 2 + d2 ^ 2) := by
  -- Multiply the two Cauchy–Schwarz bounds: a·b ≤ (n2·d1)(n2·d2) = n2²·d1·d2.
  have hab : a * b ≤ (n2 * d1) * (n2 * d2) :=
    mul_le_mul hCS1 hCS2 hb (mul_nonneg hn2 hd1)
  -- Sharp AM–GM on the gradient components.
  have hcross := cross_le_grad_sq d1 d2
  -- n2² ≥ 0 lets us scale the AM–GM step.
  have hn2sq : (0 : ℝ) ≤ n2 ^ 2 := sq_nonneg n2
  nlinarith [hprod, hab, hcross, hn2sq,
    mul_le_mul_of_nonneg_left hcross hn2sq]

-- ═══════════════════════════════════════════════════════════════
-- Norm form with the explicit sharp constant
-- ═══════════════════════════════════════════════════════════════

/-- **Squared norm form.** From `n4⁴ ≤ 2·n2²·ng²` one gets the clean
    `n4² ≤ √2 · n2 · ng`, i.e. `‖u‖₄² ≤ √2 · ‖u‖₂ · ‖∇u‖₂`. Taking square roots
    once more recovers `‖u‖₄ ≤ 2^{1/4}‖u‖₂^{1/2}‖∇u‖₂^{1/2}`. -/
theorem ladyzhenskaya_sq_form
    (n2 n4 ng : ℝ) (hn2 : 0 ≤ n2) (hng : 0 ≤ ng)
    (h : n4 ^ 4 ≤ 2 * n2 ^ 2 * ng ^ 2) :
    n4 ^ 2 ≤ Real.sqrt 2 * n2 * ng := by
  have hrhs : (0 : ℝ) ≤ Real.sqrt 2 * n2 * ng :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hn2) hng
  -- Compare squares: (n4²)² = n4⁴ ≤ 2 n2² ng² = (√2 · n2 · ng)².
  have hsq : (n4 ^ 2) ^ 2 ≤ (Real.sqrt 2 * n2 * ng) ^ 2 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [h, hs2]
  have hn4sq : (0 : ℝ) ≤ n4 ^ 2 := sq_nonneg n4
  calc n4 ^ 2 = Real.sqrt ((n4 ^ 2) ^ 2) := (Real.sqrt_sq hn4sq).symm
    _ ≤ Real.sqrt ((Real.sqrt 2 * n2 * ng) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * n2 * ng := Real.sqrt_sq hrhs

-- ═══════════════════════════════════════════════════════════════
-- Final verification
-- ═══════════════════════════════════════════════════════════════

#check @cross_le_grad_sq
#check @ladyzhenskaya_assembly
#check @ladyzhenskaya_sq_form

end NavierStokes.OQ0101
