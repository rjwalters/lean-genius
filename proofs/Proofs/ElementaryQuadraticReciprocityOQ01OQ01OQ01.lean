/-
# Gauss Sum Squared Identity for the QR Pathway
# (elementary-quadratic-reciprocity-oq-01-oq-01-oq-01)

## The Open Question

**OQ-01-OQ-01-OQ-01**: Can the Gauss sum squared identity τ² = χ(-1)·p be fully
proved in Lean 4 using ZMod machinery, filling in the key step of the Gauss
sum proof of Quadratic Reciprocity?

## Context

`ElementaryQuadraticReciprocityOQ01OQ01.lean` outlines the Gauss sum pathway for QR:

  Step 1: Define τ = Σ_a (a/p) · ζ^a (classical Gauss sum)
  Step 2: τ² = χ(-1) · p   ← THIS IS WHAT WE PROVE HERE
  Step 3: τ^q ≡ (p/q)·τ (mod q)  [Frobenius step — future work]
  Step 4: QR follows by comparing τ^q two ways

## Answer: YES

Using Mathlib's `gaussSum_sq` theorem from `Mathlib.NumberTheory.GaussSum`,
with:
- χ = quadratic character of ZMod p, promoted to ℂ via Int.cast
- ψ = ZMod.stdAddChar (the character ψ(a) = exp(2πia/p))

We prove: gaussSum χ ψ ^ 2 = χ(-1) · p  in ℂ.

The value χ(-1) = (-1)^(p/2) follows from the first supplementary law.

## Mathematical Significance

This result is the analytic heart of the Gauss sum proof of QR. The parent
file `ElementaryQuadraticReciprocityOQ02.lean` was forced to axiomatize this
as `gauss_sum_sq`. This file proves it genuinely holds in ℂ (the correct
domain — the integer version ∃ τ:ℤ, τ²=±p is false for all primes p).

## Axiom count: 0

All proofs derive from Mathlib's GaussSum and LegendreSymbol theory.
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

open MulChar AddChar ZMod Complex

namespace GaussSumSquaredQR

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

-- ============================================================================
-- The Quadratic Character of ZMod p, valued in ℂ
-- ============================================================================

/-- The Legendre symbol (·/p) as a multiplicative character ZMod p → ℂ. -/
def quadCharC : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

private lemma ringChar_ne_two (hodd : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact_mod_cast hodd

/-- The quadratic character is a genuine quadratic MulChar (values in {0,1,-1}). -/
theorem quadCharC_isQuadratic : (quadCharC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- For odd prime p, the quadratic character is nontrivial. -/
theorem quadCharC_ne_one (hodd : p ≠ 2) : quadCharC p ≠ 1 := by
  have hqc_ne : quadraticChar (ZMod p) ≠ 1 :=
    quadraticChar_ne_one (ringChar_ne_two p hodd)
  intro heq
  apply hqc_ne
  ext a
  -- ha : quadCharC p a = 1 (via MulChar.one_apply giving constant 1)
  have ha : quadCharC p a = 1 := by
    have h : quadCharC p a = (1 : MulChar (ZMod p) ℂ) a := by rw [heq]
    rwa [MulChar.one_apply] at h
  rw [MulChar.one_apply]  -- goal : quadraticChar a = 1
  rcases quadraticChar_isQuadratic (ZMod p) a with hv | hv | hv
  · -- Spell out: quadCharC p a = Int.cast (quadraticChar a) definitionally
    have ha2 : (Int.cast (quadraticChar (ZMod p) a) : ℂ) = 1 := ha
    rw [hv] at ha2; norm_num at ha2        -- (0:ℂ) = 1 → False
  · exact hv
  · have ha2 : (Int.cast (quadraticChar (ZMod p) a) : ℂ) = 1 := ha
    rw [hv] at ha2; push_cast at ha2; norm_num at ha2  -- (-1:ℂ) = 1 → False

-- ============================================================================
-- The Classical Gauss Sum
-- ============================================================================

/-- The classical Gauss sum: τ = Σ_{a:ZModp} (a/p) · exp(2πia/p).
    This is the key object in the Gauss sum proof of Quadratic Reciprocity. -/
def classicalGaussSum : ℂ :=
  gaussSum (quadCharC p) (ZMod.stdAddChar (N := p))

-- ============================================================================
-- Main Theorem: τ² = χ(-1) · p
-- ============================================================================

/-- **Gauss Sum Squared Identity** — the central step of the Gauss QR pathway:

    For odd prime p, the classical Gauss sum τ = Σ_a (a/p)·exp(2πia/p) satisfies

        τ² = (-1)^((p-1)/2) · p

    in ℂ. The exponent (p-1)/2 is p/2 (integer division), and (-1)^(p/2) = χ(-1)
    by the first supplementary law.

    Proof chain:
    (1) `gaussSum_sq`: for nontrivial quadratic χ and primitive ψ, τ² = χ(-1)·|ZMod p|
    (2) |ZMod p| = p by ZMod.card
    (3) χ(-1) = legendreSym p (-1) = χ₄(p) = (-1)^(p/2) by the first supplement -/
theorem gauss_sum_squared (hodd : p ≠ 2) :
    classicalGaussSum p ^ 2 = (-1 : ℂ) ^ (p / 2) * (p : ℂ) := by
  unfold classicalGaussSum
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp.out.pos⟩
  have hψ : (ZMod.stdAddChar (N := p)).IsPrimitive := ZMod.isPrimitive_stdAddChar
  have hχ_ne : quadCharC p ≠ 1 := quadCharC_ne_one p hodd
  have hχ_q : (quadCharC p).IsQuadratic := quadCharC_isQuadratic p
  rw [gaussSum_sq hχ_ne hχ_q hψ]
  have hcard : (Fintype.card (ZMod p) : ℂ) = (p : ℂ) := by
    exact_mod_cast ZMod.card p
  rw [hcard]
  suffices h_eval : quadCharC p (-1 : ZMod p) = (-1 : ℂ) ^ (p / 2) by rw [h_eval]
  have happ : quadCharC p (-1 : ZMod p) =
      (Int.cast : ℤ → ℂ) (quadraticChar (ZMod p) (-1 : ZMod p)) := rfl
  rw [happ]
  have hleg : quadraticChar (ZMod p) (-1 : ZMod p) = legendreSym p (-1 : ℤ) := by
    unfold legendreSym; congr 1; push_cast; ring
  rw [hleg, legendreSym.at_neg_one hodd]
  have hodd_mod : p % 2 = 1 := by
    have : ¬ 2 ∣ p := fun h2d => by
      rcases hp.out.eq_one_or_self_of_dvd 2 h2d with h | h
      · exact absurd h (by norm_num)
      · exact hodd h.symm
    omega
  rw [χ₄_eq_neg_one_pow hodd_mod]
  push_cast; ring

-- ============================================================================
-- Corollaries
-- ============================================================================

/-- **Existential form**: there exists τ : ℂ with τ² = (-1)^(p/2) · p.
    This promotes the axiom `gauss_sum_sq` in ElementaryQuadraticReciprocityOQ02
    to a theorem with an explicit witness (the classical Gauss sum). -/
theorem gauss_sum_squared_exists (hodd : p ≠ 2) :
    ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (p / 2) * (p : ℂ) :=
  ⟨classicalGaussSum p, gauss_sum_squared p hodd⟩

/-- **First supplement via Gauss sums**: -1 is a QR mod p iff p ≢ 3 (mod 4).
    Equivalently, (a/p) = -1 for a = -1 iff p ≡ 3 (mod 4).
    Directly from Mathlib's `ZMod.exists_sq_eq_neg_one_iff`. -/
theorem neg_one_quadratic_residue_iff :
    IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 :=
  ZMod.exists_sq_eq_neg_one_iff

/-- **Sign for p ≡ 1 (mod 4)**: τ² = p (positive). -/
theorem gauss_sum_sq_pos_case (hodd : p ≠ 2) (h : p % 4 = 1) :
    classicalGaussSum p ^ 2 = (p : ℂ) := by
  rw [gauss_sum_squared p hodd]
  have heven : Even (p / 2) := ⟨p / 4, by omega⟩
  rw [heven.neg_one_pow]; ring

/-- **Sign for p ≡ 3 (mod 4)**: τ² = -p (negative). -/
theorem gauss_sum_sq_neg_case (hodd : p ≠ 2) (h : p % 4 = 3) :
    classicalGaussSum p ^ 2 = -(p : ℂ) := by
  rw [gauss_sum_squared p hodd]
  have hodd_exp : Odd (p / 2) := ⟨p / 4, by omega⟩
  rw [hodd_exp.neg_one_pow]; ring

-- ============================================================================
-- Concrete Instances
-- ============================================================================

private instance factPrime3gsq : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance factPrime5gsq : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance factPrime7gsq : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance factPrime13gsq : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- p = 3 (≡ 3 mod 4): τ² = -3. -/
example : ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (3 / 2) * (3 : ℂ) :=
  gauss_sum_squared_exists 3 (by norm_num)

/-- p = 5 (≡ 1 mod 4): τ² = 5. -/
example : ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (5 / 2) * (5 : ℂ) :=
  gauss_sum_squared_exists 5 (by norm_num)

/-- p = 7 (≡ 3 mod 4): τ² = -7. -/
example : ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (7 / 2) * (7 : ℂ) :=
  gauss_sum_squared_exists 7 (by norm_num)

/-- p = 13 (≡ 1 mod 4): τ² = 13. -/
example : ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (13 / 2) * (13 : ℂ) :=
  gauss_sum_squared_exists 13 (by norm_num)

end GaussSumSquaredQR

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `gauss_sum_squared` | τ² = (-1)^(p/2)·p in ℂ | Proved (gaussSum_sq) |
  | `gauss_sum_squared_exists` | ∃ τ:ℂ, τ²=(-1)^(p/2)·p | Proved |
  | `neg_one_quadratic_residue_iff` | IsSquare(-1:ZModp) ↔ p≡1(4) | Proved |
  | `gauss_sum_sq_pos_case` | p≡1(4) → τ²=p | Proved |
  | `gauss_sum_sq_neg_case` | p≡3(4) → τ²=-p | Proved |

  **Sorries**: 0
  **Axioms**: 0

  Answer: YES — τ² = χ(-1)·p is fully provable in Lean 4.
-/
