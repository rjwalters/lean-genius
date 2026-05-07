/-
# Gauss Sum Squared: From Axiom to Theorem in ℂ
# (elementary-quadratic-reciprocity-oq-02-oq-01)

## The Open Question

**OQ-02-OQ-01**: The parent proof `ElementaryQuadraticReciprocityOQ02.lean` uses:
```
  axiom gauss_sum_sq : ∃ (τ : ℤ), τ ^ 2 = (-1)^(p/2) * p
```
Can this axiom be proved using Mathlib's `gaussSum_sq` machinery and the
quadratic character infrastructure?

## Key Insight

The axiom as stated (over ℤ) is **mathematically false**: for any prime p,
there is no integer τ with τ² = ±p. The correct formulation requires working
in ℂ, where the **classical Gauss sum**

  τ = Σ_{a : ZMod p} χ(a) · ψ(a)  where χ = Legendre symbol, ψ = e^{2πi·/p}

satisfies τ² = χ(-1) · p = (-1)^((p-1)/2) · p.

## Proof Strategy

Using Mathlib's `gaussSum_sq` theorem (from `Mathlib.NumberTheory.GaussSum`):

  gaussSum_sq : for nontrivial quadratic χ and primitive ψ, (gaussSum χ ψ)² = χ(-1) · |R|

We instantiate with:
1. χ = `quadraticChar (ZMod p) ∘ Int.castRingHom ℂ` : MulChar (ZMod p) ℂ
   - quadratic: by `quadraticChar_isQuadratic`
   - nontrivial: by `quadraticChar_ne_one` (since char ≠ 2 for odd prime p)
2. ψ = `ZMod.stdAddChar (N := p)` : AddChar (ZMod p) ℂ
   - primitive: by `ZMod.isPrimitive_stdAddChar` (for any [NeZero p])

Result: τ² = χ(-1) · Fintype.card (ZMod p) = χ(-1) · p

Computing χ(-1) via the chain:
  χ(-1) = Int.cast (quadraticChar (ZMod p) (-1))
        = Int.cast (legendreSym p (-1))      [legendreSym = quadraticChar ∘ cast, by def]
        = Int.cast (ZMod.χ₄ ↑p)             [by legendreSym.at_neg_one]
        = (-1 : ℂ)^(p/2)                    [by χ₄_eq_neg_one_pow + push_cast]

## Axiom count: 0 new axioms

This proof replaces the parent's `gauss_sum_sq` axiom with a genuine Lean
theorem (restated in ℂ where it is actually true).
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

open MulChar AddChar ZMod Complex

namespace GaussSumQRCyclotomic

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

-- ============================================================================
-- Setup: The quadratic character of ZMod p, valued in ℂ
-- ============================================================================

/-- The quadratic character of ZMod p, promoted from ℤ to ℂ via Int.cast.
    This is the Legendre symbol (a/p) viewed as a multiplicative character
    from ZMod p to ℂ, which is the correct domain for the Gauss sum. -/
def quadCharC : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- For an odd prime p, the ring characteristic of ZMod p is p ≠ 2. -/
private lemma char_ZMod_ne_two (hodd : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact_mod_cast hodd

-- ============================================================================
-- Properties of quadCharC
-- ============================================================================

/-- quadCharC is a quadratic multiplicative character: values in {0, 1, -1} ⊆ ℂ. -/
theorem quadCharC_isQuadratic : (quadCharC p).IsQuadratic :=
  -- The quadratic property lifts through ring homomorphisms:
  -- if χ a ∈ {0,1,-1} and f is a ring hom then (f ∘ χ) a = f(χ a) ∈ {0,1,-1}
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- quadCharC is not the trivial character (for odd prime p).
    This uses quadraticChar_ne_one (valid since char(ZMod p) = p ≠ 2)
    and injectivity of Int.cast : ℤ → ℂ. -/
theorem quadCharC_ne_one (hodd : p ≠ 2) : quadCharC p ≠ 1 := by
  have hqc_ne : quadraticChar (ZMod p) ≠ 1 :=
    quadraticChar_ne_one (char_ZMod_ne_two p hodd)
  intro heq
  apply hqc_ne
  -- quadCharC p = quadraticChar.ringHomComp f, and f = Int.cast is injective
  -- If quadCharC p = 1, then f ∘ quadraticChar = 1, so quadraticChar = 1 by injectivity
  ext a
  have ha : (Int.cast (quadraticChar (ZMod p) a) : ℂ) = (1 : MulChar (ZMod p) ℂ) a := by
    show quadCharC p a = _; rw [heq]
  rw [MulChar.one_apply] at ha  -- ha : (Int.cast (quadraticChar a) : ℂ) = 1
  rw [MulChar.one_apply]        -- goal : quadraticChar a = 1
  rcases quadraticChar_isQuadratic (ZMod p) a with hv | hv | hv
  · rw [hv, map_zero] at ha; norm_num at ha
  · exact hv
  · rw [hv] at ha; push_cast at ha; norm_num at ha

-- ============================================================================
-- The Main Theorem
-- ============================================================================

/-- **Gauss Sum Squared Formula**:
    For odd prime p, the Gauss sum of the Legendre symbol satisfies
    τ² = (-1)^(p/2) · p  in ℂ.

    Proof uses Mathlib's `gaussSum_sq` with:
    - χ = quadCharC (quadratic character of ZMod p valued in ℂ)
    - ψ = ZMod.stdAddChar (standard additive character of ZMod p → ℂ)

    This corrects and proves the axiom `gauss_sum_sq` from
    ElementaryQuadraticReciprocityOQ02.lean, restating it in ℂ
    (where it is actually true, unlike the original ℤ version). -/
theorem gauss_sum_sq_in_complex (hodd : p ≠ 2) :
    gaussSum (quadCharC p) (ZMod.stdAddChar (N := p)) ^ 2 =
    (-1 : ℂ) ^ (p / 2) * (p : ℂ) := by
  -- Set up NeZero instance (prime p is positive, so p ≠ 0)
  haveI hNeZero : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp.out.pos⟩
  -- ψ is primitive
  have hψ : (ZMod.stdAddChar (N := p)).IsPrimitive := ZMod.isPrimitive_stdAddChar
  -- χ is nontrivial and quadratic
  have hχ_ne : quadCharC p ≠ 1 := quadCharC_ne_one p hodd
  have hχ_q : (quadCharC p).IsQuadratic := quadCharC_isQuadratic p
  -- Apply Mathlib's gaussSum_sq: τ² = χ(-1) · |ZMod p|
  rw [gaussSum_sq hχ_ne hχ_q hψ]
  -- Cardinality: |ZMod p| = p as ℂ
  have hcard : (Fintype.card (ZMod p) : ℂ) = (p : ℂ) := by
    exact_mod_cast ZMod.card p
  rw [hcard]
  -- Suffices to show quadCharC p (-1) = (-1)^(p/2)
  suffices h_eval : quadCharC p (-1 : ZMod p) = (-1 : ℂ) ^ (p / 2) by
    rw [h_eval]
  -- Step 1: quadCharC p a = Int.cast (quadraticChar (ZMod p) a) by definition
  have happ : quadCharC p (-1 : ZMod p) =
      (Int.cast : ℤ → ℂ) (quadraticChar (ZMod p) (-1 : ZMod p)) := rfl
  rw [happ]
  -- Step 2: quadraticChar (ZMod p) (-1) = legendreSym p (-1)
  -- legendreSym p a is defined as quadraticChar (ZMod p) (↑a), so this reduces to
  -- showing that (-1 : ZMod p) = ((-1 : ℤ) : ZMod p), which is true by ring.
  have hleg : quadraticChar (ZMod p) (-1 : ZMod p) = legendreSym p (-1 : ℤ) := by
    unfold legendreSym
    congr 1
    push_cast
    ring
  rw [hleg]
  -- Step 3: legendreSym p (-1) = χ₄ ↑p  [first supplementary law]
  rw [legendreSym.at_neg_one hodd]
  -- Step 4: χ₄ ↑p = (-1)^(p/2) for odd prime p
  have hodd_mod : p % 2 = 1 := by
    have h2 : ¬ 2 ∣ p := fun h2d => by
      rcases hp.out.eq_one_or_self_of_dvd 2 h2d with h | h
      · exact absurd h (by norm_num)
      · exact hodd h.symm
    omega
  rw [χ₄_eq_neg_one_pow hodd_mod]
  -- Int.cast commutes with (-1)^n: push_cast handles this
  push_cast; ring

/-- **Existential form** (corrected `gauss_sum_sq` from parent proof):
    For odd prime p, there exists τ : ℂ with τ² = (-1)^(p/2) · p.

    The witness is the explicit Gauss sum τ = Σ_a χ(a)ψ(a) where
    χ is the Legendre symbol and ψ is the standard additive character. -/
theorem gauss_sum_sq_exists (hodd : p ≠ 2) :
    ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (p / 2) * (p : ℂ) :=
  ⟨gaussSum (quadCharC p) (ZMod.stdAddChar (N := p)), gauss_sum_sq_in_complex p hodd⟩

/-- **Verification for p = 3**: τ² = (-1)^1 · 3 = -3 ∈ ℂ. -/
example : ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (3 / 2) * (3 : ℂ) :=
  gauss_sum_sq_exists 3 (by norm_num)

/-- **Verification for p = 5**: τ² = (-1)^2 · 5 = 5 ∈ ℂ. -/
example : ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (5 / 2) * (5 : ℂ) :=
  gauss_sum_sq_exists 5 (by norm_num)

/-- **Verification for p = 7**: τ² = (-1)^3 · 7 = -7 ∈ ℂ. -/
example : ∃ τ : ℂ, τ ^ 2 = (-1 : ℂ) ^ (7 / 2) * (7 : ℂ) :=
  gauss_sum_sq_exists 7 (by norm_num)

end GaussSumQRCyclotomic
