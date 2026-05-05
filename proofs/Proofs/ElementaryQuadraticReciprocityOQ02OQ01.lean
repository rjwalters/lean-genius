import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic

/-
# Gauss Sum Squared Formula: Corrected Statement and Proof

## Open Question (from elementary-quadratic-reciprocity-oq-02)

Prove the Gauss sum squared formula τ² = χ(-1)·p, which the parent entry
(OQ-02) axiomatized incorrectly with τ : ℤ.

## The Error in the Parent Entry

ElementaryQuadraticReciprocityOQ02.lean axiomatizes:
  `gauss_sum_sq : ∃ (τ : ℤ), τ ^ 2 = (-1) ^ (p / 2) * (p : ℤ)`

This axiom is false for ALL odd primes p:
- p ≡ 1 (mod 4): needs ∃ τ : ℤ, τ² = p. Impossible: p is prime, not a perfect square.
- p ≡ 3 (mod 4): needs ∃ τ : ℤ, τ² = -p. Impossible: τ² ≥ 0 > -p.

## The Correct Statement

The Gauss sum τ = Σ_{a : ZMod p} χ(a) · ψ(a) lives in the codomain R' of
the characters, not in ℤ. The correct formula:

  τ² = χ(-1) · p  in R'

This is Mathlib's `gaussSum_sq` (Mathlib.NumberTheory.GaussSum).

## Results Summary

| Theorem                    | Statement                         | Method         |
|----------------------------|-----------------------------------|----------------|
| `gauss_sum_sq_corrected`   | gaussSum χ ψ ^ 2 = χ(-1) * p     | gaussSum_sq    |
| `legendreSym_eq_quadChar`  | legendreSym p a = quadraticChar a | by definition  |
| `legendre_gauss_sum_sq`    | Gauss sum for Legendre char       | from above     |
| `parent_axiom_is_false`    | ¬ ∃ τ : ℤ, τ² = (-1)^(p/2) * p   | Nat.Prime      |

## References
- Gauss (1801): Disquisitiones Arithmeticae, §356
- Ireland & Rosen: Classical Introduction to Modern Number Theory, Ch. 8
- Mathlib: Mathlib.NumberTheory.GaussSum (`gaussSum_sq`)
-/

namespace GaussSumSquaredCorrection

open MulChar AddChar

-- ===========================================================================
-- Part I: The Corrected Gauss Sum Formula
-- ===========================================================================

/-- **Gauss Sum Squared Formula** (proven, not axiom)

    For p a prime, R = ZMod p, a nontrivial quadratic character
    χ : MulChar (ZMod p) R', and a primitive additive character ψ : AddChar (ZMod p) R':

      gaussSum χ ψ ^ 2 = χ(-1) * p

    Direct from `gaussSum_sq` (Mathlib.NumberTheory.GaussSum), with
    `Fintype.card (ZMod p) = p` from `ZMod.card`.

    **Correction to parent entry**: The parent's axiom `gauss_sum_sq` claimed τ : ℤ
    satisfying τ² = ±p. No such integer exists; τ must live in R'. -/
theorem gauss_sum_sq_corrected {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [hp : Fact p.Prime]
    {χ : MulChar (ZMod p) R'} (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 2 = χ (-1) * (p : R') := by
  have h := gaussSum_sq hχ₁ hχ₂ hψ
  rwa [ZMod.card] at h

-- ===========================================================================
-- Part II: Connection to the Legendre Symbol
-- ===========================================================================

variable {p : ℕ} [hp : Fact p.Prime]

/-- The Legendre symbol equals the quadratic character of ZMod p by definition. -/
theorem legendreSym_eq_quadChar (a : ℤ) :
    legendreSym p a = quadraticChar (ZMod p) (a : ZMod p) := rfl

/-- For the Legendre character embedded in R' via φ : ℤ →+* R',
    the Gauss sum satisfies:
      (Σ a : ZMod p, φ(legendreSym p a) · ψ(a))² = φ(legendreSym p (-1)) · p -/
theorem legendre_gauss_sum_sq {R' : Type*} [CommRing R'] [IsDomain R']
    (φ : ℤ →+* R')
    {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive)
    (hχ₁ : (quadraticChar (ZMod p)).ringHomComp φ ≠ 1) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp φ) ψ ^ 2 =
    φ (legendreSym p (-1)) * (p : R') := by
  have hχ₂ : ((quadraticChar (ZMod p)).ringHomComp φ).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp φ
  have hval : ((quadraticChar (ZMod p)).ringHomComp φ) (-1 : ZMod p) =
              φ (legendreSym p (-1)) := by
    simp only [legendreSym, ringHomComp_apply, map_neg, map_one, Int.cast_neg, Int.cast_one]
  rw [gauss_sum_sq_corrected hχ₁ hχ₂ hψ, hval]

-- ===========================================================================
-- Part III: Why the Parent Axiom Is False
-- ===========================================================================

/-- No integer τ satisfies τ² = (-1)^{p/2} · p for any odd prime p.
    This proves the parent entry's `gauss_sum_sq` axiom is mathematically false. -/
theorem parent_axiom_is_false {p : ℕ} [hpp : Fact p.Prime] (hodd : p ≠ 2) :
    ¬ ∃ (τ : ℤ), τ ^ 2 = (-1) ^ (p / 2) * (p : ℤ) := by
  intro ⟨τ, hτ⟩
  have hp := hpp.out
  -- (-1)^n is either 1 or -1 for any ring
  have hsgn : (-1 : ℤ) ^ (p / 2) = 1 ∨ (-1 : ℤ) ^ (p / 2) = -1 :=
    neg_one_pow_eq_or _
  rcases hsgn with h | h
  · -- Case: (-1)^(p/2) = 1, so τ² = p (prime — not a perfect square)
    rw [h, one_mul] at hτ
    have habs : τ.natAbs ^ 2 = p := by
      have key := congr_arg Int.natAbs hτ
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at key
    have hdvd : τ.natAbs ∣ p := ⟨τ.natAbs, by rw [← sq]; exact habs.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · -- τ.natAbs = 1, so 1^2 = 1 = p, but p ≥ 2
      rw [h1, one_pow] at habs
      exact hp.one_lt.ne habs
    · -- τ.natAbs = p, so p^2 = p, but p ≥ 2 means p^2 > p
      rw [h1] at habs
      nlinarith [hp.two_le]
  · -- Case: (-1)^(p/2) = -1, so τ² = -p < 0 (impossible since τ² ≥ 0)
    rw [h, neg_mul, one_mul] at hτ
    have hnn := sq_nonneg τ
    have hpos : (0 : ℤ) < p := by exact_mod_cast hp.pos
    linarith

-- ===========================================================================
-- Part IV: Summary Theorem
-- ===========================================================================

/-- **Complete Gauss Sum Analysis**

    Two complementary results:
    1. The Gauss sum squared formula τ² = χ(-1)·p is PROVED (not axiom).
    2. The parent entry's axiom (claiming τ : ℤ) is FALSE for all odd primes p.

    These results together show the complete picture: the formula IS true
    (in the right setting: τ in a domain R'), but the specific type claim τ : ℤ
    from the parent is always false. -/
theorem gauss_sum_analysis :
    (∀ {R' : Type} [CommRing R'] [IsDomain R'] {p : ℕ} [Fact p.Prime]
     {χ : MulChar (ZMod p) R'} (_ : χ ≠ 1) (_ : χ.IsQuadratic)
     {ψ : AddChar (ZMod p) R'} (_ : ψ.IsPrimitive),
     gaussSum χ ψ ^ 2 = χ (-1) * (p : R')) ∧
    (∀ {p : ℕ} [Fact p.Prime] (_ : p ≠ 2),
     ¬ ∃ (τ : ℤ), τ ^ 2 = (-1) ^ (p / 2) * (p : ℤ)) :=
  ⟨fun hχ₁ hχ₂ hψ => gauss_sum_sq_corrected hχ₁ hχ₂ hψ,
   fun hodd => parent_axiom_is_false hodd⟩

end GaussSumSquaredCorrection
