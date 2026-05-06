/-
  Angle Trisection OQ02-OQ01-OQ01-OQ01-OQ01:
  Inseparable Galois Groups: Counterexample and Correct Statement

  **Open question**: Can `insep_gal_trivial` be proved in Lean using Mathlib's
  purely inseparable extension infrastructure?

  **Answer: NO — the axiom as stated is mathematically FALSE.**

  The axiom `insep_gal_trivial` (AngleTrisectionOQ02OQ01OQ01OQ01.lean) claims:
    inseparable irreducible f over char-p field  →  |Gal(f)| = 1

  This fails for f = g(X^p) when g is a separable irreducible of degree ≥ 2.
  In that case Gal(f) ≅ Gal(g), which can be nontrivial.

  ## Counterexample Analysis

  Over F = F₂(a) (char 2), let g(X) = X² + X + a (Artin-Schreier, separable irreducible).
  Set f(X) = g(X²) = X⁴ + X² + a.

  **f is irreducible over F₂(a)**:
    Any quadratic factoring (X²+b₁X+c₁)(X²+b₂X+c₂) forces b₁ = b₂ (from X³ = 0).
    If b₁ = 0: c₁ + c₂ = 1, c₁c₂ = a, so c₁, c₂ are roots of X²+X+a.
    But X²+X+a is irreducible over F₂(a) (Artin-Schreier: a ≠ t²+t for any t ∈ F₂(a)).
    If b₁ ≠ 0: b₁(c₁+c₂) = 0 forces c₁ = c₂, then 0 = b₁² gives b₁ = 0. Contradiction.

  **f is inseparable**: f'(X) = 4X³ + 2X = 0 in char 2.

  **|Gal(f)| = 2, not 1**:
    If α satisfies α² + α + a = 0, then β = α + 1 satisfies β² + β + a = 0 (the other root).
    In char 2: (α^(1/2))² = α, and (β^(1/2))² = β.
    But (α^(1/2) + 1)² = α^(1/2)² + 1² = α + 1 = β (since char 2).
    So β^(1/2) = α^(1/2) + 1 ∈ F(α^(1/2)), and f.SplittingField = F(α^(1/2)).
    The map σ: α^(1/2) ↦ α^(1/2) + 1 is a nontrivial F-automorphism of order 2.
    Hence |Gal(f)| = 2.

  ## The Correct Theorem

  The correct hypothesis is not "f inseparable" but "f.SplittingField/F is purely inseparable."
  This holds exactly when f(X) = c·(X - r)^(p^e) for some r in the splitting field.

  Key proof: if K/F is purely inseparable and σ : K ≃ₐ[F] K, then σ = id.
  For each x ∈ K, ∃ n with x^(p^n) ∈ F. Then:
    σ(x)^(p^n) = σ(x^(p^n)) = x^(p^n)
  Subtracting: (σ(x) - x)^(p^n) = σ(x)^(p^n) - x^(p^n) = 0 (using char-p Frobenius).
  A field has no nonzero nilpotents, so σ(x) = x.

  Parent: AngleTrisectionOQ02OQ01OQ01OQ01.lean
  Answers: angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01

  Axioms: 1 (counterexample_gal_card)
  Sorries: 0
  Theorems: 7
-/

import Mathlib

open Polynomial

namespace AngleTrisectionInsepGalCorrect

-- ============================================================================
-- Part I: The Counterexample Framework
-- ============================================================================

noncomputable def base : Type := FractionRing (Polynomial (ZMod 2))

noncomputable instance base_field : Field base := inferInstance

noncomputable def aGen : base :=
  algebraMap (Polynomial (ZMod 2)) base Polynomial.X

noncomputable def f_target : base[X] :=
  Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.C aGen

noncomputable def g_factor : base[X] :=
  Polynomial.X ^ 2 + Polynomial.X + Polynomial.C aGen

/-- f_target = g_factor ∘ (X²): the structural relationship confirming f = g(X²). -/
lemma f_is_g_composed_sq : f_target = g_factor.comp (Polynomial.X ^ 2) := by
  simp only [f_target, g_factor, Polynomial.comp, Polynomial.eval₂_add,
             Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  ring

/-- f is inseparable: all exponents in f are even, so f' = 0 in char 2. -/
lemma f_derivative_zero : f_target.derivative = 0 := by
  simp [f_target, Polynomial.derivative_add, Polynomial.derivative_pow,
        Polynomial.derivative_C, Polynomial.derivative_X_pow]
  ring

-- ============================================================================
-- Part II: The Correct Theorem — Purely Inseparable ⟹ Trivial Galois Group
-- ============================================================================

/-- In characteristic p, (a - b)^(p^n) = a^(p^n) - b^(p^n).

    Proof: iterateFrobenius K p n is a ring hom, so map_sub gives the result directly. -/
lemma sub_pow_char_pow_eq {K : Type*} [CommRing K] {p : ℕ} [CharP K p] [hp : Fact p.Prime]
    (a b : K) (n : ℕ) : (a - b) ^ p ^ n = a ^ p ^ n - b ^ p ^ n := by
  have h := (iterateFrobenius K p n).map_sub a b
  simp only [iterateFrobenius_def] at h
  exact h

/-- **Key theorem**: Every F-algebra automorphism of a purely inseparable extension is the identity.

    For any x ∈ K with IsPurelyInseparable F K:
    - ∃ n with x^(p^n) ∈ F (by definition of purely inseparable)
    - σ(x)^(p^n) = σ(x^(p^n)) = x^(p^n) (σ fixes F)
    - (σ(x) - x)^(p^n) = 0 by char-p Frobenius identity
    - σ(x) = x since K has no nonzero nilpotents -/
theorem algEquiv_eq_refl_of_isPurelyInseparable {F K : Type*} [Field F] [Field K]
    [Algebra F K] {p : ℕ} [CharP F p] [CharP K p] [hp : Fact p.Prime]
    [IsPurelyInseparable F K] (σ : K ≃ₐ[F] K) : σ = AlgEquiv.refl F K := by
  ext x
  simp only [AlgEquiv.coe_refl, Function.id_eq]
  -- Get n with x^(ringChar F)^n in the image of algebraMap F K
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (F := F) x
  -- Convert ringChar F to p using characteristic uniqueness
  have hringF : ringChar F = p := CharP.eq F (ringChar.charP F) inferInstance
  rw [hringF] at hn
  obtain ⟨c, hc⟩ := hn
  -- σ fixes elements in the image of F
  have hfixed : σ (x ^ p ^ n) = x ^ p ^ n := by rw [← hc]; exact σ.commutes c
  -- σ(x)^(p^n) = x^(p^n) via map_pow
  have hpow : σ x ^ p ^ n = x ^ p ^ n := by rw [← map_pow σ x, hfixed]
  -- (σ(x) - x)^(p^n) = 0 using char-p subtraction
  have hzero : (σ x - x) ^ p ^ n = 0 := by
    rw [sub_pow_char_pow_eq (σ x) x n, hpow, sub_self]
  -- σ(x) = x since K is a field (no nilpotents)
  have hne : p ^ n ≠ 0 := pow_ne_zero _ (Nat.Prime.pos hp.out).ne'
  exact sub_eq_zero.mp (pow_eq_zero_iff hne |>.mp hzero)

/-- **Main theorem**: If f.SplittingField is purely inseparable over F, then |Gal(f)| = 1.

    This is the correct replacement for the false axiom `insep_gal_trivial`. -/
theorem gal_card_one_of_purelyInseparable_splitting {F : Type*} [Field F]
    {p : ℕ} [CharP F p] [hp : Fact p.Prime]
    (f : F[X]) [hK : IsPurelyInseparable F f.SplittingField]
    [hcharK : CharP f.SplittingField p] :
    Nat.card f.Gal = 1 := by
  haveI : Unique f.Gal :=
    ⟨⟨AlgEquiv.refl F f.SplittingField⟩, fun σ => algEquiv_eq_refl_of_isPurelyInseparable σ⟩
  exact Nat.card_unique

-- ============================================================================
-- Part III: The Counterexample — |Gal(f_target)| = 2
-- ============================================================================

/-- The splitting field of f_target = X⁴+X²+a is NOT purely inseparable over F₂(a),
    because it has the nontrivial automorphism σ: α^(1/2) ↦ α^(1/2) + 1.
    We axiomatize the conclusion |Gal(f_target)| = 2 pending full formalization of the
    Artin-Schreier extension theory over F₂(a). -/
axiom counterexample_gal_card : Nat.card f_target.Gal = 2

/-- The axiom `insep_gal_trivial` in AngleTrisectionOQ02OQ01OQ01OQ01.lean is incorrect:
    the inseparable, irreducible f_target has |Gal(f_target)| = 2, not 1. -/
theorem insep_gal_trivial_refuted :
    ∃ (f : base[X]), ¬ f.Separable ∧ Nat.card f.Gal ≠ 1 := by
  refine ⟨f_target, ?_, ?_⟩
  · -- f_target is inseparable: f' = 0, so IsCoprime f_target 0 → IsUnit f_target (false)
    intro h_sep
    rw [Polynomial.Separable, f_derivative_zero, isCoprime_zero_right] at h_sep
    -- h_sep : IsUnit f_target; if unit then natDegree = 0, but f_target has degree 4
    rw [Polynomial.isUnit_iff] at h_sep
    obtain ⟨u, hu⟩ := h_sep
    have h1 : f_target.natDegree = 0 := by
      have := congr_arg Polynomial.natDegree hu.symm
      rwa [Polynomial.natDegree_C] at this
    have h2 : f_target.natDegree = 4 := by
      simp only [f_target]; compute_degree!
    omega
  · -- |Gal(f_target)| = 2 ≠ 1
    rw [counterexample_gal_card]; norm_num

-- ============================================================================
-- Part IV: Summary
-- ============================================================================

/-!
## Conclusion

`insep_gal_trivial` is mathematically INCORRECT.

The correct statement: `gal_card_one_of_purelyInseparable_splitting`
- Hypothesis: `IsPurelyInseparable F f.SplittingField`
- Conclusion: `Nat.card f.Gal = 1`

This is provable from Mathlib's `IsPurelyInseparable` API.

The false axiom should be replaced in the parent entry.

| Theorem | Status |
|---------|--------|
| `f_is_g_composed_sq` | proved |
| `f_derivative_zero` | proved |
| `sub_pow_char_pow_eq` | proved (iterateFrobenius.map_sub) |
| `algEquiv_eq_refl_of_isPurelyInseparable` | proved (CharP.eq + iterateFrobenius) |
| `gal_card_one_of_purelyInseparable_splitting` | proved |
| `insep_gal_trivial_refuted` | proved |
| `counterexample_gal_card` | axiom |
-/

end AngleTrisectionInsepGalCorrect
