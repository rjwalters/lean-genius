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
  Theorems: 19
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ01OQ01OQ01

open Polynomial

namespace AngleTrisectionInsepGalCorrect

-- ============================================================================
-- Part I: The Counterexample Framework
-- ============================================================================

/-- `base = F₂(a)`. Declared as `abbrev` (reducible) so instance synthesis
    can unfold it to `FractionRing (Polynomial (ZMod 2))` and pick up the
    `Field`, `Algebra (Polynomial (ZMod 2)) ·`, and `IsFractionRing` instances
    automatically (a non-reducible `def` would block synthesis in tactic
    contexts even when the term-mode body of `aGen` succeeded). -/
noncomputable abbrev base : Type := FractionRing (Polynomial (ZMod 2))

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
  have h2 : (2 : base) = 0 := CharP.cast_eq_zero base 2
  have h4 : (4 : base) = 0 := by
    have e : (4 : base) = 2 * 2 := by norm_num
    rw [e, h2, zero_mul]
  unfold f_target
  rw [Polynomial.derivative_add, Polynomial.derivative_add,
      Polynomial.derivative_C, add_zero,
      Polynomial.derivative_X_pow, Polynomial.derivative_X_pow,
      show ((4 : ℕ) : base) = 0 from h4, show ((2 : ℕ) : base) = 0 from h2,
      Polynomial.C_0, zero_mul, zero_mul, add_zero]

/-- f_target = X⁴ + X² + aGen has natDegree 4 (the leading X⁴ term dominates). -/
lemma f_target_natDegree : f_target.natDegree = 4 := by
  unfold f_target; compute_degree!

/-- f_target = X⁴ + X² + aGen has degree 4. -/
lemma f_target_degree : f_target.degree = 4 := by
  unfold f_target; compute_degree!

/-- f_target is nonzero — immediate from natDegree = 4. -/
lemma f_target_ne_zero : f_target ≠ 0 := by
  intro h
  have hd : f_target.natDegree = 4 := f_target_natDegree
  rw [h, Polynomial.natDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- f_target is monic (leading coefficient = 1). -/
lemma f_target_monic : f_target.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, f_target_natDegree]
  unfold f_target
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-- g_factor = X² + X + aGen has natDegree 2 (the leading X² term dominates). -/
lemma g_factor_natDegree : g_factor.natDegree = 2 := by
  unfold g_factor; compute_degree!

/-- g_factor = X² + X + aGen has degree 2. -/
lemma g_factor_degree : g_factor.degree = 2 := by
  unfold g_factor; compute_degree!

/-- g_factor is nonzero — immediate from natDegree = 2. -/
lemma g_factor_ne_zero : g_factor ≠ 0 := by
  intro h
  have hd : g_factor.natDegree = 2 := g_factor_natDegree
  rw [h, Polynomial.natDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- g_factor is monic (leading coefficient = 1). -/
lemma g_factor_monic : g_factor.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, g_factor_natDegree]
  unfold g_factor
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_C]

/-- Coefficient of X⁰ in f_target = X⁴ + X² + aGen is aGen. -/
lemma f_target_coeff_zero : f_target.coeff 0 = aGen := by
  unfold f_target
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-- Coefficient of X² in f_target = X⁴ + X² + aGen is 1. -/
lemma f_target_coeff_two : f_target.coeff 2 = 1 := by
  unfold f_target
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-- Coefficient of X⁴ in f_target = X⁴ + X² + aGen is 1. -/
lemma f_target_coeff_four : f_target.coeff 4 = 1 := by
  unfold f_target
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-- Coefficient of X¹ in f_target = X⁴ + X² + aGen is 0 (no linear term). -/
lemma f_target_coeff_one : f_target.coeff 1 = 0 := by
  unfold f_target
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-- Coefficient of X³ in f_target = X⁴ + X² + aGen is 0 (no cubic term). -/
lemma f_target_coeff_three : f_target.coeff 3 = 0 := by
  unfold f_target
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

-- ============================================================================
-- Part I.5: Step 1a — aGen is not a square in base
--
-- Closest concrete next step in the multi-session plan to discharge
-- `counterexample_gal_card`. Consumed by Capelli-style irreducibility of
-- `g_factor.comp (X^2)` (Step 1c).
--
-- Proof: a putative square `y² = aGen` rewrites (via `IsLocalization.surj`
-- onto `mk' p q` and clearing denominators) to `p² = X · q²` in
-- `Polynomial (ZMod 2)`. Taking `natDegree` gives an even number = odd
-- number, contradiction (closed by `omega`).
-- ============================================================================

/-- `aGen ≠ 0` in `base`: `algebraMap` from a domain to its FractionRing is
    injective, and `Polynomial.X ≠ 0`. -/
lemma aGen_ne_zero : aGen ≠ 0 := by
  intro h
  have h' : algebraMap (Polynomial (ZMod 2)) base Polynomial.X =
            algebraMap (Polynomial (ZMod 2)) base 0 := by
    rw [map_zero]; exact h
  exact Polynomial.X_ne_zero
    (IsFractionRing.injective (Polynomial (ZMod 2)) base h')

/-- Internal helper: in `Polynomial (ZMod 2)`, the equation `p² = X · q²`
    with `q ≠ 0` is impossible by `natDegree` parity (`2 · deg p = 1 + 2 · deg q`,
    even = odd). -/
private lemma R_sq_eq_X_mul_sq_imp_false
    {p q : Polynomial (ZMod 2)} (hq : q ≠ 0)
    (hpq : p * p = Polynomial.X * (q * q)) : False := by
  have hX : (Polynomial.X : Polynomial (ZMod 2)) ≠ 0 := Polynomial.X_ne_zero
  have hpp_ne : p * p ≠ 0 := by
    rw [hpq]; exact mul_ne_zero hX (mul_ne_zero hq hq)
  have hp : p ≠ 0 := fun h => hpp_ne (by rw [h, zero_mul])
  have hLHS : (p * p).natDegree = 2 * p.natDegree := by
    rw [Polynomial.natDegree_mul hp hp]; ring
  have hRHS : (Polynomial.X * (q * q)).natDegree = 1 + 2 * q.natDegree := by
    rw [Polynomial.natDegree_mul hX (mul_ne_zero hq hq),
        Polynomial.natDegree_X, Polynomial.natDegree_mul hq hq]
    ring
  have hEq : 2 * p.natDegree = 1 + 2 * q.natDegree := by
    have := congrArg Polynomial.natDegree hpq
    rw [hLHS, hRHS] at this; exact this
  omega

/-- **Step 1a**: `aGen` is not a square in `base = FractionRing (Polynomial (ZMod 2))`.

    Proof: a putative square `aGen = y · y` rewrites (via `IsLocalization.surj`
    onto a representative `(p, q)` with `q ∈ R⁰`) to `p² = X · q²` in
    `Polynomial (ZMod 2)` — which is impossible by `natDegree` parity.

    Consumed by Capelli-style irreducibility of `f_target = g_factor.comp (X^2)`
    (Step 1c in the chain that discharges `counterexample_gal_card`). -/
lemma aGen_not_isSquare : ¬ IsSquare aGen := by
  rintro ⟨y, hy⟩
  -- hy : aGen = y * y
  obtain ⟨⟨p, q⟩, hyq⟩ :=
    IsLocalization.surj (M := nonZeroDivisors (Polynomial (ZMod 2)))
      (S := base) y
  -- hyq : y * (algebraMap _ _) ↑q = (algebraMap _ _) p
  set qP : Polynomial (ZMod 2) := (q : Polynomial (ZMod 2)) with hqP
  have hqv_ne : qP ≠ 0 := nonZeroDivisors.coe_ne_zero q
  -- Bridge: clear denominators to obtain p² = X · q² in Polynomial (ZMod 2).
  have hpq : p * p = Polynomial.X * (qP * qP) := by
    -- Square hyq:
    have h_sq_eq :
        (y * algebraMap (Polynomial (ZMod 2)) base qP) *
          (y * algebraMap (Polynomial (ZMod 2)) base qP) =
        algebraMap (Polynomial (ZMod 2)) base p *
          algebraMap (Polynomial (ZMod 2)) base p := by
      rw [hyq]
    -- Translate to a single algebraMap equation, then use injectivity.
    have h_alg :
        algebraMap (Polynomial (ZMod 2)) base (p * p) =
        algebraMap (Polynomial (ZMod 2)) base
          (Polynomial.X * (qP * qP)) := by
      have hy' : algebraMap (Polynomial (ZMod 2)) base Polynomial.X = y * y := hy
      rw [map_mul, map_mul, map_mul, ← h_sq_eq, hy']
      ring
    exact IsFractionRing.injective (Polynomial (ZMod 2)) base h_alg
  exact R_sq_eq_X_mul_sq_imp_false hqv_ne hpq

-- ============================================================================
-- Part II: The Correct Theorem — Purely Inseparable ⟹ Trivial Galois Group
-- ============================================================================

/-- In characteristic p, (a - b)^(p^n) = a^(p^n) - b^(p^n).

    Proof: the iterated Frobenius `iterateFrobenius K p n : K →+* K` is a ring
    homomorphism whose underlying map is `x ↦ x^(p^n)` (`iterateFrobenius_def`),
    so it commutes with subtraction by `map_sub`. -/
lemma sub_pow_char_pow_eq {K : Type*} [CommRing K] {p : ℕ} [CharP K p] [hp : Fact p.Prime]
    (a b : K) (n : ℕ) : (a - b) ^ p ^ n = a ^ p ^ n - b ^ p ^ n := by
  simpa [iterateFrobenius_def] using map_sub (iterateFrobenius K p n) a b

/-- **Key theorem**: Every F-algebra automorphism of a purely inseparable extension is the identity.

    For any x ∈ K with IsPurelyInseparable F K:
    - ∃ n with x^(p^n) ∈ F (by definition of purely inseparable)
    - σ(x)^(p^n) = σ(x^(p^n)) = x^(p^n) (σ fixes F)
    - (σ(x) - x)^(p^n) = 0 by char-p Frobenius identity
    - σ(x) = x since K has no nonzero nilpotents -/
theorem algEquiv_eq_refl_of_isPurelyInseparable {F K : Type*} [Field F] [Field K]
    [Algebra F K] {p : ℕ} [CharP K p] [hp : Fact p.Prime]
    [IsPurelyInseparable F K] (σ : K ≃ₐ[F] K) :
    σ = (AlgEquiv.refl : K ≃ₐ[F] K) := by
  ext x
  show σ x = x
  -- Lift `CharP K p → CharP F p` (Algebra.charP_iff); the `expChar_prime` instance
  -- then gives `ExpChar F p`, which `IsPurelyInseparable.pow_mem` consumes.
  haveI hF_p : CharP F p := (Algebra.charP_iff F K p).mpr inferInstance
  obtain ⟨n, c, hc⟩ : ∃ n : ℕ, ∃ c : F, algebraMap F K c = x ^ p ^ n := by
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem F p x
    obtain ⟨c, hc⟩ := hn
    exact ⟨n, c, hc⟩
  -- σ fixes algebraMap F K c
  have hfixed : σ (x ^ p ^ n) = x ^ p ^ n := by
    rw [← hc]; exact σ.commutes c
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
    (f : F[X]) [hK : IsPurelyInseparable F f.SplittingField] :
    Nat.card f.Gal = 1 := by
  -- Push CharP F p down to CharP f.SplittingField p.
  haveI : CharP f.SplittingField p :=
    (Algebra.charP_iff F f.SplittingField p).mp inferInstance
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun σ τ => (algEquiv_eq_refl_of_isPurelyInseparable σ).trans
                      (algEquiv_eq_refl_of_isPurelyInseparable τ).symm⟩,
          ⟨(AlgEquiv.refl : f.SplittingField ≃ₐ[F] f.SplittingField)⟩⟩

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
  · -- f_target is inseparable: f' = 0, so Separable f_target ⟺ IsCoprime f_target 0
    --                                                       ⟺ IsUnit f_target, contradicting natDegree = 4.
    intro h_sep
    have h_coprime : IsCoprime f_target f_target.derivative := h_sep
    rw [f_derivative_zero, isCoprime_zero_right] at h_coprime
    -- h_coprime : IsUnit f_target
    have hd : f_target.natDegree = 4 := f_target_natDegree
    have hz : f_target.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit h_coprime
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
| `f_target_natDegree` | proved (compute_degree!) |
| `f_target_degree` | proved (compute_degree!) |
| `f_target_ne_zero` | proved (corollary of natDegree) |
| `f_target_monic` | proved (leading coefficient = 1) |
| `g_factor_natDegree` | proved (compute_degree!) |
| `g_factor_degree` | proved (compute_degree!) |
| `g_factor_ne_zero` | proved (corollary of natDegree) |
| `g_factor_monic` | proved (leading coefficient = 1) |
| `f_target_coeff_zero` | proved (coeff 0 = aGen) |
| `f_target_coeff_one` | proved (coeff 1 = 0) |
| `f_target_coeff_two` | proved (coeff 2 = 1) |
| `f_target_coeff_three` | proved (coeff 3 = 0) |
| `f_target_coeff_four` | proved (coeff 4 = 1) |
| `sub_pow_char_pow_eq` | proved (via `iterateFrobenius` and `map_sub`) |
| `algEquiv_eq_refl_of_isPurelyInseparable` | proved |
| `gal_card_one_of_purelyInseparable_splitting` | proved |
| `insep_gal_trivial_refuted` | proved |
| `counterexample_gal_card` | axiom (intentional — Galois count of the explicit f) |
-/

end AngleTrisectionInsepGalCorrect
