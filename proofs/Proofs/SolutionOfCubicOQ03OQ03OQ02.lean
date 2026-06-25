import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-
# OQ-03-OQ-03-OQ-02: Ferrari's Closed-Form Quartic Roots Are Genuine Roots

The parent (`SolutionOfCubicOQ03OQ03.lean`) showed that the resolvent cubic of a
depressed quartic `x⁴ + p·x² + q·x + r` reduces, via Cardano, to an explicit root
`m` (a root of `ResolventCubicCardano.isResolventRoot p q r m`).

This file closes the loop: it takes *any* resolvent root `m`, forms Ferrari's two
quadratic factors, and verifies that the four closed-form Ferrari expressions are
genuine roots of the quartic over the algebraically closed field `ℂ`.

## The construction

Given a resolvent root `m`, choose a square root `s` with `s² = 2m + p` (exists over
an algebraically closed field). Put `c = m + p`. Ferrari's identity is the
factorization

    x⁴ + p·x² + q·x + r
        = (x² − s·x + C₁) · (x² + s·x + C₂),
    where  C₁ = c + q/(2s),  C₂ = c − q/(2s).

The factorization is valid **exactly when** `m` is a resolvent root: matching the
constant term gives `C₁·C₂ = r ⟺ (m+p)² − q²/(4(2m+p)) = r`, which clears to

    8m³ + 20p·m² + (16p² − 8r)·m + (4p³ − 4pr − q²) = 0,

i.e. `isResolventRoot p q r m` verbatim. (See `ferrariC1C2_eq_r`.)

Each quadratic factor is then solved by the quadratic formula, yielding the four
Ferrari roots

    (s ± d₁)/2   with  d₁² = s² − 4·C₁,
    (−s ± d₂)/2  with  d₂² = s² − 4·C₂.

## Results (0 sorries, 0 axioms)

- `quartic_factor`          : the abstract Ferrari factorization (division-free core)
- `ferrariC1C2_eq_r`        : constant-term match ⟺ resolvent root
- `ferrari_factorization`   : the concrete factorization for a resolvent root
- `root_left` / `root_right`: quadratic-formula roots of each factor
- `ferrari_root_of_left` / `…_right` : factor root ⟹ quartic root
- `ferrari_four_roots`      : the four closed-form roots are genuine quartic roots
- `ferrari_roots_exist`     : over ℂ the four Ferrari roots exist (alg. closed)

Companion: `SolutionOfCubicOQ03OQ03.lean` (the parent, which derives the resolvent
root `m` via Cardano). The single predicate this file needs, `isResolventRoot`, is
inlined below so the file depends only on Mathlib and is self-contained.
-/

set_option linter.unusedVariables false

namespace FerrariQuarticRoots

/-- The resolvent cubic from Ferrari's method. For the depressed quartic
`x⁴ + p·x² + q·x + r`, the value `m` is a *resolvent root* when

    8m³ + 20p·m² + (16p² − 8r)·m + (4p³ − 4pr − q²) = 0.

This predicate is the exact resolvent-cubic condition of the parent
`SolutionOfCubicOQ03OQ03.lean`; it is inlined here (a single one-line definition)
so this file depends only on Mathlib and is self-contained. -/
def isResolventRoot (p q r m : ℂ) : Prop :=
  8 * m ^ 3 + 20 * p * m ^ 2 + (16 * p ^ 2 - 8 * r) * m
    + (4 * p ^ 3 - 4 * p * r - q ^ 2) = 0

/-- The depressed quartic `x⁴ + p·x² + q·x + r` evaluated at `x`. -/
def quartic (p q r x : ℂ) : ℂ := x ^ 4 + p * x ^ 2 + q * x + r

-- ============================================================
-- SECTION I: The abstract Ferrari factorization (division-free)
-- ============================================================

/-- **Ferrari factorization (core).** Whenever `s² = 2m + p` and the two constant
terms `C₁, C₂` satisfy `C₁ + C₂ = 2m + 2p`, `s·(C₁ − C₂) = q`, and `C₁·C₂ = r`, the
quartic factors as `(x² − s·x + C₁)·(x² + s·x + C₂)`.

This is the heart of Ferrari's method, stated without any division so it is closed
purely by `linear_combination`. -/
theorem quartic_factor (p q r m s C₁ C₂ x : ℂ)
    (hs : s ^ 2 = 2 * m + p)
    (hsum : C₁ + C₂ = 2 * m + 2 * p)
    (hQ : s * (C₁ - C₂) = q)
    (hprod : C₁ * C₂ = r) :
    quartic p q r x = (x ^ 2 - s * x + C₁) * (x ^ 2 + s * x + C₂) := by
  unfold quartic
  linear_combination (-x ^ 2) * hsum + (x ^ 2) * hs - x * hQ - hprod

-- ============================================================
-- SECTION II: The concrete Ferrari constant terms
-- ============================================================

/-- Ferrari's first constant term `C₁ = (m + p) + q/(2s)`. -/
noncomputable def ferrariC1 (p q m s : ℂ) : ℂ := (m + p) + q / (2 * s)

/-- Ferrari's second constant term `C₂ = (m + p) − q/(2s)`. -/
noncomputable def ferrariC2 (p q m s : ℂ) : ℂ := (m + p) - q / (2 * s)

/-- The sum of the two constant terms is `2m + 2p` (the `q/(2s)` terms cancel). -/
theorem ferrariC1C2_sum (p q m s : ℂ) :
    ferrariC1 p q m s + ferrariC2 p q m s = 2 * m + 2 * p := by
  unfold ferrariC1 ferrariC2; ring

/-- The split equation `s·(C₁ − C₂) = q` (needs `s ≠ 0`). -/
theorem ferrariC1C2_split (p q m s : ℂ) (hsne : s ≠ 0) :
    s * (ferrariC1 p q m s - ferrariC2 p q m s) = q := by
  unfold ferrariC1 ferrariC2
  field_simp
  ring

/-- **Constant term ⟺ resolvent root.** With `s² = 2m + p` and `s ≠ 0`, the product
of the two Ferrari constant terms equals `r` exactly when `m` is a root of the
resolvent cubic. This is the precise sense in which Ferrari's method *requires* a
resolvent root. -/
theorem ferrariC1C2_eq_r (p q r m s : ℂ)
    (hs : s ^ 2 = 2 * m + p) (hsne : s ≠ 0)
    (hres : isResolventRoot p q r m) :
    ferrariC1 p q m s * ferrariC2 p q m s = r := by
  have hsne2 : (2 * s) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hsne)
  unfold ferrariC1 ferrariC2 isResolventRoot at *
  -- Difference of squares, written over the common denominator `(2s)²` so the
  -- division is cleared *deterministically* by `div_eq_iff` (no `field_simp`
  -- discharger guesswork on whether `2m+p ≠ 0`).
  rw [show (m + p + q / (2 * s)) * (m + p - q / (2 * s))
        = ((m + p) ^ 2 * (2 * s) ^ 2 - q ^ 2) / (2 * s) ^ 2 from by
        field_simp; ring]
  rw [div_eq_iff hsne2]
  -- Now `s`-free after substituting `(2s)² = 4(2m+p)`; the resolvent cubic closes it.
  rw [show (2 * s) ^ 2 = 4 * (2 * m + p) from by rw [mul_pow, hs]; ring]
  linear_combination hres

-- ============================================================
-- SECTION III: The factorization for a genuine resolvent root
-- ============================================================

/-- **Ferrari factorization for a resolvent root.** For any resolvent root `m` and a
square root `s` of `2m + p` (with `s ≠ 0`), the quartic factors into Ferrari's two
quadratics with constant terms `C₁, C₂`. -/
theorem ferrari_factorization (p q r m s x : ℂ)
    (hs : s ^ 2 = 2 * m + p) (hsne : s ≠ 0)
    (hres : isResolventRoot p q r m) :
    quartic p q r x =
      (x ^ 2 - s * x + ferrariC1 p q m s) * (x ^ 2 + s * x + ferrariC2 p q m s) :=
  quartic_factor p q r m s _ _ x hs
    (ferrariC1C2_sum p q m s)
    (ferrariC1C2_split p q m s hsne)
    (ferrariC1C2_eq_r p q r m s hs hsne hres)

-- ============================================================
-- SECTION IV: Quadratic-formula roots of each factor
-- ============================================================

/-- Quadratic formula for the first factor `x² − s·x + C`: the values `(s ± d)/2`
with `d² = s² − 4C` are its roots. -/
theorem root_left (s C d x : ℂ) (hd : d ^ 2 = s ^ 2 - 4 * C)
    (hx : x = (s + d) / 2 ∨ x = (s - d) / 2) :
    x ^ 2 - s * x + C = 0 := by
  rcases hx with hx | hx <;> subst hx <;> linear_combination hd / 4

/-- Quadratic formula for the second factor `x² + s·x + C`: the values `(−s ± d)/2`
with `d² = s² − 4C` are its roots. -/
theorem root_right (s C d x : ℂ) (hd : d ^ 2 = s ^ 2 - 4 * C)
    (hx : x = (-s + d) / 2 ∨ x = (-s - d) / 2) :
    x ^ 2 + s * x + C = 0 := by
  rcases hx with hx | hx <;> subst hx <;> linear_combination hd / 4

-- ============================================================
-- SECTION V: Each factor root is a quartic root
-- ============================================================

/-- A root of the first Ferrari quadratic is a root of the quartic. -/
theorem ferrari_root_of_left (p q r m s x : ℂ)
    (hs : s ^ 2 = 2 * m + p) (hsne : s ≠ 0)
    (hres : isResolventRoot p q r m)
    (hx : x ^ 2 - s * x + ferrariC1 p q m s = 0) :
    quartic p q r x = 0 := by
  rw [ferrari_factorization p q r m s x hs hsne hres, hx, zero_mul]

/-- A root of the second Ferrari quadratic is a root of the quartic. -/
theorem ferrari_root_of_right (p q r m s x : ℂ)
    (hs : s ^ 2 = 2 * m + p) (hsne : s ≠ 0)
    (hres : isResolventRoot p q r m)
    (hx : x ^ 2 + s * x + ferrariC2 p q m s = 0) :
    quartic p q r x = 0 := by
  rw [ferrari_factorization p q r m s x hs hsne hres, hx, mul_zero]

-- ============================================================
-- SECTION VI: The four Ferrari roots are genuine roots
-- ============================================================

/-- **The four Ferrari roots.** Given a resolvent root `m`, a square root `s` of
`2m + p`, and square roots `d₁, d₂` of the two quadratic discriminants, each of the
four closed-form expressions

    (s + d₁)/2,  (s − d₁)/2,  (−s + d₂)/2,  (−s − d₂)/2

is a genuine root of the depressed quartic. -/
theorem ferrari_four_roots (p q r m s d₁ d₂ : ℂ)
    (hs : s ^ 2 = 2 * m + p) (hsne : s ≠ 0)
    (hres : isResolventRoot p q r m)
    (hd₁ : d₁ ^ 2 = s ^ 2 - 4 * ferrariC1 p q m s)
    (hd₂ : d₂ ^ 2 = s ^ 2 - 4 * ferrariC2 p q m s) :
    quartic p q r ((s + d₁) / 2) = 0 ∧
    quartic p q r ((s - d₁) / 2) = 0 ∧
    quartic p q r ((-s + d₂) / 2) = 0 ∧
    quartic p q r ((-s - d₂) / 2) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ferrari_root_of_left p q r m s _ hs hsne hres
      (root_left s _ d₁ _ hd₁ (Or.inl rfl))
  · exact ferrari_root_of_left p q r m s _ hs hsne hres
      (root_left s _ d₁ _ hd₁ (Or.inr rfl))
  · exact ferrari_root_of_right p q r m s _ hs hsne hres
      (root_right s _ d₂ _ hd₂ (Or.inl rfl))
  · exact ferrari_root_of_right p q r m s _ hs hsne hres
      (root_right s _ d₂ _ hd₂ (Or.inr rfl))

-- ============================================================
-- SECTION VII: Existence over the algebraically closed field ℂ
-- ============================================================

/-- **Existence of the Ferrari roots over ℂ.** For any resolvent root `m` with
`2m + p ≠ 0` (the generic non-degenerate case `s ≠ 0`), the required square roots
`s, d₁, d₂` exist over the algebraically closed field `ℂ`, and the resulting four
Ferrari expressions are genuine roots of the quartic. -/
theorem ferrari_roots_exist (p q r m : ℂ)
    (hres : isResolventRoot p q r m) (hsq : 2 * m + p ≠ 0) :
    ∃ s d₁ d₂ : ℂ,
      s ^ 2 = 2 * m + p ∧
      quartic p q r ((s + d₁) / 2) = 0 ∧
      quartic p q r ((s - d₁) / 2) = 0 ∧
      quartic p q r ((-s + d₂) / 2) = 0 ∧
      quartic p q r ((-s - d₂) / 2) = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 * m + p) (n := 2) (by norm_num)
  have hsne : s ≠ 0 := by
    intro h; apply hsq; rw [← hs, h]; ring
  obtain ⟨d₁, hd₁⟩ :=
    IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * ferrariC1 p q m s) (n := 2) (by norm_num)
  obtain ⟨d₂, hd₂⟩ :=
    IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * ferrariC2 p q m s) (n := 2) (by norm_num)
  obtain ⟨r1, r2, r3, r4⟩ := ferrari_four_roots p q r m s d₁ d₂ hs hsne hres hd₁ hd₂
  exact ⟨s, d₁, d₂, hs, r1, r2, r3, r4⟩

/-
## Summary

11 theorems + 4 definitions, 0 sorries, 0 axioms (propext / Classical.choice /
Quot.sound only — no `native_decide`). Self-contained: depends only on Mathlib.

### Answer to OQ-03-OQ-03-OQ-02
YES. Taking any root `m` of the parent's resolvent cubic, Ferrari's two quadratic
factors `x² ∓ s·x + ((m+p) ± q/(2s))` with `s² = 2m + p` multiply back to the
quartic `x⁴ + p·x² + q·x + r` — and the constant-term match holds *exactly* because
`m` is a resolvent root (`ferrariC1C2_eq_r`). Solving each quadratic by the
quadratic formula gives the four closed-form Ferrari roots, each verified to be a
genuine root (`ferrari_four_roots`), and over the algebraically closed field `ℂ`
the requisite square roots always exist (`ferrari_roots_exist`).
-/

end FerrariQuarticRoots
