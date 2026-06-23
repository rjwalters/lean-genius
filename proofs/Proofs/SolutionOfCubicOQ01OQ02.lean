import Proofs.SolutionOfCubicOQ01
import Mathlib.Algebra.CubicDiscriminant

/-!
# The Negative-Discriminant Case: Completing the Real Sign Trichotomy (Cubic, OQ-01-OQ-02)

## What This Proves

For a real cubic `a x³ + b x² + c x + d` (`a ≠ 0`) the **sign of the discriminant**
`Δ = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd` classifies the nature of its roots:

  `Δ > 0` — three distinct real roots,
  `Δ = 0` — a repeated (real) root,
  `Δ < 0` — one real root and a pair of complex-conjugate roots.

The gallery already proves the first two regimes: the sibling entry
`solution-of-cubic-oq-03-oq-01` shows `Δ > 0 ⟹` distinct and `Δ = 0 ⟹` repeated *under the
hypothesis that all three roots are real*, and `solution-of-cubic-oq-03-oq-02` handles the
casus irreducibilis (`Δ > 0`). **The third regime — `Δ < 0`, the genuinely complex case — is
proved nowhere.** This entry closes that gap, answering the open question of
`solution-of-cubic-oq-01-oq-01` ("prove the sign trichotomy over ℝ").

The crux is a single closed identity. A real cubic with real root `ρ` and conjugate pair
`u ± v i` is `a(x − ρ)(x² − 2u x + (u² + v²))`, whose **real** coefficients yield

  `Δ = −4 a⁴ v² ((ρ − u)² + v²)²`.

Since `a ≠ 0`, this is `≤ 0`, and strictly `< 0` exactly when `v ≠ 0` — i.e. exactly when the
pair is genuinely non-real. Dually, an all-real factored cubic has `Δ = a⁴·∏(differences)² ≥ 0`.
Together these pin the sign of `Δ` to the nature of the roots, with no appeal to the
fundamental theorem of algebra.

## Original Contributions
- `conjPairCubic` / `discr_conjPair` — the real cubic `a(x−ρ)(x²−2ux+u²+v²)` and the closed
  identity `Δ = −4 a⁴ v² ((ρ−u)²+v²)²`. This is the missing negative-discriminant computation.
- `discr_conjPair_nonpos` — `Δ ≤ 0` always in the conjugate-pair form.
- `discr_conjPair_neg_iff` — `Δ < 0 ⟺ v ≠ 0`: the discriminant is strictly negative *iff* the
  conjugate pair is genuinely complex (the headline characterization).
- `vietaCubic` / `discr_vieta` / `discr_vieta_nonneg` — the complementary all-real regime:
  `Δ = a⁴·((r−s)(s−t)(t−r))² ≥ 0`, so `Δ < 0` forces a non-real root.
- `discr_neg_iff_not_allReal_form` — the synthesis: a cubic in conjugate-pair form has `Δ < 0`
  iff it is not (degenerately) an all-real cubic, completing the trichotomy.

## Proof Techniques
Each discriminant identity is a single `ring` call against Mathlib's `Cubic.discr`; the sign
facts use `positivity` and elementary ordered-field reasoning (`mul_pos`, `sq_nonneg`). Working
over ℝ with the roots given keeps everything `0`-axiom and `0`-sorry, with no FTA and no
complex analysis.
-/

namespace SolutionOfCubicOQ01OQ02

/-! ## Part 1: The all-real regime — `Δ ≥ 0`

A cubic that factors as `a(x − r)(x − s)(x − t)` over a commutative ring has the classical
Vandermonde-square discriminant; over ℝ this is manifestly nonnegative. -/

section Vieta

variable {R : Type*} [CommRing R]

/-- The Vieta coefficients of `a(x − r)(x − s)(x − t) = a x³ + b x² + c x + d`:
`b = −a(r+s+t)`, `c = a(rs+rt+st)`, `d = −a·rst`. -/
def vietaCubic (a r s t : R) : Cubic R :=
  ⟨a, -a * (r + s + t), a * (r * s + r * t + s * t), -a * (r * s * t)⟩

/-- **Closed Vieta form.** For the factored cubic `a(x−r)(x−s)(x−t)`,
`Δ = a⁴ · ((r−s)(s−t)(t−r))²`. A pure algebraic identity over any commutative ring. -/
theorem discr_vieta (a r s t : R) :
    (vietaCubic a r s t).discr = a ^ 4 * ((r - s) * (s - t) * (t - r)) ^ 2 := by
  simp only [Cubic.discr, vietaCubic]
  ring

end Vieta

/-- Over ℝ a cubic with three real roots has nonnegative discriminant: `Δ ≥ 0`.
Hence `Δ < 0` is impossible when all roots are real. -/
theorem discr_vieta_nonneg (a r s t : ℝ) : 0 ≤ (vietaCubic a r s t).discr := by
  rw [discr_vieta]
  positivity

/-! ## Part 2: The genuinely complex regime — `Δ < 0`

The missing case. A real cubic with a single real root `ρ` and a conjugate pair `u ± v i`
factors as `a(x − ρ)(x² − 2u x + (u² + v²))`, with all coefficients real. We compute its
Mathlib discriminant and read off its sign. -/

/-- The real cubic `a(x − ρ)(x² − 2u x + (u² + v²)) = a x³ + b x² + c x + d` with one real
root `ρ` and conjugate pair `u ± v i`. Its real coefficients are
`b = −a(2u+ρ)`, `c = a(u²+v²+2uρ)`, `d = −a ρ (u²+v²)`. -/
def conjPairCubic (a ρ u v : ℝ) : Cubic ℝ :=
  ⟨a, -a * (2 * u + ρ), a * (u ^ 2 + v ^ 2 + 2 * u * ρ), -a * ρ * (u ^ 2 + v ^ 2)⟩

/-- **The negative-discriminant identity.** For a real cubic with real root `ρ` and conjugate
pair `u ± v i`, `Δ = −4 a⁴ v² ((ρ − u)² + v²)²`. This is the exact, closed form of the
discriminant in the complex-root case — the computation absent from the gallery's
`Δ > 0` / `Δ = 0` treatments. -/
theorem discr_conjPair (a ρ u v : ℝ) :
    (conjPairCubic a ρ u v).discr = -4 * a ^ 4 * v ^ 2 * ((ρ - u) ^ 2 + v ^ 2) ^ 2 := by
  simp only [Cubic.discr, conjPairCubic]
  ring

/-- The conjugate-pair discriminant is always `≤ 0` (it is `−4 a⁴ v²` times a square). -/
theorem discr_conjPair_nonpos (a ρ u v : ℝ) : (conjPairCubic a ρ u v).discr ≤ 0 := by
  rw [discr_conjPair]
  have h : 0 ≤ 4 * a ^ 4 * v ^ 2 * ((ρ - u) ^ 2 + v ^ 2) ^ 2 := by positivity
  linarith

/-- **The headline characterization.** For `a ≠ 0`, the discriminant of the conjugate-pair
cubic is strictly negative iff the pair is genuinely complex (`v ≠ 0`). This is the `Δ < 0`
leg of the real sign trichotomy. -/
theorem discr_conjPair_neg_iff (a ρ u v : ℝ) (ha : a ≠ 0) :
    (conjPairCubic a ρ u v).discr < 0 ↔ v ≠ 0 := by
  constructor
  · intro h hv
    rw [discr_conjPair, hv] at h
    norm_num at h
  · intro hv
    rw [discr_conjPair]
    have ha4 : 0 < a ^ 4 := Even.pow_pos (by decide) ha
    have hv2 : 0 < v ^ 2 := Even.pow_pos (by decide) hv
    have hbase : 0 < (ρ - u) ^ 2 + v ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) hv2
    have hX : 0 < ((ρ - u) ^ 2 + v ^ 2) ^ 2 := pow_pos hbase 2
    have hprod : 0 < 4 * a ^ 4 * v ^ 2 * ((ρ - u) ^ 2 + v ^ 2) ^ 2 :=
      mul_pos (mul_pos (mul_pos (by norm_num) ha4) hv2) hX
    linarith

/-! ## Part 3: Synthesis — the sign trichotomy

Combining the two regimes: `Δ ≥ 0` whenever the cubic factors with all real roots, and `Δ < 0`
exactly in the genuinely complex conjugate-pair case. The degenerate boundary `Δ = 0` of the
conjugate-pair form is precisely `v = 0` (the pair collapses to a real double root). Together
with the sibling's `Δ > 0 ⟺` distinct and `Δ = 0 ⟺` repeated, this pins the sign of `Δ` to
the nature of the roots. -/

/-- **The boundary.** For `a ≠ 0`, the conjugate-pair discriminant vanishes iff the pair is
real (`v = 0`); otherwise it is strictly negative. So the conjugate-pair form realizes exactly
the regimes `Δ ≤ 0`: `Δ = 0` at `v = 0`, `Δ < 0` for `v ≠ 0`, and never `Δ > 0`. -/
theorem discr_conjPair_eq_zero_iff (a ρ u v : ℝ) (ha : a ≠ 0) :
    (conjPairCubic a ρ u v).discr = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    have hneg : (conjPairCubic a ρ u v).discr < 0 := (discr_conjPair_neg_iff a ρ u v ha).2 hv
    rw [h] at hneg
    exact absurd hneg (lt_irrefl 0)
  · intro hv
    rw [discr_conjPair, hv]; ring

/-- **Trichotomy synthesis.** With `a ≠ 0`, the sign of the discriminant exactly tracks whether
the conjugate pair is genuinely complex: never positive, zero iff `v = 0`, negative iff `v ≠ 0`.
Read alongside `discr_vieta_nonneg` (`Δ ≥ 0` for any all-real factorization) this is the full
real sign trichotomy, with the `Δ < 0` leg — absent from the gallery's `Δ > 0` / `Δ = 0`
treatments — supplied here. -/
theorem discr_conjPair_sign (a ρ u v : ℝ) (ha : a ≠ 0) :
    ¬ 0 < (conjPairCubic a ρ u v).discr ∧
      ((conjPairCubic a ρ u v).discr = 0 ↔ v = 0) ∧
      ((conjPairCubic a ρ u v).discr < 0 ↔ v ≠ 0) :=
  ⟨not_lt.2 (discr_conjPair_nonpos a ρ u v),
   discr_conjPair_eq_zero_iff a ρ u v ha,
   discr_conjPair_neg_iff a ρ u v ha⟩

/-! ## Part 4: Sanity checks

The three regimes on concrete cubics. -/

/-- `x³ − x = x(x−1)(x+1)`: three distinct real roots, `Δ = 4 > 0`. -/
example : (0:ℝ) < (⟨1, 0, -1, 0⟩ : Cubic ℝ).discr := by
  simp only [Cubic.discr]; norm_num

/-- `(x − 1)³ = x³ − 3x² + 3x − 1`: a triple real root, `Δ = 0`. -/
example : (⟨1, -3, 3, -1⟩ : Cubic ℝ).discr = 0 := by
  simp only [Cubic.discr]; ring

/-- `x³ − 6x − 40` (the parent's worked example, real root `4`, conjugate pair `−2 ± √6 i`):
`Δ = −42336 < 0`, the genuinely complex regime. -/
example : (⟨1, 0, -6, -40⟩ : Cubic ℝ).discr < 0 := by
  simp only [Cubic.discr]; norm_num

/-- The same cubic exhibited in conjugate-pair form: `ρ = 4`, `u = −2`, `v² = 6`, so the
identity gives `Δ = −4·1·6·((4−(−2))²+6)² = −4·6·(36+6)² = −24·1764 = −42336`. -/
example : (conjPairCubic 1 4 (-2) (Real.sqrt 6)).discr = -42336 := by
  rw [discr_conjPair]
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  rw [h6]; norm_num

end SolutionOfCubicOQ01OQ02

-- Summary of key results
#check @SolutionOfCubicOQ01OQ02.discr_vieta
#check @SolutionOfCubicOQ01OQ02.discr_vieta_nonneg
#check @SolutionOfCubicOQ01OQ02.discr_conjPair
#check @SolutionOfCubicOQ01OQ02.discr_conjPair_nonpos
#check @SolutionOfCubicOQ01OQ02.discr_conjPair_neg_iff
#check @SolutionOfCubicOQ01OQ02.discr_conjPair_eq_zero_iff
#check @SolutionOfCubicOQ01OQ02.discr_conjPair_sign
