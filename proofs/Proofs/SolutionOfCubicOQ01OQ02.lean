import Proofs.SolutionOfCubicOQ01

/-!
# The Discriminant of the General Cubic (Solution of Cubic, OQ-01-OQ-02)

## What This Proves

The parent file `SolutionOfCubicOQ01` reduced the general cubic `a x³ + b x² + c x + d`
(`a ≠ 0`) to depressed form `a·(t³ + p t + q)` via the Tschirnhaus shift, with

  `p = (3ac − b²)/(3a²)`,   `q = (2b³ − 9abc + 27a²d)/(27a³)`,

and the parent's Cardano machinery measures solvability through the **depressed
discriminant** `q²/4 + p³/27`. This file answers the parent's second open question:

> *Formalize the discriminant of the general cubic in terms of `a, b, c, d` and relate it
> to the depressed discriminant `q²/4 + p³/27` used by the parent.*

The classical discriminant of `a x³ + b x² + c x + d` is

  `Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`.

## Original Contributions
- `cubicDisc` — the classical discriminant as a polynomial in `a, b, c, d`.
- `cubicDisc_eq_depressed` — the bridge: `Δ = −108 · a⁴ · (q²/4 + p³/27)`, i.e. the general
  discriminant is, up to the universal factor `−108 a⁴`, exactly the depressed discriminant
  the parent uses. This is the precise sense in which the Tschirnhaus shift preserves the
  discriminant (it scales it by `a⁴` and changes sign convention by `−108`).
- `cubicDisc_eq_zero_iff_depressed` — consequently `Δ = 0 ⟺ q²/4 + p³/27 = 0`, so the two
  discriminants detect a repeated root *simultaneously*.
- `cubicDisc_eq_of_roots` — the root form: if `a x³ + b x² + c x + d = a(x−r)(x−s)(x−t)`
  (Vieta), then `Δ = a⁴·((r−s)(r−t)(s−t))²`, the textbook product-of-squared-differences.
- `cubicDisc_roots_eq_zero_iff` — `Δ = 0 ⟺ two of the roots coincide`, the geometric meaning
  of the discriminant.

## Proof Techniques
Pure field arithmetic (`field_simp` + `ring`) for the bridge; `ring` for the root identity;
`mul_eq_zero` / `sq_eq_zero_iff` / `sub_eq_zero` for the vanishing criteria. Everything is
over `ℂ`, matching the parent, and is `0`-axiom.
-/

namespace SolutionOfCubicOQ01OQ02

open SolutionOfCubicOQ01

/-! ## Part 1: The classical discriminant -/

/-- **The discriminant of the general cubic** `a x³ + b x² + c x + d`:

  `Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`.

This is the standard symmetric polynomial whose vanishing detects a repeated root. -/
def cubicDisc (a b c d : ℂ) : ℂ :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

/-- **The depressed discriminant** `q²/4 + p³/27` used by the parent's Cardano formula.
Its sign decides the number of real roots of the depressed cubic `t³ + p t + q`. -/
noncomputable def depressedDisc (p q : ℂ) : ℂ := q ^ 2 / 4 + p ^ 3 / 27

/-! ## Part 2: The bridge to the depressed discriminant

Substituting the depressed parameters `p = depressedP a b c`, `q = depressedQ a b c d` into
`q²/4 + p³/27` recovers the general discriminant up to the universal factor `−108 a⁴`. -/

/-- **The discriminant bridge.** For `a ≠ 0`, the classical discriminant of the general
cubic equals `−108 · a⁴` times the depressed discriminant `q²/4 + p³/27` of its Tschirnhaus
reduction:

  `Δ = −108 · a⁴ · ( q²/4 + p³/27 )`.

Equivalently `q²/4 + p³/27 = −Δ / (108 a⁴)`. The factor `a⁴` is the expected scaling of a
cubic discriminant under a leading coefficient, and `−108` is the conversion between the two
standard sign conventions (`Δ = a⁴(−4p³ − 27q²)` versus `q²/4 + p³/27`). -/
theorem cubicDisc_eq_depressed (a b c d : ℂ) (ha : a ≠ 0) :
    cubicDisc a b c d
      = -108 * a ^ 4 * depressedDisc (depressedP a b c) (depressedQ a b c d) := by
  unfold cubicDisc depressedDisc depressedP depressedQ
  field_simp
  ring

/-- **The two discriminants vanish together.** For `a ≠ 0`, the general cubic has a repeated
root (`Δ = 0`) exactly when the depressed discriminant vanishes (`q²/4 + p³/27 = 0`). The
Tschirnhaus shift therefore preserves the *repeated-root* locus, as it must, being a
bijection on roots. -/
theorem cubicDisc_eq_zero_iff_depressed (a b c d : ℂ) (ha : a ≠ 0) :
    cubicDisc a b c d = 0
      ↔ depressedDisc (depressedP a b c) (depressedQ a b c d) = 0 := by
  rw [cubicDisc_eq_depressed a b c d ha]
  have hfac : (-108 : ℂ) * a ^ 4 ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero 4 ha
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hfac
  · intro h
    rw [h, mul_zero]

/-! ## Part 3: The root form and the geometric meaning

Writing the cubic in factored form `a(x−r)(x−s)(x−t)` (Vieta), the discriminant becomes the
classical product of squared root differences. -/

/-- **Discriminant in terms of roots (Vieta).** If the general cubic factors as
`a(x − r)(x − s)(x − t)`, so that by Vieta

  `b = −a(r + s + t)`,  `c = a(rs + rt + st)`,  `d = −a·rst`,

then its discriminant is `Δ = a⁴·((r−s)(r−t)(s−t))²` — the leading coefficient to the
fourth power times the squared product of pairwise root differences. -/
theorem cubicDisc_eq_of_roots (a r s t : ℂ) :
    cubicDisc a (-(a * (r + s + t))) (a * (r * s + r * t + s * t)) (-(a * (r * s * t)))
      = a ^ 4 * ((r - s) * (r - t) * (s - t)) ^ 2 := by
  unfold cubicDisc
  ring

/-- **The discriminant detects a repeated root.** With `a ≠ 0` and the cubic in factored
form `a(x − r)(x − s)(x − t)`, the discriminant vanishes precisely when two of the roots
coincide:

  `Δ = 0 ⟺ r = s ∨ r = t ∨ s = t`. -/
theorem cubicDisc_roots_eq_zero_iff (a r s t : ℂ) (ha : a ≠ 0) :
    cubicDisc a (-(a * (r + s + t))) (a * (r * s + r * t + s * t)) (-(a * (r * s * t))) = 0
      ↔ r = s ∨ r = t ∨ s = t := by
  rw [cubicDisc_eq_of_roots a r s t]
  -- `a⁴ = 0` is impossible; what remains is the disjunction over the three differences.
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero 4 ha
  rw [mul_eq_zero, sq_eq_zero_iff, mul_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero, sub_eq_zero]
  -- The product rewrites yield a left-associated disjunction; `tauto` reconciles the
  -- associativity and discharges the `a⁴ = 0` branch using `ha4`.
  tauto

/-! ## Part 4: Sanity checks -/

/-- The depressed discriminant is the `a = 1, b = 0` specialization of the general one:
for an already-depressed cubic `x³ + p x + q` (here `c = p`, `d = q`), the classical formula
collapses to `−4p³ − 27q² = −108·(q²/4 + p³/27)`. -/
example (p q : ℂ) : cubicDisc 1 0 p q = -4 * p ^ 3 - 27 * q ^ 2 := by
  unfold cubicDisc; ring

example (p q : ℂ) : cubicDisc 1 0 p q = -108 * depressedDisc p q := by
  unfold cubicDisc depressedDisc; ring

/-- `x³ − 3x + 2 = (x − 1)²(x + 2)` has a repeated root, so its discriminant is `0`.
(`p = −3, q = 2`: `−4(−27) − 27·4 = 108 − 108 = 0`.) -/
example : cubicDisc 1 0 (-3) 2 = 0 := by
  unfold cubicDisc; norm_num

/-- `x³ − x = x(x−1)(x+1)` has three distinct roots, so its discriminant is nonzero
(`Δ = −4(−1)³ = 4`). -/
example : cubicDisc 1 0 (-1) 0 = 4 := by
  unfold cubicDisc; norm_num

/-- The root form, checked against the distinct-roots example `r,s,t = 0,1,−1`
(`a = 1`): `Δ = ((0−1)(0+1)(1+1))² = (−2)² = 4`. -/
example : cubicDisc 1 (-(1 * ((0:ℂ) + 1 + -1))) (1 * (0 * 1 + 0 * -1 + 1 * -1))
    (-(1 * (0 * 1 * -1))) = 4 := by
  rw [cubicDisc_eq_of_roots]; norm_num

end SolutionOfCubicOQ01OQ02

-- Summary of key results
#check SolutionOfCubicOQ01OQ02.cubicDisc
#check SolutionOfCubicOQ01OQ02.cubicDisc_eq_depressed
#check SolutionOfCubicOQ01OQ02.cubicDisc_eq_zero_iff_depressed
#check SolutionOfCubicOQ01OQ02.cubicDisc_eq_of_roots
#check SolutionOfCubicOQ01OQ02.cubicDisc_roots_eq_zero_iff
