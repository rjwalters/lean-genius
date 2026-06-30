import Proofs.SolutionOfCubicOQ01

/-!
# The Discriminant of the General Cubic and its Invariance under the Tschirnhaus Shift (Solution of Cubic, OQ-01-OQ-01)

## What This Proves

The parent file `SolutionOfCubicOQ01` proves the **Tschirnhaus shift** `x = t - b/(3a)`
reduces the general cubic `a x³ + b x² + c x + d` to depressed form `a·(t³ + p t + q)`
with `p = (3ac - b²)/(3a²)` and `q = (2b³ - 9abc + 27a²d)/(27a³)`. That parent's docstring
left as an open question:

  *"Formalize the discriminant of the general cubic in terms of a, b, c, d and relate it to
  the depressed discriminant used by the parent."*

This file answers exactly that. We define the classical **general cubic discriminant**

  `Δ(a,b,c,d) = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`

and prove the central structural fact: the Tschirnhaus shift carries it to the depressed
polynomial discriminant up to the factor `a⁴`,

  `Δ(a,b,c,d) = a⁴ · (−4p³ − 27q²)`.

Geometrically, the discriminant of a degree-`n` polynomial scales by `a^(2n−2)` under a unit
factor (`a⁴` for `n = 3`) and is **invariant under translation** `x ↦ t − b/(3a)`; both facts
are visible in this single identity. We then bridge to the parent's Cardano discriminant
`Δ_C = q²/4 + p³/27` (the quantity under the square root of Cardano's formula), establish the
repeated-root criterion `Δ = 0`, and express `Δ` in the symmetric **root form**
`a⁴·∏_{i<j}(xᵢ − xⱼ)²`.

## Original Contributions
- `generalDiscriminant` — the discriminant of `a x³ + b x² + c x + d` as a polynomial in
  `a, b, c, d`.
- `general_discriminant_eq_shift` — the headline: `Δ = a⁴ · (−4p³ − 27q²)`, the shift's
  effect on the discriminant. This is the discriminant analogue of the parent's `cubic_depress`.
- `depressedDisc_eq_cardano` / `general_discriminant_eq_cardano` — bridge to the parent's
  Cardano discriminant `q²/4 + p³/27`: `−4p³ − 27q² = −108·(q²/4 + p³/27)`, so
  `Δ = −108·a⁴·Δ_C`.
- `general_discriminant_eq_zero_iff` — the shift preserves the repeated-root locus:
  `Δ = 0 ⟺ −4p³ − 27q² = 0` (because `a ≠ 0`).
- `generalDiscriminant_eq_root_form` — symmetric form: for a monic-times-`a` cubic with roots
  `x₁, x₂, x₃` (Vieta), `Δ = a⁴·((x₁−x₂)(x₁−x₃)(x₂−x₃))²`.
- `repeated_root_iff` — `Δ = 0 ⟺ two of the roots coincide`, the geometric meaning of the
  discriminant.

## Proof Techniques
The shift identity is a single field identity (`field_simp` clears the denominators of `p, q`
using `a ≠ 0`, then `ring`). The root form is a pure polynomial identity (`ring` after
substituting Vieta). The vanishing criteria use `a⁴ ≠ 0` (`pow_ne_zero`) and
`NoZeroDivisors`. Everything is over `ℂ`, matching the parent, and is `0`-axiom.
-/

namespace SolutionOfCubicOQ01OQ01

open SolutionOfCubic SolutionOfCubicOQ01

/-! ## Part 1: The general cubic discriminant

The discriminant of `a x³ + b x² + c x + d`, a polynomial in its four coefficients. -/

/-- **The discriminant of the general cubic** `a x³ + b x² + c x + d`:
`Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`. -/
def generalDiscriminant (a b c d : ℂ) : ℂ :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

/-- The **polynomial discriminant** of the depressed cubic `t³ + p t + q`: `−4p³ − 27q²`.
(This is the standard discriminant; it differs from the parent's Cardano discriminant
`q²/4 + p³/27` by the factor `−108`, see `depressedDisc_eq_cardano`.) -/
def depressedDisc (p q : ℂ) : ℂ := -4 * p ^ 3 - 27 * q ^ 2

/-! ## Part 2: The shift identity — the discriminant under depression

Substituting the depressed parameters `p, q` of the Tschirnhaus shift shows the general
discriminant is `a⁴` times the depressed discriminant. -/

/-- **The discriminant under the Tschirnhaus shift.** For `a ≠ 0`, the general cubic
discriminant equals `a⁴` times the depressed polynomial discriminant of the shifted cubic:

  `Δ(a,b,c,d) = a⁴ · (−4p³ − 27q²)`,   `p = depressedP a b c`, `q = depressedQ a b c d`.

The `a⁴` is the `a^(2·3−2)` scaling of a cubic discriminant under a leading factor; the rest
is the *translation invariance* of the discriminant under `x = t − b/(3a)`. This is the
discriminant analogue of the parent's coefficient identity `cubic_depress`. -/
theorem general_discriminant_eq_shift (a b c d : ℂ) (ha : a ≠ 0) :
    generalDiscriminant a b c d
      = a ^ 4 * depressedDisc (depressedP a b c) (depressedQ a b c d) := by
  unfold generalDiscriminant depressedDisc depressedP depressedQ
  field_simp
  ring

/-! ## Part 3: Bridge to the parent's Cardano discriminant

The parent uses `Δ_C = q²/4 + p³/27` (the radicand of Cardano's formula). The polynomial
discriminant is `−108` times it. -/

/-- The depressed polynomial discriminant is `−108` times the parent's Cardano discriminant
`Δ_C = q²/4 + p³/27`. So the two notions of "discriminant" agree up to a nonzero constant and
in particular vanish together. -/
theorem depressedDisc_eq_cardano (p q : ℂ) :
    depressedDisc p q = -108 * SolutionOfCubic.discriminant p q := by
  unfold depressedDisc SolutionOfCubic.discriminant
  ring

/-- The general discriminant in terms of the parent's Cardano discriminant of the depressed
cubic: `Δ(a,b,c,d) = −108 · a⁴ · (q²/4 + p³/27)`. This is the explicit link the parent's
open question asked for. -/
theorem general_discriminant_eq_cardano (a b c d : ℂ) (ha : a ≠ 0) :
    generalDiscriminant a b c d
      = -108 * a ^ 4 *
          SolutionOfCubic.discriminant (depressedP a b c) (depressedQ a b c d) := by
  rw [general_discriminant_eq_shift a b c d ha, depressedDisc_eq_cardano]
  ring

/-! ## Part 4: The repeated-root locus is shift-invariant

`Δ = 0` exactly when the depressed discriminant vanishes — the shift moves roots but not the
condition that two of them collide. -/

/-- **The shift preserves the repeated-root locus.** Since `a ≠ 0`, the general cubic has
`Δ = 0` iff its depressed form has `−4p³ − 27q² = 0`. -/
theorem general_discriminant_eq_zero_iff (a b c d : ℂ) (ha : a ≠ 0) :
    generalDiscriminant a b c d = 0
      ↔ depressedDisc (depressedP a b c) (depressedQ a b c d) = 0 := by
  rw [general_discriminant_eq_shift a b c d ha]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero 4 ha)
    · exact h'
  · intro h
    rw [h, mul_zero]

/-! ## Part 5: The symmetric root form

For a cubic `a(x − x₁)(x − x₂)(x − x₃)` — i.e. coefficients given by Vieta — the discriminant
is `a⁴` times the squared product of root differences. -/

/-- **Root form of the discriminant.** If `b, c, d` are the Vieta coefficients of the roots
`x₁, x₂, x₃` (so `a x³ + b x² + c x + d = a(x−x₁)(x−x₂)(x−x₃)`), then

  `Δ(a,b,c,d) = a⁴ · ((x₁−x₂)(x₁−x₃)(x₂−x₃))²`.

This is the classical symmetric expression; it makes manifest that `Δ` is a square (up to
`a⁴`) and that it vanishes exactly when two roots coincide. -/
theorem generalDiscriminant_eq_root_form (a x₁ x₂ x₃ b c d : ℂ)
    (hb : b = -a * (x₁ + x₂ + x₃))
    (hc : c = a * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hd : d = -a * (x₁ * x₂ * x₃)) :
    generalDiscriminant a b c d = a ^ 4 * ((x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃)) ^ 2 := by
  subst hb hc hd
  unfold generalDiscriminant
  ring

/-- **The discriminant detects repeated roots.** For `a ≠ 0` and `x₁, x₂, x₃` the roots
(via Vieta), `Δ = 0` iff two of the roots coincide. -/
theorem repeated_root_iff (a x₁ x₂ x₃ b c d : ℂ) (ha : a ≠ 0)
    (hb : b = -a * (x₁ + x₂ + x₃))
    (hc : c = a * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hd : d = -a * (x₁ * x₂ * x₃)) :
    generalDiscriminant a b c d = 0 ↔ (x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃) := by
  rw [generalDiscriminant_eq_root_form a x₁ x₂ x₃ b c d hb hc hd]
  constructor
  · intro h
    have hsq : ((x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (pow_ne_zero 4 ha)
      · exact h'
    have hp : (x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃) = 0 := sq_eq_zero_iff.mp hsq
    rcases mul_eq_zero.mp hp with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact Or.inl (sub_eq_zero.mp h3)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h2))
  · intro h
    rcases h with h | h | h <;> subst h <;> ring

/-! ## Part 6: Sanity checks -/

/-- With `a = 1, b = 0` the cubic is already depressed (`p = c`, `q = d`), and the general
discriminant reduces to the depressed discriminant `−4c³ − 27d²`. -/
example (c d : ℂ) : generalDiscriminant 1 0 c d = depressedDisc c d := by
  unfold generalDiscriminant depressedDisc; ring

/-- The depressed cubic `t³ − 6t − 40` (the parent's worked example, root `t = 4`) has
discriminant `−4·(−6)³ − 27·(−40)² = 864 − 43200 = −42336 ≠ 0`, so its roots are distinct. -/
example : generalDiscriminant 1 0 (-6) (-40) = -42336 := by
  unfold generalDiscriminant; norm_num

/-- A perfect cube `(x − 2)³ = x³ − 6x² + 12x − 8` has a triple root, so `Δ = 0`. -/
example : generalDiscriminant 1 (-6) 12 (-8) = 0 := by
  unfold generalDiscriminant; norm_num

end SolutionOfCubicOQ01OQ01

-- Summary of key results
#check SolutionOfCubicOQ01OQ01.general_discriminant_eq_shift
#check SolutionOfCubicOQ01OQ01.general_discriminant_eq_cardano
#check SolutionOfCubicOQ01OQ01.general_discriminant_eq_zero_iff
#check SolutionOfCubicOQ01OQ01.generalDiscriminant_eq_root_form
#check SolutionOfCubicOQ01OQ01.repeated_root_iff
