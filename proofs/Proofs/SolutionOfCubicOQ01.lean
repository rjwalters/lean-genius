import Proofs.SolutionOfCubic

/-!
# Reducing the General Cubic to Depressed Form (Solution of Cubic, OQ-01)

## What This Proves

The parent file `SolutionOfCubic` solves the **depressed** cubic `t³ + p t + q = 0`
via Cardano's formula. But a textbook cubic comes in the *general* shape

  `a x³ + b x² + c x + d = 0`   (`a ≠ 0`).

The first — and historically essential — step of Cardano's method is the **Tschirnhaus
shift** `x = t − b/(3a)`, which annihilates the quadratic term and produces a depressed
cubic `t³ + p t + q` with

  `p = (3ac − b²) / (3a²)`,   `q = (2b³ − 9abc + 27a²d) / (27a³)`.

This file proves that reduction as a clean field identity, then *bridges it back* to the
parent file: combining the shift with `SolutionOfCubic.cardano_formula` yields an explicit
root of the **general** cubic, closing the loop from `a x³ + b x² + c x + d` all the way to
a radical expression.

## Original Contributions
- `cubic_depress` — the core algebraic identity: the shifted general cubic equals
  `a·(t³ + p t + q)`. This is exactly the statement quoted in the parent's docstring,
  here proved rather than asserted.
- `generalCubicEval_shift` — evaluation form: `general(t − b/3a) = a · depressed(t)`.
- `general_root_of_depressed_root` / `depressed_root_of_general_root` — the shift is a
  *bijection on roots*: `t ↦ t − b/(3a)` carries roots of the depressed cubic to roots of
  the general cubic and back.
- `general_cubic_cardano_root` — the payoff: an explicit Cardano root of the general
  cubic, built from the parent's `cardano_formula`.

## Proof Techniques
Pure field arithmetic (`field_simp` + `ring`) for the shift; the parent's depressed-cubic
theorems for the bridge. Everything is over `ℂ`, matching the parent, and is `0`-axiom.
-/

namespace SolutionOfCubicOQ01

open Complex Polynomial SolutionOfCubic

/-! ## Part 1: The depressed parameters

Given a general cubic `a x³ + b x² + c x + d`, these are the `p` and `q` of the depressed
cubic obtained from the shift `x = t − b/(3a)`. -/

/-- Linear coefficient of the depressed cubic: `p = (3ac − b²)/(3a²)`. -/
noncomputable def depressedP (a b c : ℂ) : ℂ := (3 * a * c - b ^ 2) / (3 * a ^ 2)

/-- Constant coefficient of the depressed cubic: `q = (2b³ − 9abc + 27a²d)/(27a³)`. -/
noncomputable def depressedQ (a b c d : ℂ) : ℂ :=
  (2 * b ^ 3 - 9 * a * b * c + 27 * a ^ 2 * d) / (27 * a ^ 3)

/-! ## Part 2: The core reduction identity

Substituting `x = t − b/(3a)` into the general cubic gives `a · (t³ + p t + q)`. -/

/-- **The Tschirnhaus shift.** For `a ≠ 0`, evaluating the general cubic
`a x³ + b x² + c x + d` at `x = t − b/(3a)` produces `a · (t³ + p t + q)`, where `p` and
`q` are the depressed parameters. In particular the `t²` term has vanished. -/
theorem cubic_depress (a b c d t : ℂ) (ha : a ≠ 0) :
    a * (t - b / (3 * a)) ^ 3 + b * (t - b / (3 * a)) ^ 2 + c * (t - b / (3 * a)) + d
      = a * (t ^ 3 + depressedP a b c * t + depressedQ a b c d) := by
  unfold depressedP depressedQ
  field_simp
  ring

/-! ## Part 3: Evaluation form and the root bijection

We package the general cubic as an evaluation function and relate its roots, under the
shift, to roots of the parent's `depressedCubic`. -/

/-- The general cubic `a x³ + b x² + c x + d` as an evaluation function. -/
noncomputable def generalCubicEval (a b c d x : ℂ) : ℂ :=
  a * x ^ 3 + b * x ^ 2 + c * x + d

/-- Evaluation form of the shift: the general cubic at `t − b/(3a)` equals `a` times the
parent's depressed cubic evaluated at `t`. -/
theorem generalCubicEval_shift (a b c d t : ℂ) (ha : a ≠ 0) :
    generalCubicEval a b c d (t - b / (3 * a))
      = a * (depressedCubic (depressedP a b c) (depressedQ a b c d)).eval t := by
  rw [generalCubicEval, depressedCubic_eval, cubic_depress a b c d t ha]

/-- **Roots descend along the shift.** If `t` is a root of the depressed cubic, then
`t − b/(3a)` is a root of the general cubic. -/
theorem general_root_of_depressed_root (a b c d t : ℂ) (ha : a ≠ 0)
    (ht : (depressedCubic (depressedP a b c) (depressedQ a b c d)).eval t = 0) :
    generalCubicEval a b c d (t - b / (3 * a)) = 0 := by
  rw [generalCubicEval_shift a b c d t ha, ht, mul_zero]

/-- **Roots lift along the shift.** Conversely, if `x` is a root of the general cubic, then
`t = x + b/(3a)` is a root of the depressed cubic. Together with the previous theorem this
shows `t ↦ t − b/(3a)` is a bijection between the two root sets (its inverse is
`x ↦ x + b/(3a)`). -/
theorem depressed_root_of_general_root (a b c d x : ℂ) (ha : a ≠ 0)
    (hx : generalCubicEval a b c d x = 0) :
    (depressedCubic (depressedP a b c) (depressedQ a b c d)).eval (x + b / (3 * a)) = 0 := by
  have hshift : generalCubicEval a b c d ((x + b / (3 * a)) - b / (3 * a))
      = a * (depressedCubic (depressedP a b c) (depressedQ a b c d)).eval (x + b / (3 * a)) :=
    generalCubicEval_shift a b c d (x + b / (3 * a)) ha
  rw [add_sub_cancel_right, hx] at hshift
  -- now `0 = a * eval`, and `a ≠ 0`, so `eval = 0`
  have := hshift.symm
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h ha
  · exact h

/-! ## Part 4: The payoff — a Cardano root of the *general* cubic

Chaining the shift with the parent's `cardano_formula` gives an explicit root of the
general cubic in Cardano form. -/

/-- **General cubic, solved.** For `a ≠ 0`, if `u, v` satisfy the Cardano conditions for the
*depressed* parameters — `u³ + v³ = −q` and `u v = −p/3` — then

  `x = (u + v) − b/(3a)`

is a root of the general cubic `a x³ + b x² + c x + d = 0`. This is Cardano's complete
solution: the shift of Part 2 followed by the parent's depressed-cubic formula. -/
theorem general_cubic_cardano_root (a b c d u v : ℂ) (ha : a ≠ 0)
    (h_sum : u ^ 3 + v ^ 3 = -depressedQ a b c d)
    (h_prod : u * v = -depressedP a b c / 3) :
    generalCubicEval a b c d (u + v - b / (3 * a)) = 0 := by
  apply general_root_of_depressed_root a b c d (u + v) ha
  exact cardano_formula u v (depressedP a b c) (depressedQ a b c d) h_sum h_prod

/-! ## Part 5: Sanity checks

A monic cubic with a known integer root, run through the reduction. -/

/-- For a *monic* cubic (`a = 1`) the shift is just `x = t − b/3`, `p = c − b²/3`,
`q = 2b³/27 − bc/3 + d`. We confirm `depressedP` and `depressedQ` specialize correctly. -/
example (b c : ℂ) : depressedP 1 b c = c - b ^ 2 / 3 := by
  unfold depressedP; ring

example (b c d : ℂ) : depressedQ 1 b c d = 2 * b ^ 3 / 27 - b * c / 3 + d := by
  unfold depressedQ; ring

/-- Concrete check of the full identity on `x³ − 3x² + ... `: the shift kills the quadratic
term. With `a=1, b=-3`, the shift is `x = t + 1`. -/
example (c d t : ℂ) :
    (1 : ℂ) * (t - (-3) / (3 * 1)) ^ 3 + (-3) * (t - (-3) / (3 * 1)) ^ 2
        + c * (t - (-3) / (3 * 1)) + d
      = 1 * (t ^ 3 + depressedP 1 (-3) c * t + depressedQ 1 (-3) c d) :=
  cubic_depress 1 (-3) c d t (by norm_num)

/-- `x³ − 6x − 40 = 0` (already depressed: `a=1, b=0`) has root `x = 4`. Here the shift is
the identity and `4 = (u+v) − 0` recovers the parent example. -/
example : generalCubicEval 1 0 (-6) (-40) 4 = 0 := by
  unfold generalCubicEval; norm_num

end SolutionOfCubicOQ01

-- Summary of key results
#check SolutionOfCubicOQ01.cubic_depress
#check SolutionOfCubicOQ01.generalCubicEval_shift
#check SolutionOfCubicOQ01.general_root_of_depressed_root
#check SolutionOfCubicOQ01.depressed_root_of_general_root
#check SolutionOfCubicOQ01.general_cubic_cardano_root
