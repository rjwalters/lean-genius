import Mathlib.Tactic

/-
# OQ-03-OQ-04: Newton–Girard Identities for the Cubic

The parent (SolutionOfCubicOQ03.lean) proves Vieta's formulas relating the
three Cardano roots `a, b, c` of a cubic to its elementary symmetric functions

  e₁ = a + b + c,    e₂ = ab + bc + ca,    e₃ = abc.

This file proves the **Newton–Girard identities**, which express the power sums

  pₙ = aⁿ + bⁿ + cⁿ

in terms of e₁, e₂, e₃.  The central result is the *linear recurrence*

  pₙ₊₃ = e₁·pₙ₊₂ − e₂·pₙ₊₁ + e₃·pₙ      (for every n ≥ 0, with p₀ = 3),

which holds because each of `a, b, c` is a root of the monic cubic

  X³ − e₁X² + e₂X − e₃ = (X − a)(X − b)(X − c),

so each satisfies `xⁿ⁺³ = e₁xⁿ⁺² − e₂xⁿ⁺¹ + e₃xⁿ`; summing the three gives the
recurrence.  Everything is a polynomial identity, proved by `ring` /
`linear_combination`, so the development is fully constructive over an arbitrary
commutative ring (0 axioms, 0 sorries, no `native_decide`).

We also record:
  * the closed forms for p₁, p₂, p₃, p₄;
  * the classical Newton identities in "triangular" form (p₃ has the famous
    `+3e₃`, encoding that there are exactly three variables);
  * the specialization to the depressed cubic `X³ + pX + q` of the parent
    (where e₁ = 0), giving `pₙ₊₃ = −p·pₙ₊₁ − q·pₙ` and `a³+b³+c³ = −3q`.
-/

set_option linter.unusedVariables false

namespace SolutionOfCubicOQ03OQ04

variable {R : Type*} [CommRing R]

-- ============================================================
-- SECTION I: Elementary Symmetric Functions and Power Sums
-- ============================================================

/-- First elementary symmetric function: e₁ = a + b + c. -/
def e1 (a b c : R) : R := a + b + c

/-- Second elementary symmetric function: e₂ = ab + bc + ca. -/
def e2 (a b c : R) : R := a * b + b * c + c * a

/-- Third elementary symmetric function: e₃ = abc. -/
def e3 (a b c : R) : R := a * b * c

/-- The `n`-th power sum: pₙ = aⁿ + bⁿ + cⁿ. -/
def powerSum (a b c : R) (n : ℕ) : R := a ^ n + b ^ n + c ^ n

@[simp] theorem powerSum_zero (a b c : R) : powerSum a b c 0 = 3 := by
  unfold powerSum; norm_num

-- ============================================================
-- SECTION II: Each Root Satisfies the Cubic
-- ============================================================

/-- `a` is a root of `X³ − e₁X² + e₂X − e₃`.  Equivalently
`a³ = e₁a² − e₂a + e₃`.  This is the engine of the whole file: the cross terms
in `e₁a² − e₂a + e₃` cancel, leaving exactly `a³`. -/
theorem root_a_cubic (a b c : R) :
    a ^ 3 = e1 a b c * a ^ 2 - e2 a b c * a + e3 a b c := by
  unfold e1 e2 e3; ring

theorem root_b_cubic (a b c : R) :
    b ^ 3 = e1 a b c * b ^ 2 - e2 a b c * b + e3 a b c := by
  unfold e1 e2 e3; ring

theorem root_c_cubic (a b c : R) :
    c ^ 3 = e1 a b c * c ^ 2 - e2 a b c * c + e3 a b c := by
  unfold e1 e2 e3; ring

-- ============================================================
-- SECTION III: Per-Root Recurrences
-- ============================================================

/-- Multiplying `a³ = e₁a² − e₂a + e₃` by `aⁿ` gives the per-root recurrence
`aⁿ⁺³ = e₁aⁿ⁺² − e₂aⁿ⁺¹ + e₃aⁿ`. -/
theorem pow_rec_a (a b c : R) (n : ℕ) :
    a ^ (n + 3) = e1 a b c * a ^ (n + 2) - e2 a b c * a ^ (n + 1) + e3 a b c * a ^ n := by
  unfold e1 e2 e3; ring

theorem pow_rec_b (a b c : R) (n : ℕ) :
    b ^ (n + 3) = e1 a b c * b ^ (n + 2) - e2 a b c * b ^ (n + 1) + e3 a b c * b ^ n := by
  unfold e1 e2 e3; ring

theorem pow_rec_c (a b c : R) (n : ℕ) :
    c ^ (n + 3) = e1 a b c * c ^ (n + 2) - e2 a b c * c ^ (n + 1) + e3 a b c * c ^ n := by
  unfold e1 e2 e3; ring

-- ============================================================
-- SECTION IV: The Newton–Girard Recurrence (main theorem)
-- ============================================================

/-- **Newton–Girard recurrence.** For all `n`, the power sums of `a, b, c`
satisfy

  pₙ₊₃ = e₁·pₙ₊₂ − e₂·pₙ₊₁ + e₃·pₙ.

This single identity, together with `p₀ = 3`, `p₁ = e₁`, `p₂ = e₁² − 2e₂`,
determines every power sum from the elementary symmetric functions.  The proof
sums the three per-root recurrences. -/
theorem newton_recurrence (a b c : R) (n : ℕ) :
    powerSum a b c (n + 3)
      = e1 a b c * powerSum a b c (n + 2)
        - e2 a b c * powerSum a b c (n + 1)
        + e3 a b c * powerSum a b c n := by
  unfold powerSum
  linear_combination pow_rec_a a b c n + pow_rec_b a b c n + pow_rec_c a b c n

/-- The recurrence in the homogeneous range `k ≥ 4`: every power sum is an
`e₁, e₂, e₃`-combination of the previous three.  (Stated as `pₖ₊₄` to make the
`k ≥ 4` hypothesis-free.) -/
theorem newton_recurrence_succ (a b c : R) (n : ℕ) :
    powerSum a b c (n + 4)
      = e1 a b c * powerSum a b c (n + 3)
        - e2 a b c * powerSum a b c (n + 2)
        + e3 a b c * powerSum a b c (n + 1) :=
  newton_recurrence a b c (n + 1)

-- ============================================================
-- SECTION V: Closed Forms and the Triangular Newton Identities
-- ============================================================

theorem powerSum_one (a b c : R) : powerSum a b c 1 = e1 a b c := by
  unfold powerSum e1; ring

theorem powerSum_two (a b c : R) :
    powerSum a b c 2 = e1 a b c ^ 2 - 2 * e2 a b c := by
  unfold powerSum e1 e2; ring

theorem powerSum_three (a b c : R) :
    powerSum a b c 3 = e1 a b c ^ 3 - 3 * e1 a b c * e2 a b c + 3 * e3 a b c := by
  unfold powerSum e1 e2 e3; ring

theorem powerSum_four (a b c : R) :
    powerSum a b c 4
      = e1 a b c ^ 4 - 4 * e1 a b c ^ 2 * e2 a b c
        + 4 * e1 a b c * e3 a b c + 2 * e2 a b c ^ 2 := by
  unfold powerSum e1 e2 e3; ring

/-- Classical Newton identity for `p₁`: `p₁ = e₁`. -/
theorem newton_p1 (a b c : R) : powerSum a b c 1 = e1 a b c :=
  powerSum_one a b c

/-- Classical Newton identity for `p₂`: `p₂ = e₁p₁ − 2e₂`. -/
theorem newton_p2 (a b c : R) :
    powerSum a b c 2 = e1 a b c * powerSum a b c 1 - 2 * e2 a b c := by
  unfold powerSum e1 e2; ring

/-- Classical Newton identity for `p₃`: `p₃ = e₁p₂ − e₂p₁ + 3e₃`.

The constant `+3e₃` (rather than the homogeneous `+e₃·p₀` of higher orders)
records that there are exactly three variables: it is `e₃·p₀` with `p₀ = 3`. -/
theorem newton_p3 (a b c : R) :
    powerSum a b c 3
      = e1 a b c * powerSum a b c 2 - e2 a b c * powerSum a b c 1 + 3 * e3 a b c := by
  unfold powerSum e1 e2 e3; ring

/-- Classical Newton identity for `p₄` (homogeneous, since `4 > 3`):
`p₄ = e₁p₃ − e₂p₂ + e₃p₁`. -/
theorem newton_p4 (a b c : R) :
    powerSum a b c 4
      = e1 a b c * powerSum a b c 3 - e2 a b c * powerSum a b c 2
        + e3 a b c * powerSum a b c 1 := by
  unfold powerSum e1 e2 e3; ring

-- ============================================================
-- SECTION VI: Specialization to the Depressed Cubic X³ + pX + q
-- ============================================================

/-
For the depressed cubic of the parent file the roots satisfy `e₁ = 0`,
`e₂ = p`, `e₃ = −q` (Vieta for `x³ + px + q`).  The Newton recurrence then
collapses to a two-term recurrence, and the cross terms vanish.
-/

/-- **Depressed recurrence.** If `a + b + c = 0`, `ab + bc + ca = p` and
`abc = −q`, then `pₙ₊₃ = −p·pₙ₊₁ − q·pₙ`. -/
theorem depressed_recurrence (a b c p q : R)
    (h1 : a + b + c = 0) (h2 : a * b + b * c + c * a = p) (h3 : a * b * c = -q)
    (n : ℕ) :
    powerSum a b c (n + 3) = -p * powerSum a b c (n + 1) - q * powerSum a b c n := by
  have hrec := newton_recurrence a b c n
  unfold e1 e2 e3 at hrec
  rw [h1, h2, h3] at hrec
  linear_combination hrec

/-- For a depressed cubic the linear power sum vanishes: `p₁ = a + b + c = 0`. -/
theorem depressed_p1 (a b c p q : R) (h1 : a + b + c = 0) :
    powerSum a b c 1 = 0 := by
  unfold powerSum; simpa using h1

/-- For a depressed cubic, `p₂ = a² + b² + c² = −2p`. -/
theorem depressed_p2 (a b c p q : R)
    (h1 : a + b + c = 0) (h2 : a * b + b * c + c * a = p) :
    powerSum a b c 2 = -2 * p := by
  unfold powerSum
  linear_combination (a + b + c) * h1 - 2 * h2

/-- **Sum of cubes of the roots of `x³ + px + q`.** A clean consequence of the
depressed recurrence at `n = 0`: `a³ + b³ + c³ = −3q`.  (When `a, b, c` are the
roots, `a³ + b³ + c³ − 3abc = (a+b+c)(…) = 0`, and `abc = −q`.) -/
theorem depressed_sum_cubes (a b c p q : R)
    (h1 : a + b + c = 0) (h2 : a * b + b * c + c * a = p) (h3 : a * b * c = -q) :
    powerSum a b c 3 = -3 * q := by
  have hr := depressed_recurrence a b c p q h1 h2 h3 0
  simp only [Nat.zero_add] at hr
  rw [depressed_p1 a b c p q h1, powerSum_zero] at hr
  linear_combination hr

end SolutionOfCubicOQ03OQ04
