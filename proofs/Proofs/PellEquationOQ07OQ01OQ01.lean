/-
Pell's Equation OQ-07 → OQ-01 → OQ-01: The Cassini / Catalan Identity from det(Mⁿ) = (det M)ⁿ

The grandparent (`pell-equation-oq-07`) shows each coordinate of the power sequence
`aⁿ` of a generator `a = ⟨x₁, y₁⟩ ∈ ℤ√d` obeys the second-order recurrence

    uₙ₊₂ = (2·x₁)·uₙ₊₁ − N(a)·uₙ                       (Cayley–Hamilton recurrence)

and the parent (`pell-equation-oq-07-oq-01`) realises the two coordinates as the
powers of the companion matrix `M = !![x₁, d·y₁; y₁, x₁]`, with `Mⁿ =
!![re(aⁿ), d·im(aⁿ); im(aⁿ), re(aⁿ)]` and `det M = N(a)`.

This entry supplies the **Cassini / Catalan-type identity** that the companion
determinant produces. Two determinant phenomena are recorded:

## 1. The norm identity — the *direct* consequence of `det(Mⁿ) = (det M)ⁿ`

Because `det` is multiplicative, `det(Mⁿ) = (det M)ⁿ = N(a)ⁿ`. Reading `det(Mⁿ)`
off the parent's explicit power form gives the classical norm identity

    re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ,

i.e. `N(aⁿ) = N(a)ⁿ` made visible as a 2×2 determinant. This is `norm_pow_eq`.

## 2. The Cassini identity — the determinant of the *state* matrix

For a Pell-type sequence the genuinely Cassini-flavoured quantity is the "off-by-one"
determinant `uₙ₋₁·uₙ₊₁ − uₙ²`. This is the determinant of the state matrix
`W k = !![u(k+2), u(k+1); u(k+1), u k]`, whose columns are consecutive state
vectors of the recurrence. The recurrence companion `C = !![p, −q; 1, 0]` (with
`p = 2x₁`, `q = N(a)`, `det C = q`) advances the state, so `W k = Cᵏ·W₀` and hence

    det(W k) = (det C)ᵏ · det(W₀) = qᵏ · det(W₀),    i.e.
    u(k+2)·u(k) − u(k+1)² = N(a)ᵏ · (u₀·u₂ − u₁²).

We prove this general Cassini/Catalan identity over any commutative ring
(`cassini_general`), package it as the determinant statement `det(W k) = qᵏ·det(W₀)`
(`cassini_det_general`), then specialise to the Pell coordinate sequences
`re(aⁿ)` and `im(aⁿ)` using the grandparent's recurrences.

## The Pell punchline: a *constant* invariant

For a Pell generator (`N(a) = 1`) the factor `qᵏ = 1` disappears, so both
Cassini quantities are **constant in `k`**:

    re(aₖ₊₁)·re(aₖ₋₁) − re(aₖ)² = d·y₁²           (`re_cassini_pell`)
    im(aₖ₊₁)·im(aₖ₋₁) − im(aₖ)² = −y₁²            (`im_cassini_pell`)

exactly as `Fₙ₋₁Fₙ₊₁ − Fₙ² = (−1)ⁿ` is constant (up to sign) for Fibonacci. For the
`D = 2` chain `1,3,17,99,…` this reads `xₖ₊₁xₖ₋₁ − xₖ² = 8`.

## Main results

* `cassini_general` — over any `CommRing`, `u(k+2)·u(k) − u(k+1)² = qᵏ·(u₂u₀ − u₁²)`
  for a sequence with `u(n+2) = p·u(n+1) − q·u(n)` (proved by the `D(k+1) = q·D(k)`
  recurrence for the Cassini defect).
* `cassini_det_general` — the same identity as a determinant of the state matrix,
  `det !![u(k+2),u(k+1);u(k+1),u k] = qᵏ·det !![u 2,u 1;u 1,u 0]`.
* `re_cassini` / `im_cassini` — the Pell specialisations, with `re_cassini_const`
  and `im_cassini_const` evaluating the base defect to `d·y₁²` and `−y₁²`.
* `re_cassini_pell` / `im_cassini_pell` — the constant invariants for `N(a) = 1`.
* `norm_pow_eq` — `re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ` straight from `det(Mⁿ) = (det M)ⁿ`
  via the parent's `companion_pow` and `Matrix.det_pow`.
* `D = 2` numeric checks against `1,3,17,99` / `0,2,12,70`.

All proofs are `sorry`-free and axiom-free (the `decide` uses are kernel `decide`,
not `native_decide`).

References:
- Grandparent: `pell-equation-oq-07` (the coordinate recurrences `re_recurrence`,
  `im_recurrence`).
- Parent: `pell-equation-oq-07-oq-01` (`companion`, `companion_pow`, `companion_det`).
- Cassini/Catalan: the identity `Fₙ₋₁Fₙ₊₁ − Fₙ² = (−1)ⁿ` and its generalisation to
  any second-order linear recurrence via the companion-matrix determinant.
-/

import Proofs.PellEquationOQ07OQ01

namespace PellEquationOQ07OQ01OQ01

open Zsqrtd PellEquationOQ07OQ01

/-
## The general Cassini / Catalan identity over a commutative ring

For any sequence `u : ℕ → R` obeying the second-order recurrence
`u(n+2) = p·u(n+1) − q·u(n)`, the "Cassini defect" `D(k) = u(k+2)·u(k) − u(k+1)²`
satisfies `D(k+1) = q·D(k)`: substituting the recurrence for the two highest terms
makes the difference `D(k+1) − q·D(k)` collapse to `u(k+2)·(p·u(k+1) − q·u(k) −
u(k+2)) = 0`. Induction then gives `D(k) = qᵏ·D(0)`.
-/

/-- **General Cassini / Catalan identity.** For a sequence satisfying the second-order
recurrence `u(n+2) = p·u(n+1) − q·u(n)`, the off-by-one product minus square is
`qᵏ` times its base value:
`u(k+2)·u(k) − u(k+1)² = qᵏ·(u₂·u₀ − u₁²)`. Specialising to `Fₙ` (with `p = 1`,
`q = −1`) recovers `Fₙ₊₁Fₙ₋₁ − Fₙ² = (−1)ⁿ`. -/
theorem cassini_general {R : Type*} [CommRing R] (u : ℕ → R) (p q : R)
    (hrec : ∀ n, u (n + 2) = p * u (n + 1) - q * u n) (k : ℕ) :
    u (k + 2) * u k - u (k + 1) ^ 2 = q ^ k * (u 2 * u 0 - u 1 ^ 2) := by
  -- The Cassini defect satisfies the one-step scaling `D(m+1) = q·D(m)`.
  have hD : ∀ m, u (m + 3) * u (m + 1) - u (m + 2) ^ 2
      = q * (u (m + 2) * u m - u (m + 1) ^ 2) := by
    intro m
    have h1 : u (m + 3) = p * u (m + 2) - q * u (m + 1) := hrec (m + 1)
    have h2 : u (m + 2) = p * u (m + 1) - q * u m := hrec m
    linear_combination u (m + 1) * h1 - u (m + 2) * h2
  induction k with
  | zero => simp
  | succ n ih =>
    show u (n + 3) * u (n + 1) - u (n + 2) ^ 2 = q ^ (n + 1) * (u 2 * u 0 - u 1 ^ 2)
    rw [hD n, ih, pow_succ]; ring

/-- **The Cassini identity as a determinant.** The Cassini defect is the determinant
of the state matrix `W k = !![u(k+2), u(k+1); u(k+1), u k]` (whose columns are the
consecutive state vectors of the recurrence), and `det(W k) = qᵏ·det(W 0)` — the
determinant form of `W k = Cᵏ·W 0` for the recurrence companion `C = !![p,−q;1,0]`
with `det C = q`. -/
theorem cassini_det_general {R : Type*} [CommRing R] (u : ℕ → R) (p q : R)
    (hrec : ∀ n, u (n + 2) = p * u (n + 1) - q * u n) (k : ℕ) :
    (!![u (k + 2), u (k + 1); u (k + 1), u k] : Matrix (Fin 2) (Fin 2) R).det
      = q ^ k * (!![u 2, u 1; u 1, u 0] : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  linear_combination cassini_general u p q hrec k

/-
## Specialisation to the Pell coordinate sequences

The grandparent shows `re(aⁿ)` and `im(aⁿ)` both obey `uₙ₊₂ = (2·re a)·uₙ₊₁ −
N(a)·uₙ`, i.e. the recurrence with `p = 2·re a`, `q = N(a)`. Feeding these into
`cassini_general` gives the Cassini identities for each coordinate.
-/

/-- **Cassini identity for the real coordinate.** `re(aₖ₊₁)·re(aₖ₋₁) − re(aₖ)² =
N(a)ᵏ·(re(a²)·re(a⁰) − re(a¹)²)`, from the grandparent's `re_recurrence`. -/
theorem re_cassini {d : ℤ} (a : ℤ√d) (k : ℕ) :
    (a ^ (k + 2)).re * (a ^ k).re - (a ^ (k + 1)).re ^ 2
      = a.norm ^ k * ((a ^ 2).re * (a ^ 0).re - (a ^ 1).re ^ 2) :=
  cassini_general (fun n => (a ^ n).re) (2 * a.re) a.norm
    (fun n => PellEquationOQ07.Zsqrtd.re_recurrence a n) k

/-- **Cassini identity for the `√d` coordinate.** `im(aₖ₊₁)·im(aₖ₋₁) − im(aₖ)² =
N(a)ᵏ·(im(a²)·im(a⁰) − im(a¹)²)`, from the grandparent's `im_recurrence`. -/
theorem im_cassini {d : ℤ} (a : ℤ√d) (k : ℕ) :
    (a ^ (k + 2)).im * (a ^ k).im - (a ^ (k + 1)).im ^ 2
      = a.norm ^ k * ((a ^ 2).im * (a ^ 0).im - (a ^ 1).im ^ 2) :=
  cassini_general (fun n => (a ^ n).im) (2 * a.re) a.norm
    (fun n => PellEquationOQ07.Zsqrtd.im_recurrence a n) k

/-- The base Cassini defect for the real coordinate evaluates to `d·y₁²`, using
`re(a²) = x₁² + d·y₁²`, `re(a⁰) = 1`, `re(a¹) = x₁`. -/
theorem re_cassini_const {d : ℤ} (a : ℤ√d) :
    (a ^ 2).re * (a ^ 0).re - (a ^ 1).re ^ 2 = d * a.im ^ 2 := by
  have h2 : (a ^ 2).re = a.re ^ 2 + d * a.im ^ 2 := by
    rw [pow_two, Zsqrtd.re_mul]; ring
  rw [h2, pow_zero, pow_one, Zsqrtd.re_one]; ring

/-- The base Cassini defect for the `√d` coordinate evaluates to `−y₁²`, using
`im(a²) = 2·x₁·y₁`, `im(a⁰) = 0`, `im(a¹) = y₁`. -/
theorem im_cassini_const {d : ℤ} (a : ℤ√d) :
    (a ^ 2).im * (a ^ 0).im - (a ^ 1).im ^ 2 = -a.im ^ 2 := by
  have h2 : (a ^ 2).im = 2 * a.re * a.im := by
    rw [pow_two, Zsqrtd.im_mul]; ring
  rw [h2, pow_zero, pow_one, Zsqrtd.im_one]; ring

/-- **The constant Cassini invariant for a Pell generator (real part).** When
`N(a) = 1` the scaling factor `N(a)ᵏ` vanishes, so the Cassini defect is *constant
in `k`*: `re(aₖ₊₁)·re(aₖ₋₁) − re(aₖ)² = d·y₁²` for all `k`. -/
theorem re_cassini_pell {d : ℤ} (a : ℤ√d) (h : a.norm = 1) (k : ℕ) :
    (a ^ (k + 2)).re * (a ^ k).re - (a ^ (k + 1)).re ^ 2 = d * a.im ^ 2 := by
  rw [re_cassini, re_cassini_const, h, one_pow, one_mul]

/-- **The constant Cassini invariant for a Pell generator (`√d` part).** When
`N(a) = 1` the Cassini defect of the `√d`-coordinate sequence is the constant
`−y₁²` for all `k`. -/
theorem im_cassini_pell {d : ℤ} (a : ℤ√d) (h : a.norm = 1) (k : ℕ) :
    (a ^ (k + 2)).im * (a ^ k).im - (a ^ (k + 1)).im ^ 2 = -a.im ^ 2 := by
  rw [im_cassini, im_cassini_const, h, one_pow, one_mul]

/-
## The norm identity, straight from `det(Mⁿ) = (det M)ⁿ`

The parent's companion matrix `M = companion a` has `Mⁿ = !![re(aⁿ), d·im(aⁿ);
im(aⁿ), re(aⁿ)]` (`companion_pow`) and `det M = N(a)` (`companion_det`). Since
`det` is multiplicative, `det(Mⁿ) = (det M)ⁿ = N(a)ⁿ` (`Matrix.det_pow`); reading
`det(Mⁿ)` off the explicit power form gives the norm identity.
-/

/-- **The norm identity `N(aⁿ) = N(a)ⁿ` as a determinant.** Directly from
`det(Mⁿ) = (det M)ⁿ`: `re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ`. The left side is `det(Mⁿ)`
via the parent's `companion_pow`, the right is `(det M)ⁿ` via `Matrix.det_pow` and
`companion_det`. -/
theorem norm_pow_eq {d : ℤ} (a : ℤ√d) (n : ℕ) :
    (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 = a.norm ^ n := by
  have h1 : (companion a ^ n).det = (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 := by
    rw [companion_pow, Matrix.det_fin_two_of]; ring
  have h2 : (companion a ^ n).det = a.norm ^ n := by
    rw [Matrix.det_pow, companion_det]
  rw [← h1, h2]

/-
## Concrete `D = 2` checks

The fundamental unit of `ℤ[√2]` is `3 + 2√2 = ⟨3,2⟩` (norm `1`). Its power sequence
begins `1,3,17,99` (real part) and `0,2,12,70` (`√2` part). The real Cassini
invariant is `d·y₁² = 2·2² = 8`; the `√2` invariant is `−y₁² = −4`; the norm
identity gives `1` at every power.
-/

/-- The real-part base defect for `3 + 2√2`: `re(a²)·re(a⁰) − re(a¹)² = 17·1 − 9 = 8`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 2).re * ((⟨3, 2⟩ : ℤ√2) ^ 0).re
    - ((⟨3, 2⟩ : ℤ√2) ^ 1).re ^ 2 = 8 := by decide

/-- The `√2`-part base defect for `3 + 2√2`: `im(a²)·im(a⁰) − im(a¹)² = 12·0 − 4 = −4`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 2).im * ((⟨3, 2⟩ : ℤ√2) ^ 0).im
    - ((⟨3, 2⟩ : ℤ√2) ^ 1).im ^ 2 = -4 := by decide

/-- The norm identity at `n = 2`: `re(a²)² − 2·im(a²)² = 17² − 2·12² = 289 − 288 = 1`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 2).re ^ 2 - 2 * ((⟨3, 2⟩ : ℤ√2) ^ 2).im ^ 2 = 1 := by decide

/-- The real Cassini invariant is the **constant** `8` for every `k` (norm-`1`
collapse of `re_cassini_pell`, evaluated at `d = 2`, `y₁ = 2`). -/
example (k : ℕ) : ((⟨3, 2⟩ : ℤ√2) ^ (k + 2)).re * ((⟨3, 2⟩ : ℤ√2) ^ k).re
    - ((⟨3, 2⟩ : ℤ√2) ^ (k + 1)).re ^ 2 = 8 := by
  have h : ((⟨3, 2⟩ : ℤ√2).im : ℤ) = 2 := rfl
  rw [re_cassini_pell _ PellEquationOQ07.norm_three_two, h]; norm_num

#check @cassini_general
#check @cassini_det_general
#check @re_cassini
#check @im_cassini
#check @re_cassini_pell
#check @im_cassini_pell
#check @norm_pow_eq

end PellEquationOQ07OQ01OQ01
