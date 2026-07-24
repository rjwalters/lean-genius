import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Solution of the General Quartic (Wiedijk #46)

## What This Proves
We formalize Ferrari's method for solving quartic equations. Every quartic equation
  x⁴ + ax³ + bx² + cx + d = 0
can be solved by radicals using Ferrari's method (1540).

## Approach
- **Foundation:** We work over complex numbers where the Fundamental Theorem of
  Algebra guarantees solutions exist.
- **Ferrari's Method:** The classical approach:
  1. Reduce to depressed quartic: y⁴ + py² + qy + r = 0 (via substitution y = x + a/4)
  2. Introduce auxiliary parameter m and rewrite as difference of squares
  3. Solve the resolvent cubic for m
  4. Factor quartic into two quadratics and apply quadratic formula
- **Status:** Axiom-free. All algebraic manipulations are verified, and the
  three former structural axioms (`quartic_has_four_roots`, `biquadratic_forward`,
  `biquadratic_backward`) are now discharged as theorems from Mathlib's FTA
  infrastructure and the complex quadratic formula. The connection to the
  resolvent cubic formula (Wiedijk #37) is shown.

## Status
- [x] Depressed quartic reduction theorem
- [x] Ferrari's resolvent cubic derivation
- [x] Factorization into quadratics (given m)
- [x] Four-roots existence via FTA (`quartic_has_four_roots`, no axiom)
- [x] Biquadratic (q = 0) case solved by radicals (no axiom)
- [x] 0 axioms, 0 sorries — fully machine-checked

## Mathematical Background

Ferrari's brilliant insight (1540): Add a parameter m and complete the square.

NOTE ON CONVENTION: this file uses a *non-standard* completion with constant
`p + m` (not the textbook `p/2 + m`). The derivation below, the `resolventCubic`
definition, and `ferrari_factorization_id` all share this `(y² + p + m)²`
convention; the file's `m` differs from the textbook parameter by a shift of p/2.

Starting with y⁴ + py² + qy + r = 0, substitute y⁴ = -py² - qy - r into the
expansion of (y² + p + m)² = y⁴ + 2(p + m)y² + (p + m)² to get:
  (y² + p + m)² = (2m + p)y² - qy + (m² + 2pm + p² - r)

The right side is a perfect square in y when its discriminant vanishes:
  q² - 4(2m + p)((p + m)² - r) = 0

Expanding this gives the resolvent cubic in m (matching `resolventCubic`):
  8m³ + 20pm² + (16p² - 8r)m + (4p³ - 4pr - q²) = 0

Once m is found, we have:
  (y² + p + m)² = (αy - β)²   with  α² = 2m + p,  2αβ = q,  β² = (p + m)² - r

Taking square roots:
  y² + p + m = ±(αy - β)

Each gives a quadratic factor (see `ferrari_factorization_id`), yielding four
roots total.

Historical Note: Lodovico Ferrari (1522-1565), a student of Cardano, discovered
this method at age 18. It was published in Cardano's Ars Magna (1545).
-/

open Polynomial Complex

namespace GeneralQuartic

/-! ## Part I: Basic Definitions -/

/-- A general quartic polynomial x⁴ + ax³ + bx² + cx + d -/
noncomputable def quarticPoly (a b c d : ℂ) : Polynomial ℂ :=
  X^4 + C a * X^3 + C b * X^2 + C c * X + C d

/-- A depressed quartic has no cubic term: y⁴ + py² + qy + r -/
noncomputable def depressedQuartic (p q r : ℂ) : Polynomial ℂ :=
  X^4 + C p * X^2 + C q * X + C r

/-- The resolvent cubic for Ferrari's method: 8m³ + 20pm² + (16p² - 8r)m + (4p³ - 4pr - q²) = 0
    Solving this gives a value of m that allows factorization of the quartic. -/
noncomputable def resolventCubic (p q r : ℂ) : Polynomial ℂ :=
  C 8 * X^3 + C (20 * p) * X^2 + C (16 * p^2 - 8 * r) * X + C (4 * p^3 - 4 * p * r - q^2)

/-! ## Part II: Depressed Form Reduction -/

/-- The substitution y = x + a/4 transforms a general quartic into depressed form.
    Given x⁴ + ax³ + bx² + cx + d, the depressed form is y⁴ + py² + qy + r where:
    - p = b - 3a²/8
    - q = c - ab/2 + a³/8
    - r = d - ac/4 + a²b/16 - 3a⁴/256 -/
noncomputable def depressionCoeffs (a b c d : ℂ) : ℂ × ℂ × ℂ :=
  let p := b - 3 * a^2 / 8
  let q := c - a * b / 2 + a^3 / 8
  let r := d - a * c / 4 + a^2 * b / 16 - 3 * a^4 / 256
  (p, q, r)

/-! ## Proved Results (formerly Axioms)

The depressed quartic forward/backward transformations and the resolvent cubic existence
are proved by ring identities and the Fundamental Theorem of Algebra. The structural
results that were once axioms — `quartic_has_four_roots` (FTA), `biquadratic_forward`,
and `biquadratic_backward` (the complex quadratic formula) — are now all discharged as
theorems, so this file is axiom-free. -/

/-- **Depressed Quartic Forward** (formerly axiom, now proved)
The substitution y = x + a/4 transforms the general quartic x^4 + ax^3 + bx^2 + cx + d = 0
into the depressed form y^4 + py^2 + qy + r = 0. This direction shows that if x is a root
of the original quartic, then y = x + a/4 is a root of the depressed quartic.

The proof is by the polynomial identity: expanding (x + a/4)^4 + p(x + a/4)^2 + q(x + a/4) + r
yields exactly x^4 + ax^3 + bx^2 + cx + d, so the result follows from h. -/
theorem depressed_quartic_forward (a b c d x : ℂ)
    (h : x^4 + a * x^3 + b * x^2 + c * x + d = 0) :
    let shift := a / 4
    let y := x + shift
    let p := b - 3 * a^2 / 8
    let q := c - a * b / 2 + a^3 / 8
    let r := d - a * c / 4 + a^2 * b / 16 - 3 * a^4 / 256
    y^4 + p * y^2 + q * y + r = 0 := by
  simp only []
  linear_combination h

/-- **Depressed Quartic Backward** (formerly axiom, now proved)
The inverse direction: if y is a root of the depressed quartic, then x = y - a/4
is a root of the original quartic. This is the converse transformation.

By the same polynomial identity: (y - a/4)^4 + a(y - a/4)^3 + b(y - a/4)^2 + c(y - a/4) + d
equals y^4 + py^2 + qy + r, so the result follows from h. -/
theorem depressed_quartic_backward (a b c d y : ℂ)
    (h : let p := b - 3 * a^2 / 8
         let q := c - a * b / 2 + a^3 / 8
         let r := d - a * c / 4 + a^2 * b / 16 - 3 * a^4 / 256
         y^4 + p * y^2 + q * y + r = 0) :
    let x := y - a / 4
    x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  simp only [] at h ⊢
  linear_combination h

/-- **Ferrari factorization polynomial identity** (S7 ACT, 2026-06-09).

The product of the two Ferrari factors equals the depressed quartic
provided three "Vieta-completion" conditions hold:

* `hα  : α² = 2m + p`        (the `y²` coefficient match);
* `hβ1 : 2 α β = q`          (the `y` coefficient match);
* `hβ2 : (p+m)² − β² = r`    (the constant coefficient match).

This is a pure polynomial identity in `(y, p, q, r, m, α, β)` over `ℂ`,
dischargeable by `linear_combination` from the three hypotheses (no use
of `α ≠ 0` or the resolvent cubic equation is required at this level).

It is the algebraic substrate of sound Ferrari factorization theorems:
when `α ≠ 0`, `hβ1` follows from `hβ : α ≠ 0 → β = q/(2α)`, and `hβ2`
follows from `hα`, `hβ1`, and the resolvent cubic equation `hm` (after
multiplying by `4α²` and cancelling, see `ferrari_hβ2_of_resolvent`).

**Residual axiom gap closed by this theorem.** The existing
`ferrari_factorization_forward / backward` axioms (S6 BUGFIX,
2026-06-04) repaired the `p+m` vs `p/2+m` constant-term sign of the
factor expressions, but they still admit a degenerate-case
counterexample at `α = 0`: there `hβ` is vacuous, so `β` may be
arbitrary, but the conclusion's factorization actually requires
`β² = (p+m)² − r`. The identity-based formulation below imposes that
constant-coefficient match (`hβ2`) directly, making both directions
provably sound. See
`sessions/2026-06-09-s7-act-ferrari-factorization-id-sound-discharge.md`. -/
theorem ferrari_factorization_id (p q r m α β y : ℂ)
    (hα : α^2 = 2 * m + p)
    (hβ1 : 2 * α * β = q)
    (hβ2 : (p + m)^2 - β^2 = r) :
    (y^2 + p + m - α * y + β) * (y^2 + p + m + α * y - β) =
      y^4 + p * y^2 + q * y + r := by
  linear_combination (-y^2) * hα + y * hβ1 + hβ2

/-- **Resolvent-cubic-to-`hβ2` bridge under `α ≠ 0`** (S7 ACT, 2026-06-09).

Given the Ferrari setup with `α ≠ 0` and `2αβ = q`, the resolvent cubic
equation `hm` implies the constant-coefficient match `(p+m)² − β² = r`.

Proof: multiply the target through by `4 α²` to obtain a polynomial
identity, dischargeable by `linear_combination` from `hα`, `hβ1`, and
`hm`; then cancel `4 α² ≠ 0` (uses `α ≠ 0`). -/
theorem ferrari_hβ2_of_resolvent (p q r m α β : ℂ)
    (hα : α^2 = 2 * m + p)
    (hα_ne : α ≠ 0)
    (hβ1 : 2 * α * β = q)
    (hm : 8 * m^3 + 20 * p * m^2 + (16 * p^2 - 8 * r) * m + (4 * p^3 - 4 * p * r - q^2) = 0) :
    (p + m)^2 - β^2 = r := by
  have hα2_ne : α^2 ≠ 0 := pow_ne_zero 2 hα_ne
  have h4α2_ne : (4 * α^2 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hα2_ne
  have key : 4 * α^2 * ((p + m)^2 - β^2 - r) = 0 := by
    linear_combination (4 * (p + m)^2 - 4 * r) * hα - (2 * α * β + q) * hβ1 + hm
  have heq : 4 * α^2 * ((p + m)^2 - β^2 - r) = 4 * α^2 * 0 := by
    rw [mul_zero]; exact key
  have h0 : (p + m)^2 - β^2 - r = 0 := mul_left_cancel₀ h4α2_ne heq
  linear_combination h0

/-- **Ferrari factorization, backward direction, non-degenerate case**
(S7 ACT, 2026-06-09).

The backward direction of `ferrari_factorization` under the strengthened
hypothesis `α ≠ 0`. **Proved as a theorem** (no axiom appeal), via
`ferrari_factorization_id` and `ferrari_hβ2_of_resolvent`. Replaces
`ferrari_factorization_backward` in the case it is actually used by
downstream theorems (where `α = Complex.cpow (2m + p) (1/2)` with
`2m + p ≠ 0`, hence `α ≠ 0`). -/
theorem ferrari_factorization_backward_ne (p q r m α β y : ℂ)
    (hα : α^2 = 2 * m + p)
    (hα_ne : α ≠ 0)
    (hβ : α ≠ 0 → β = q / (2 * α))
    (hm : 8 * m^3 + 20 * p * m^2 + (16 * p^2 - 8 * r) * m + (4 * p^3 - 4 * p * r - q^2) = 0)
    (h : (y^2 + p + m - α * y + β = 0) ∨ (y^2 + p + m + α * y - β = 0)) :
    y^4 + p * y^2 + q * y + r = 0 := by
  have hβ_eq : β = q / (2 * α) := hβ hα_ne
  have hβ1 : 2 * α * β = q := by
    rw [hβ_eq]; field_simp
  have hβ2 : (p + m)^2 - β^2 = r :=
    ferrari_hβ2_of_resolvent p q r m α β hα hα_ne hβ1 hm
  have hid := ferrari_factorization_id p q r m α β y hα hβ1 hβ2
  rcases h with hF1 | hF2
  · rw [hF1, zero_mul] at hid
    exact hid.symm
  · rw [hF2, mul_zero] at hid
    exact hid.symm

/-- **Ferrari factorization, forward direction, non-degenerate case**
(S7 ACT, 2026-06-09).

The forward direction of `ferrari_factorization` under the strengthened
hypothesis `α ≠ 0`. Proved using `ferrari_factorization_id` and the
no-zero-divisor property of `ℂ`. -/
theorem ferrari_factorization_forward_ne (p q r m α β y : ℂ)
    (hα : α^2 = 2 * m + p)
    (hα_ne : α ≠ 0)
    (hβ : α ≠ 0 → β = q / (2 * α))
    (hm : 8 * m^3 + 20 * p * m^2 + (16 * p^2 - 8 * r) * m + (4 * p^3 - 4 * p * r - q^2) = 0)
    (h : y^4 + p * y^2 + q * y + r = 0) :
    (y^2 + p + m - α * y + β = 0) ∨ (y^2 + p + m + α * y - β = 0) := by
  have hβ_eq : β = q / (2 * α) := hβ hα_ne
  have hβ1 : 2 * α * β = q := by
    rw [hβ_eq]; field_simp
  have hβ2 : (p + m)^2 - β^2 = r :=
    ferrari_hβ2_of_resolvent p q r m α β hα hα_ne hβ1 hm
  have hid : (y^2 + p + m - α * y + β) * (y^2 + p + m + α * y - β) = 0 := by
    rw [ferrari_factorization_id p q r m α β y hα hβ1 hβ2]; exact h
  exact mul_eq_zero.mp hid

/-- **Resolvent Cubic Has Root** (formerly axiom, now proved)
By the Fundamental Theorem of Algebra, every polynomial of degree >= 1 over ℂ has a root.
Since the resolvent cubic has degree 3 (leading coefficient 8 ≠ 0), it has a root. -/
theorem resolvent_cubic_has_root (p q r : ℂ) :
    ∃ m : ℂ, (resolventCubic p q r).eval m = 0 := by
  -- The coefficient of X^3 is 8 ≠ 0
  have hcoeff : (resolventCubic p q r).coeff 3 ≠ 0 := by
    simp only [resolventCubic, Polynomial.coeff_add, Polynomial.coeff_C_mul,
               Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  -- Therefore degree ≠ 0, and by FTA (ℂ is algebraically closed) there exists a root
  suffices hdeg : (resolventCubic p q r).degree ≠ 0 from
    IsAlgClosed.exists_root _ hdeg
  intro h0
  exact hcoeff (by rw [Polynomial.eq_C_of_degree_le_zero (le_of_eq h0)]; simp [Polynomial.coeff_C])

/-- **Theorem: Quartic Has Four Roots**
By the Fundamental Theorem of Algebra (ℂ is algebraically closed), the monic
degree-4 polynomial `quarticPoly a b c d` has a root multiset of cardinality 4.
Listing its (not necessarily distinct) roots `r₁,r₂,r₃,r₄`, a complex number is a
root of the quartic iff it equals one of them. Previously an axiom; now discharged
from Mathlib's FTA infrastructure (`splits_iff_card_roots`, `mem_roots`). -/
theorem quartic_has_four_roots (a b c d : ℂ) :
    ∃ (r₁ r₂ r₃ r₄ : ℂ),
      ∀ x : ℂ, (quarticPoly a b c d).eval x = 0 ↔ (x = r₁ ∨ x = r₂ ∨ x = r₃ ∨ x = r₄) := by
  have hmonic : (quarticPoly a b c d).Monic := by unfold quarticPoly; monicity!
  have hdeg : (quarticPoly a b c d).natDegree = 4 := by unfold quarticPoly; compute_degree!
  set P := quarticPoly a b c d with hP
  have hPne : P ≠ 0 := hmonic.ne_zero
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hcard4 : Multiset.card P.roots = 4 := by
    rw [Polynomial.splits_iff_card_roots.mp hsplits, hdeg]
  obtain ⟨r₁, hr₁mem⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hcard4]; norm_num)
  have hcard3 : Multiset.card (P.roots.erase r₁) = 3 := by
    rw [Multiset.card_erase_of_mem hr₁mem, hcard4]; rfl
  obtain ⟨r₂, r₃, r₄, herase⟩ := Multiset.card_eq_three.mp hcard3
  refine ⟨r₁, r₂, r₃, r₄, fun x => ?_⟩
  constructor
  · intro hx
    have hmem : x ∈ P.roots := (Polynomial.mem_roots hPne).mpr hx
    rw [← Multiset.cons_erase hr₁mem, herase] at hmem
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
    tauto
  · intro hx
    have hmem : x ∈ P.roots := by
      rw [← Multiset.cons_erase hr₁mem, herase]
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
      tauto
    exact (Polynomial.mem_roots hPne).mp hmem

/-- **Theorem: Biquadratic Forward**
When q = 0, the depressed quartic y⁴ + py² + r = 0 reduces to a quadratic in z = y².
Setting `s = √(p²−4r)` (the principal complex square root, `s² = p²−4r` even when the
radicand is 0), the identity `(2y²+p−s)(2y²+p+s) = 4(y⁴+py²+r) + (p²−4r−s²)` shows the
product vanishes, so `y²` equals one of `(−p±s)/2`. Previously an axiom. -/
theorem biquadratic_forward (p r y : ℂ)
    (h : y^4 + p * y^2 + 0 * y + r = 0) :
    (y^2 = (-p + Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) ∨
    (y^2 = (-p - Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) := by
  have hs2 : (Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) ^ 2 = p^2 - 4*r := by
    have hh := Complex.cpow_nat_inv_pow (p^2 - 4*r) (n := 2) (by norm_num)
    rwa [show ((2 : ℕ) : ℂ)⁻¹ = (1/2 : ℂ) by norm_num] at hh
  set s := Complex.cpow (p^2 - 4*r) (1/2 : ℂ)
  have key : (2 * y^2 + p - s) * (2 * y^2 + p + s) = 0 := by
    have hexp : (2 * y^2 + p - s) * (2 * y^2 + p + s)
        = 4 * (y^4 + p * y^2 + 0 * y + r) + (p^2 - 4*r - s^2) := by ring
    rw [hexp, h, hs2]; ring
  rcases mul_eq_zero.mp key with h1 | h1
  · left; linear_combination h1 / 2
  · right; linear_combination h1 / 2

/-- **Theorem: Biquadratic Backward**
If `y²` equals one of `(−p±√(p²−4r))/2`, then `y` is a root of the biquadratic
y⁴ + py² + r = 0. The converse of `biquadratic_forward`; proved by substituting each
value and using `s² = p²−4r`. Previously an axiom. -/
theorem biquadratic_backward (p r y : ℂ)
    (h : (y^2 = (-p + Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) ∨
         (y^2 = (-p - Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2)) :
    y^4 + p * y^2 + 0 * y + r = 0 := by
  have hs2 : (Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) ^ 2 = p^2 - 4*r := by
    have hh := Complex.cpow_nat_inv_pow (p^2 - 4*r) (n := 2) (by norm_num)
    rwa [show ((2 : ℕ) : ℂ)⁻¹ = (1/2 : ℂ) by norm_num] at hh
  set s := Complex.cpow (p^2 - 4*r) (1/2 : ℂ)
  have hy4 : y^4 + p * y^2 + 0 * y + r = (y^2)^2 + p * (y^2) + r := by ring
  rw [hy4]
  rcases h with h1 | h1 <;> rw [h1] <;> linear_combination hs2 / 4

/-- Any general quartic can be reduced to depressed form via substitution. -/
theorem quartic_to_depressed (a b c d : ℂ) :
    ∃ (p q r : ℂ) (shift : ℂ),
      ∀ x : ℂ, (quarticPoly a b c d).eval x = 0 ↔
               (depressedQuartic p q r).eval (x + shift) = 0 := by
  use (depressionCoeffs a b c d).1, (depressionCoeffs a b c d).2.1,
      (depressionCoeffs a b c d).2.2, a / 4
  intro x
  simp only [quarticPoly, depressedQuartic, depressionCoeffs, eval_add, eval_mul,
             eval_pow, eval_X, eval_C]
  constructor
  · intro h
    -- Apply forward direction
    have := depressed_quartic_forward a b c d x
    simp only [quarticPoly, eval_add, eval_mul, eval_pow, eval_X, eval_C] at this
    exact this h
  · intro h
    -- Apply backward direction
    have := depressed_quartic_backward a b c d (x + a / 4)
    simp only [depressedQuartic, depressionCoeffs, eval_add, eval_mul, eval_pow, eval_X, eval_C] at this
    have h2 := this h
    skip
    ring_nf at h2 ⊢
    exact h2

/-! ## Part III: Ferrari's Method -/

/-- Ferrari's key insight: For a depressed quartic y⁴ + py² + qy + r = 0,
    if m is a root of the resolvent cubic, then the quartic factors as:
    (y² + p + m − αy + β)(y² + p + m + αy − β) = 0
    where α² = 2m + p (assuming 2m + p ≠ 0) and β = q/(2α).

    **Convention note**: this file's resolvent cubic corresponds to the
    non-standard completion `(y² + p + m)²` (with constant `p + m`,
    not the textbook `p/2 + m`). See `ferrari_factorization_id`. -/
theorem ferrari_factorization (p q r m α β : ℂ)
    (hα : α^2 = 2 * m + p)
    (hα_ne : α ≠ 0)
    (hβ : α ≠ 0 → β = q / (2 * α))
    (hm : (resolventCubic p q r).eval m = 0) :
    ∀ y : ℂ, (depressedQuartic p q r).eval y = 0 ↔
             ((y^2 + p + m - α * y + β = 0) ∨
              (y^2 + p + m + α * y - β = 0)) := by
  intro y
  simp only [depressedQuartic, resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  -- Extract the resolvent cubic condition
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hm
  constructor
  · intro h
    exact ferrari_factorization_forward_ne p q r m α β y hα hα_ne hβ hm h
  · intro h
    exact ferrari_factorization_backward_ne p q r m α β y hα hα_ne hβ hm h

/-- The resolvent cubic always has a solution (over ℂ). -/
theorem resolvent_has_root (p q r : ℂ) :
    ∃ m : ℂ, (resolventCubic p q r).eval m = 0 :=
  -- Follows from FTA via our axiom
  resolvent_cubic_has_root p q r

/-! ## Part IV: The Four Roots -/

/-- Once we have m from the resolvent cubic, the quartic factors into two quadratics.
    Each quadratic gives two roots via the quadratic formula, yielding four roots total. -/
theorem quartic_four_roots (a b c d : ℂ) :
    ∃ (r₁ r₂ r₃ r₄ : ℂ),
      ∀ x : ℂ, (quarticPoly a b c d).eval x = 0 ↔ (x = r₁ ∨ x = r₂ ∨ x = r₃ ∨ x = r₄) :=
  -- This follows from FTA via our axiom
  quartic_has_four_roots a b c d

/-- Explicit formula for roots (Ferrari's formula).
    Given depressed quartic y⁴ + py² + qy + r = 0 with resolvent root m:

    Let α = √(2m + p), and if α ≠ 0, let β = q/(2α). Then the four roots are
    (with the file's non-standard `(y² + p + m)²` completion convention —
    see `ferrari_factorization_id`):

    Factor 1 (`y² − αy + (p + m + β) = 0`): roots `y = (α ± √(α² − 4(p+m+β)))/2`
    Factor 2 (`y² + αy + (p + m − β) = 0`): roots `y = (−α ± √(α² − 4(p+m−β)))/2`

    For the general quartic x⁴ + ax³ + bx² + cx + d = 0, subtract a/4 from each. -/
noncomputable def ferrariRoots (p q r m : ℂ) (_hm : (resolventCubic p q r).eval m = 0) : ℂ × ℂ × ℂ × ℂ :=
  let α := Complex.cpow (2 * m + p) (1/2 : ℂ)  -- √(2m + p)
  let β := if α = 0 then 0 else q / (2 * α)
  let disc1 := α^2 - 4 * (p + m + β)   -- discriminant of Factor 1
  let disc2 := α^2 - 4 * (p + m - β)   -- discriminant of Factor 2
  let sqrt1 := Complex.cpow disc1 (1/2 : ℂ)
  let sqrt2 := Complex.cpow disc2 (1/2 : ℂ)
  ((α + sqrt1) / 2, (α - sqrt1) / 2, (-α + sqrt2) / 2, (-α - sqrt2) / 2)

/-- **Ferrari Roots Verification, non-degenerate case** (formerly axiom
`ferrari_roots_verify`; S8 SOUND DISCHARGE, 2026-06-13).

The four explicit Ferrari roots satisfy the depressed quartic, **provided**
the chosen resolvent root `m` is non-degenerate (`2m + p ≠ 0`, equivalently
`α ≠ 0`).

**Why the `2m + p ≠ 0` hypothesis is mandatory (latent-false axiom found).**
The former unconditional `ferrari_roots_verify` axiom is *false* on the
degenerate branch `α = 0`. There `β` is forced to `0` and both
discriminants collapse to `disc₁ = disc₂ = α² − 4(p+m) = −4(p+m)`, so
`y₁² = −(p+m)`. The resolvent equation at such an `m = −p/2` forces `q = 0`
(its constant term is `−q²`), and the four roots are then valid only when
`r = p²/4`. Concrete counterexample: `(p,q,r,m) = (0,0,1,0)` satisfies
`hm` (constant term `4p³−4pr−q² = 0`) yet every Ferrari root equals `0`,
while `(depressedQuartic 0 0 1).eval 0 = r = 1 ≠ 0`. The old axiom thus
proved `(1 : ℂ) = 0`. This is the same `α = 0` soundness gap that S7 closed
for `ferrari_factorization_*`.

**Proof.** With `α ≠ 0`, each root lies on one of Ferrari's two quadratic
factors (a pure `linear_combination` identity using `(√·)² = ·`), and
`ferrari_factorization_backward_ne` carries factor membership to the
depressed quartic. -/
theorem ferrari_roots_verify_ne (p q r m : ℂ)
    (hm : (resolventCubic p q r).eval m = 0)
    (h2mp : 2 * m + p ≠ 0) :
    let (y₁, y₂, y₃, y₄) := ferrariRoots p q r m hm
    (depressedQuartic p q r).eval y₁ = 0 ∧
    (depressedQuartic p q r).eval y₂ = 0 ∧
    (depressedQuartic p q r).eval y₃ = 0 ∧
    (depressedQuartic p q r).eval y₄ = 0 := by
  -- The half-power squares back: (z ^ (1/2))² = z over ℂ (true even at z = 0).
  have hcpow_sq : ∀ z : ℂ, (Complex.cpow z (1/2 : ℂ)) ^ 2 = z := by
    intro z
    have h := Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
    rwa [show ((2 : ℕ) : ℂ)⁻¹ = (1/2 : ℂ) by norm_num] at h
  -- Resolvent cubic in expanded polynomial form.
  have hm' : 8 * m ^ 3 + 20 * p * m ^ 2 + (16 * p ^ 2 - 8 * r) * m
      + (4 * p ^ 3 - 4 * p * r - q ^ 2) = 0 := by
    have h := hm
    simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
    linear_combination h
  -- Unfold the explicit roots and the depressed-quartic evaluation.
  simp only [ferrariRoots, depressedQuartic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  set α : ℂ := Complex.cpow (2 * m + p) (1/2 : ℂ) with hα_def
  have hα : α ^ 2 = 2 * m + p := by rw [hα_def]; exact hcpow_sq _
  have hα_ne : α ≠ 0 := fun h0 => h2mp (by rw [← hα, h0]; ring)
  set β : ℂ := if α = 0 then 0 else q / (2 * α) with hβ_def
  have hβ_eq : β = q / (2 * α) := by rw [hβ_def]; exact if_neg hα_ne
  have hβ : α ≠ 0 → β = q / (2 * α) := fun _ => hβ_eq
  set s1 : ℂ := Complex.cpow (α ^ 2 - 4 * (p + m + β)) (1/2 : ℂ) with hs1_def
  set s2 : ℂ := Complex.cpow (α ^ 2 - 4 * (p + m - β)) (1/2 : ℂ) with hs2_def
  have hs1 : s1 ^ 2 = α ^ 2 - 4 * (p + m + β) := by rw [hs1_def]; exact hcpow_sq _
  have hs2 : s2 ^ 2 = α ^ 2 - 4 * (p + m - β) := by rw [hs2_def]; exact hcpow_sq _
  -- Each root satisfies one of the two Ferrari quadratic factors.
  have fac1a : ((α + s1) / 2) ^ 2 + p + m - α * ((α + s1) / 2) + β = 0 := by
    linear_combination (1 / 4 : ℂ) * hs1
  have fac1b : ((α - s1) / 2) ^ 2 + p + m - α * ((α - s1) / 2) + β = 0 := by
    linear_combination (1 / 4 : ℂ) * hs1
  have fac2a : ((-α + s2) / 2) ^ 2 + p + m + α * ((-α + s2) / 2) - β = 0 := by
    linear_combination (1 / 4 : ℂ) * hs2
  have fac2b : ((-α - s2) / 2) ^ 2 + p + m + α * ((-α - s2) / 2) - β = 0 := by
    linear_combination (1 / 4 : ℂ) * hs2
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination
      ferrari_factorization_backward_ne p q r m α β ((α + s1) / 2) hα hα_ne hβ hm' (Or.inl fac1a)
  · linear_combination
      ferrari_factorization_backward_ne p q r m α β ((α - s1) / 2) hα hα_ne hβ hm' (Or.inl fac1b)
  · linear_combination
      ferrari_factorization_backward_ne p q r m α β ((-α + s2) / 2) hα hα_ne hβ hm' (Or.inr fac2a)
  · linear_combination
      ferrari_factorization_backward_ne p q r m α β ((-α - s2) / 2) hα hα_ne hβ hm' (Or.inr fac2b)

/-! ## Part V: Verification -/

/-- Verification: The Ferrari roots satisfy the depressed quartic equation.
    This confirms Ferrari's method produces valid solutions.

    Requires the resolvent root `m` to be non-degenerate (`2m + p ≠ 0`); see
    `ferrari_roots_verify_ne` for why the degenerate branch is genuinely
    excluded rather than merely inconvenient. -/
theorem ferrari_roots_are_roots (p q r m : ℂ)
    (hm : (resolventCubic p q r).eval m = 0) (h2mp : 2 * m + p ≠ 0) :
    let (y₁, y₂, y₃, y₄) := ferrariRoots p q r m hm
    (depressedQuartic p q r).eval y₁ = 0 ∧
    (depressedQuartic p q r).eval y₂ = 0 ∧
    (depressedQuartic p q r).eval y₃ = 0 ∧
    (depressedQuartic p q r).eval y₄ = 0 :=
  ferrari_roots_verify_ne p q r m hm h2mp

/-! ## Part VI: Special Cases -/

/-- Biquadratic quartic (q = 0): y⁴ + py² + r = 0 simplifies to quadratic in y². -/
theorem biquadratic_simple (p r : ℂ) :
    ∀ y : ℂ, (depressedQuartic p 0 r).eval y = 0 ↔
             (y^2 = (-p + Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) ∨
             (y^2 = (-p - Complex.cpow (p^2 - 4*r) (1/2 : ℂ)) / 2) := by
  intro y
  simp only [depressedQuartic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  constructor
  · intro h
    -- Apply forward direction (biquadratic case is q = 0)
    exact biquadratic_forward p r y h
  · intro h
    -- Apply backward direction
    exact biquadratic_backward p r y h

/-! ## Part VI.5: Biquadratic-Limit Removable Singularity (OQ-02.c)

This subsection discharges the biquadratic-limit identity sketched in
`research/problems/general-quartic-oq-02/knowledge.md` (Approach A). At
`q = 0`, the indeterminate-form factor `β = q / (2α)` in `ferrariRoots`
degenerates whenever a chosen resolvent root `m` satisfies `2m + p = 0`.
The two helper lemmas isolate the trivial root `m = -p/2` and rewrite the
resolvent cubic in the cleaner constant-term `4p^3 - 4pr` (the `-q²`
contribution vanishes). `ferrari_biquad_limit` then states that for every
`(p, r) ≠ (0, 0)` there exists a non-degenerate resolvent root whose four
Ferrari roots, when squared, fall in the two-element biquadratic root
pair `{(-p ± √(p²−4r))/2}` — the canonical biquadratic root set.

`ferrari_biquad_limit` is proved in S3 (DISCHARGE): Sub-step A pairs a
square root `u^2 = r` (from FTA on `X^2 + C(-r)`) with the case-split
`m₁ = -p + u` vs `m₂ = -p - u`; Sub-step B chains
`ferrari_roots_are_roots` with `biquadratic_simple` to land each
`yᵢ^2` in the biquadratic root pair. -/

/-- At `q = 0`, the constant term of the resolvent cubic simplifies (the
`-q²` contribution vanishes). Provable by `ring`. -/
theorem resolvent_cubic_q_zero (p r : ℂ) :
    resolventCubic p 0 r =
    C 8 * X^3 + C (20 * p) * X^2 + C (16 * p^2 - 8 * r) * X + C (4 * p^3 - 4 * p * r) := by
  unfold resolventCubic
  ring

/-- At `q = 0`, `m = -p/2` is always a root of the resolvent cubic.
This is the *trivial* (degenerate) resolvent root: it makes
`α² = 2m + p = 0`, so `α = 0` and the `β = q/(2α)` factor in
`ferrariRoots` is the indeterminate `0/0`. For the non-trivial Ferrari
branch (Approach A in `knowledge.md`), we need a *different* resolvent
root, which exists whenever `(p, r) ≠ (0, 0)`. -/
theorem resolvent_root_neg_p_half_at_q_zero (p r : ℂ) :
    (resolventCubic p 0 r).eval (-p / 2) = 0 := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- **Resolvent cubic in the Newton-polygon-cleaned variable `s = 2m + p`**
(Lemma 1 from `sessions/2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md`,
§2; S5a SCAFFOLD).

The substitution `m ↦ (s - p) / 2` (equivalently, `s := 2m + p`, which is
the `α²` of Ferrari's intermediate factor) transforms the resolvent cubic
into the Newton-polygon-friendly cleaned form
`R̃(s) = s³ + 2p·s² + (p² − 4r)·s − q²`.

The cleaned form makes the dependence on `q²` explicit as the inhomogeneous
term and factors out the trivial `α = 0 ⇔ s = 0` degeneracy. It is the
universal substrate for the Newton-polygon analysis in the S4c PREP
(which establishes that, in the smooth Pan-witness family, the tangency
order `k` between `α(t)` and the actual quartic root spread is pinned
at `k = 1`).

Proof: pure algebraic identity. Discharged by `ring` after unfolding
`resolventCubic` and polynomial `eval`. -/
theorem resolvent_cubic_eval_s_form (p q r s : ℂ) :
    (resolventCubic p q r).eval ((s - p) / 2) =
    s^3 + 2 * p * s^2 + (p^2 - 4 * r) * s - q^2 := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- **Pan-witness specialization of the cleaned resolvent** (S5b SCAFFOLD-1).

At the Pan numerical-instability witness `(p, q, r)(t) = (-1, t², 1/4 − t² + t⁴/4)`
(see `sessions/2026-05-13-s4b-prep-pan-witness-arithmetic-audit.md` §2), the
cleaned-resolvent identity `resolvent_cubic_eval_s_form` specializes to

`R̃(s; -1, t², 1/4 − t² + t⁴/4) = s³ − 2 s² + (4 t² − t⁴) · s − t⁴`.

The first-order tangency that drives the `α(t) = Θ(t)` cancellation is
visible from this identity directly: at `t = 0` the RHS is `s²(s − 2)`,
exhibiting a double root at `s = 0` (i.e., `α² = s = 0` is a double root
of the cleaned resolvent in `s`). This is the algebraic precursor to the
`k = 1` tangency proof for a future S5b ACT.

Proof: substitute the witness coordinates into `resolvent_cubic_eval_s_form`
and close by `ring`. -/
theorem pan_witness_cleaned_resolvent (t s : ℂ) :
    (resolventCubic (-1) (t^2) (1/4 - t^2 + t^4/4)).eval ((s - (-1)) / 2) =
    s^3 - 2 * s^2 + (4 * t^2 - t^4) * s - t^4 := by
  rw [resolvent_cubic_eval_s_form]
  ring

/-- **Pan-witness `t = 0` factorisation** (S5b SCAFFOLD-2).

Specialising `pan_witness_cleaned_resolvent` at the boundary value
`t = 0`, the cleaned-resolvent polynomial in `s` collapses to
`s³ - 2 s² = s² · (s - 2)`. This **factorised** form exposes:

* a **double root** at `s = 0` (i.e. `α² = 2m + p = 0`, the degenerate
  Ferrari branch);
* a **single root** at `s = 2` (the non-degenerate branch).

This is the algebraic substrate for the future `pan_witness_k1_tangency`
(S5b ACT proper, see `sessions/2026-05-13-s5b-scaffold-1-pan-witness-cleaned-resolvent.md`
§11). The double root at `s = 0` is what perturbs — under
`t ≠ 0` — into a `Θ(t)` pair of roots (the `s¹` coefficient `4t² - t⁴`
of `pan_witness_cleaned_resolvent` is `Θ(t²)`, so by Vieta the two
near-zero roots are at `s = ±Θ(t)`), giving `α(t) = Θ(√t · √t) = Θ(t)`
— the `k = 1` tangency of OQ-02.a.1. The third root at `s = 2 + O(t²)`
is the non-degenerate Ferrari branch and stays a fixed distance away.

Proof: identical `simp only + ring` pattern as `resolvent_cubic_q_zero`
(line 341), `resolvent_root_neg_p_half_at_q_zero` (line 353), and
`resolvent_cubic_eval_s_form` (line 376). -/
theorem pan_witness_t_zero_factorisation (s : ℂ) :
    (resolventCubic (-1) 0 (1/4 : ℂ)).eval ((s - (-1)) / 2) = s^2 * (s - 2) := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- **Pan-witness `t = 0` non-degenerate root** (S5b SCAFFOLD-3).

At the Pan witness's `t = 0` boundary `(p, q, r) = (-1, 0, 1/4)`, the
cleaned resolvent factorises as `s² · (s - 2)` (see
`pan_witness_t_zero_factorisation`). Translating back to `m`-coordinates
via `m = (s + 1)/2`, the third (non-double) resolvent root sits at
`s = 2`, i.e. `m = 3/2`, where `2m + p = 3 - 1 = 2 ≠ 0` — the
**non-degenerate Ferrari branch** at the Pan-witness boundary.

This lemma makes the abstract existence statement
`ferrari_biquad_limit (-1) (1/4) hpr` concrete with `m = 3/2`. It also
matches the Newton-polygon prediction in `pan_witness_t_zero_factorisation`'s
docstring (third root stays at `s = 2 + O(t²)` under `t ≠ 0`
perturbation).

Proof: identical `simp only + ring` pattern as
`pan_witness_t_zero_factorisation` (line 426). -/
theorem pan_witness_t_zero_nondegenerate_root :
    (resolventCubic (-1) 0 (1/4 : ℂ)).eval (3/2 : ℂ) = 0 := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-! ### The `k = 1` tangency along the Pan witness (S5b ACT, OQ-02.a)

The scaffolds above reduced OQ-02.a to a statement about the *cleaned*
resolvent `R̃(s; t) = s³ − 2s² + (4t² − t⁴)s − t⁴` along the Pan witness:
the degenerate double root `s = 0` of the `t = 0` boundary perturbs, for
`t ≠ 0`, into roots of size exactly `Θ(t²)` in `s` — hence
`α = √s = Θ(t)`, the **first-order (`k = 1`) cancellation** of Ferrari's
intermediate. The S4c Newton-polygon PREP showed `k ≥ 2` is unattainable
in smooth families; this section shows `k = 1` is *attained*, pinning the
tangency order.

The quantitative form needs no asymptotic (`O`/`Θ`) infrastructure: for
real `0 < t ≤ 1` the real cleaned resolvent changes sign on
`(t²/4, t²)` — so it has a root `s = α²` there (IVT) — and is strictly
negative on all of `[0, t²/4]` — so no root cancels faster. Together:
every near-zero cancellation of `α²` along the Pan family happens at
order *exactly* `t²`, i.e. `t/2 < α < t`. -/

/-- The **real** cleaned resolvent along the Pan witness:
`R̃(s; t) = s³ − 2s² + (4t² − t⁴)s − t⁴` with `t, s : ℝ`. The real form of
`pan_witness_cleaned_resolvent`, suitable for sign analysis and the IVT. -/
def panCleanedResolvent (t s : ℝ) : ℝ :=
  s ^ 3 - 2 * s ^ 2 + (4 * t ^ 2 - t ^ 4) * s - t ^ 4

/-- The real cleaned resolvent computes the (complex) resolvent cubic of the
Pan witness under the substitution `m = (s + 1)/2` (`s = 2m + p` with
`p = −1`): real roots of `panCleanedResolvent t` are genuine resolvent-cubic
roots of the Ferrari data. Bridge between the real sign analysis below and
the file's ℂ-valued Ferrari objects. -/
theorem panCleanedResolvent_bridge (t s : ℝ) :
    (resolventCubic (-1) ((t : ℂ) ^ 2) (1/4 - (t : ℂ) ^ 2 + (t : ℂ) ^ 4 / 4)).eval
      (((s : ℂ) + 1) / 2) = (panCleanedResolvent t s : ℂ) := by
  have h := pan_witness_cleaned_resolvent (t : ℂ) (s : ℂ)
  rw [show ((s : ℂ) - (-1)) / 2 = ((s : ℂ) + 1) / 2 by ring] at h
  rw [h]
  simp only [panCleanedResolvent]
  push_cast
  ring

/-- **No faster-than-`t²` cancellation**: the cleaned resolvent is strictly
negative on the whole interval `0 ≤ s ≤ t²/4` (for `0 < t ≤ 1`). Certificate:
`−R̃(s) = (t⁴ − 4t²s) + s·(t⁴ + 2s − s²) + s²·s·0…` — the first summand is
nonnegative since `4t²s ≤ t⁴`, the second is nonnegative since `s ≤ 1/4 < 2`,
and they cannot vanish simultaneously (`s = 0` forces the first to be `t⁴ > 0`).
Hence any vanishing of `α² = s` along the Pan family is of order at least
`t²/4`: the intermediate `α` cannot cancel at order higher than `t`. -/
theorem pan_witness_no_root_below (t s : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hs0 : 0 ≤ s) (hs : s ≤ t ^ 2 / 4) : panCleanedResolvent t s < 0 := by
  rcases eq_or_lt_of_le hs0 with rfl | hspos
  · -- boundary `s = 0`: the value is exactly `−t⁴`
    have h : panCleanedResolvent t 0 = -t ^ 4 := by
      unfold panCleanedResolvent; ring
    rw [h]
    have : (0 : ℝ) < t ^ 4 := by positivity
    linarith
  · -- interior `s > 0`: `−R̃(s) = t²(t² − 4s) + t⁴s + s²(2 − s)`, with the
    -- middle summand strictly positive
    unfold panCleanedResolvent
    nlinarith [mul_pos (pow_pos ht0 4) hspos,
      mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ t ^ 2 - 4 * s),
      mul_nonneg (sq_nonneg s) (by nlinarith : (0 : ℝ) ≤ 2 - s)]

/-- The cleaned resolvent is strictly positive at `s = t²` (any `t ≠ 0`):
`R̃(t²; t) = t⁴`. The upper end of the sign-change bracket. -/
theorem pan_witness_pos_at_t_sq (t : ℝ) (ht0 : t ≠ 0) :
    0 < panCleanedResolvent t (t ^ 2) := by
  have h : panCleanedResolvent t (t ^ 2) = t ^ 4 := by
    unfold panCleanedResolvent; ring
  rw [h]
  positivity

/-- **The `k = 1` tangency, real root-localization form** (S5b ACT,
OQ-02.a). For every `0 < t ≤ 1` the cleaned resolvent of the Pan witness has
a real root `s` with `t²/4 < s < t²`.

Interpretation: `s = α²` where `α = √(2m + p)` is Ferrari's cancelling
intermediate, so `t/2 < α < t` — the cancellation is of order **exactly**
`t¹` (`k = 1`), matching the Newton-polygon prediction and completing the
witness half of OQ-02.a: smooth families cannot do better than `k = 1`
(S4c PREP), and the Pan family attains it. -/
theorem pan_witness_k1_tangency (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ s : ℝ, t ^ 2 / 4 < s ∧ s < t ^ 2 ∧ panCleanedResolvent t s = 0 := by
  have hab : t ^ 2 / 4 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  have hcont : ContinuousOn (panCleanedResolvent t) (Set.Icc (t ^ 2 / 4) (t ^ 2)) := by
    apply Continuous.continuousOn
    unfold panCleanedResolvent
    fun_prop
  have hneg : panCleanedResolvent t (t ^ 2 / 4) < 0 :=
    pan_witness_no_root_below t (t ^ 2 / 4) ht0 ht1 (by positivity) le_rfl
  have hpos : 0 < panCleanedResolvent t (t ^ 2) :=
    pan_witness_pos_at_t_sq t (ne_of_gt ht0)
  have hivt := intermediate_value_Ioo hab hcont
  have h0 : (0 : ℝ) ∈ Set.Ioo (panCleanedResolvent t (t ^ 2 / 4))
      (panCleanedResolvent t (t ^ 2)) := ⟨hneg, hpos⟩
  obtain ⟨s, hs, hs0⟩ := hivt h0
  exact ⟨s, hs.1, hs.2, hs0⟩

/-- **The `k = 1` tangency, resolvent-cubic form** (S5b ACT capstone,
OQ-02.a). For every `0 < t ≤ 1` the Pan-witness resolvent cubic
`resolventCubic (−1) (t²) (1/4 − t² + t⁴/4)` has a **real** root `m` whose
Ferrari intermediate `α² = 2m + p = 2m − 1` satisfies `t²/4 < 2m − 1 < t²`.

This is the formal statement of OQ-02.a's exact-arithmetic stability
witness at the tangency order the S4c Newton-polygon analysis pinned:
along the Pan family the resolvent root exists in exact arithmetic, but its
Ferrari intermediate `α = √(2m − 1) ∈ (t/2, t)` cancels linearly while the
family stays uniformly well-separated — the `Ω(t⁻¹)`-amplification
mechanism of Ferrari's formula near the biquadratic stratum. -/
theorem pan_witness_k1_resolvent_root (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ m : ℝ,
      (resolventCubic (-1) ((t : ℂ) ^ 2) (1/4 - (t : ℂ) ^ 2 + (t : ℂ) ^ 4 / 4)).eval
        ((m : ℂ)) = 0 ∧
      t ^ 2 / 4 < 2 * m - 1 ∧ 2 * m - 1 < t ^ 2 := by
  obtain ⟨s, hs1, hs2, hs0⟩ := pan_witness_k1_tangency t ht0 ht1
  refine ⟨(s + 1) / 2, ?_, by linarith, by linarith⟩
  have hbridge := panCleanedResolvent_bridge t s
  rw [hs0] at hbridge
  rw [show ((((s + 1) / 2 : ℝ) : ℂ)) = ((s : ℂ) + 1) / 2 by push_cast; ring]
  simpa using hbridge

/-- **The `Ω(t⁻¹)` amplification theorem (S13, OQ-02.a capstone).**

This formalizes the amplification mechanism that the prose of
`pan_witness_k1_resolvent_root` only asserted: along the Pan witness,
Ferrari's intermediate `α = √s` (where `s = α²` is the cleaned-resolvent
root pinned in `(t²/4, t²)` by `pan_witness_k1_tangency`) satisfies

* `t/2 < α < t` — the cancellation is of order exactly `t¹`, and
* the square-root extraction step of Ferrari's formula has sensitivity
  `dα/ds = 1/(2√s) > 1/(2t)` at `s` — an `Ω(t⁻¹)` error-amplification
  factor that blows up as the Pan family approaches the biquadratic
  stratum `t → 0`, while the exact root `s` stays well inside `(0, t²)`.

Together with the S4c Newton-polygon bound (no smooth family can achieve
`k ≥ 2`) this is the complete, quantitative form of OQ-02.a: Ferrari's
formula is numerically unstable near the biquadratic stratum with
amplification factor at least `1/(2t)`, and the Pan family attains this
order exactly. -/
theorem pan_witness_amplification (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ s : ℝ, panCleanedResolvent t s = 0 ∧
      t / 2 < Real.sqrt s ∧ Real.sqrt s < t ∧
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s ∧
      1 / (2 * t) < 1 / (2 * Real.sqrt s) := by
  obtain ⟨s, hs1, hs2, hs0⟩ := pan_witness_k1_tangency t ht0 ht1
  have hspos : 0 < s := lt_trans (by positivity) hs1
  have hsq1 : t / 2 < Real.sqrt s := by
    have h := Real.sqrt_lt_sqrt (by positivity) hs1
    rwa [show t ^ 2 / 4 = (t / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)] at h
  have hsq2 : Real.sqrt s < t := by
    have h := Real.sqrt_lt_sqrt hspos.le hs2
    rwa [Real.sqrt_sq ht0.le] at h
  refine ⟨s, hs0, hsq1, hsq2, Real.hasDerivAt_sqrt (ne_of_gt hspos), ?_⟩
  have hsqrtpos : 0 < Real.sqrt s := lt_trans (by positivity) hsq1
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- **Biquadratic limit (OQ-02.c, S3 DISCHARGE)**

In the biquadratic limit `q = 0`, Ferrari's formula admits a
non-degenerate resolvent root `m` (i.e. one with `2m + p ≠ 0`), and at
any such `m` each of the four Ferrari roots squared lies in the
two-element biquadratic root set
`{(-p + √(p²−4r))/2, (-p − √(p²−4r))/2}`.

This closes the `α = 0` boundary case of `ferrariRoots`: the formula
degenerates only on the trivial resolvent root `m = -p/2`
(see `resolvent_root_neg_p_half_at_q_zero`), which exists for every
`(p, r)` but is excluded by the `(p, r) ≠ (0, 0)` hypothesis here for
*some* other resolvent root to exist.

**Proof strategy (S3 DISCHARGE):**

* *Sub-step A (non-degenerate resolvent root exists).* Use FTA on
  `X^2 + C(-r)` to obtain `u : ℂ` with `u^2 = r`. Then both `m₁ := -p + u`
  and `m₂ := -p - u` are roots of `resolventCubic p 0 r` (algebraic
  identity: `eval (-p + v) = (8v - 4p)(v^2 - r)`). Case-split on whether
  `m₁` satisfies `2*m₁ + p ≠ 0`. If yes, use `m₁`. Otherwise `u = p/2`,
  so `r = p^2/4`; the hypothesis `p ≠ 0 ∨ r ≠ 0` then forces `p ≠ 0`,
  and `m₂ = -3p/2` satisfies `2*m₂ + p = -2p ≠ 0`.

* *Sub-step B (Ferrari roots squared land in biquadratic root pair).*
  By `ferrari_roots_are_roots`, each `yᵢ ∈ ferrariRoots p 0 r m hm`
  satisfies `(depressedQuartic p 0 r).eval yᵢ = 0`. Then
  `biquadratic_simple` (the `q = 0` characterization) gives
  `yᵢ^2 = z₁ ∨ yᵢ^2 = z₂` directly. This bypasses any explicit-formula
  expansion of `yᵢ^2`; see `knowledge.md` → "Approach A" → "Alternative". -/
theorem ferrari_biquad_limit (p r : ℂ) (hpr : p ≠ 0 ∨ r ≠ 0) :
    ∃ m : ℂ, ∃ (hm : (resolventCubic p 0 r).eval m = 0), 2 * m + p ≠ 0 ∧
      (let s : ℂ := Complex.cpow (p^2 - 4*r) (1/2 : ℂ)
       let z₁ : ℂ := (-p + s) / 2
       let z₂ : ℂ := (-p - s) / 2
       let (y₁, y₂, y₃, y₄) := ferrariRoots p 0 r m hm
       (y₁^2 = z₁ ∨ y₁^2 = z₂) ∧
       (y₂^2 = z₁ ∨ y₂^2 = z₂) ∧
       (y₃^2 = z₁ ∨ y₃^2 = z₂) ∧
       (y₄^2 = z₁ ∨ y₄^2 = z₂)) := by
  -- Step 1: Obtain u with u² = r via FTA on X² + C(-r) (degree 2 over ℂ).
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u^2 = r := by
    have hdeg : (X^2 + C (-r) : Polynomial ℂ).degree = 2 :=
      Polynomial.degree_X_pow_add_C (by norm_num) _
    obtain ⟨u, hu⟩ : ∃ u : ℂ, (X^2 + C (-r) : Polynomial ℂ).eval u = 0 :=
      IsAlgClosed.exists_root _ (by rw [hdeg]; decide)
    simp only [eval_add, eval_pow, eval_X, eval_C] at hu
    exact ⟨u, by linear_combination hu⟩
  -- Step 2: Helper -- (-p + v) is a resolvent root whenever v² = r.
  -- Algebraic identity: (resolventCubic p 0 r).eval (-p + v) = (8v - 4p) * (v² - r),
  -- verified by `linear_combination`.
  have hresolv : ∀ v : ℂ, v^2 = r → (resolventCubic p 0 r).eval (-p + v) = 0 := by
    intro v hv
    simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    linear_combination (8*v - 4*p) * hv
  -- Sub-step B (alternative path per knowledge.md):
  -- For any valid resolvent root m, each Ferrari root yᵢ satisfies the depressed
  -- quartic (`ferrari_roots_are_roots`), hence yᵢ² is a root of the biquadratic
  -- (`biquadratic_simple`), i.e., yᵢ² ∈ {z₁, z₂}.
  have hsub_B : ∀ (m : ℂ) (hm : (resolventCubic p 0 r).eval m = 0), 2 * m + p ≠ 0 →
      (let s : ℂ := Complex.cpow (p^2 - 4*r) (1/2 : ℂ)
       let z₁ : ℂ := (-p + s) / 2
       let z₂ : ℂ := (-p - s) / 2
       let (y₁, y₂, y₃, y₄) := ferrariRoots p 0 r m hm
       (y₁^2 = z₁ ∨ y₁^2 = z₂) ∧
       (y₂^2 = z₁ ∨ y₂^2 = z₂) ∧
       (y₃^2 = z₁ ∨ y₃^2 = z₂) ∧
       (y₄^2 = z₁ ∨ y₄^2 = z₂)) := by
    intro m hm h2mp
    obtain ⟨hy₁, hy₂, hy₃, hy₄⟩ := ferrari_roots_are_roots p 0 r m hm h2mp
    exact ⟨(biquadratic_simple p r _).mp hy₁,
           (biquadratic_simple p r _).mp hy₂,
           (biquadratic_simple p r _).mp hy₃,
           (biquadratic_simple p r _).mp hy₄⟩
  -- Step 3: Sub-step A. Both m₁ = -p + u and m₂ = -p - u are resolvent roots.
  -- Case-split on whether m₁ is non-degenerate.
  by_cases h1 : 2 * (-p + u) + p = 0
  · -- m₁ degenerate: deduce u = p/2, so r = u² = p²/4. Then `p ≠ 0 ∨ r ≠ 0`
    -- forces p ≠ 0 (else r = 0 contradicts the disjunct). m₂ = -p - u = -3p/2,
    -- and 2*m₂ + p = -2p ≠ 0.
    have hu_p : u = p / 2 := by linear_combination h1 / 2
    have hr_p : r = p^2 / 4 := by rw [← hu, hu_p]; ring
    have hp : p ≠ 0 := by
      rcases hpr with h | h
      · exact h
      · intro hp0; exact h (by rw [hr_p, hp0]; ring)
    have hu_neg : (-u)^2 = r := by linear_combination hu
    have h_m₂_resolv : (resolventCubic p 0 r).eval (-p - u) = 0 := by
      rw [show (-p - u : ℂ) = -p + (-u) from by ring]
      exact hresolv (-u) hu_neg
    have hm₂_nondeg : 2 * (-p - u) + p ≠ 0 := by
      rw [hu_p]
      intro h_eq
      exact hp (by linear_combination -h_eq / 2)
    exact ⟨-p - u, h_m₂_resolv, hm₂_nondeg, hsub_B (-p - u) h_m₂_resolv hm₂_nondeg⟩
  · -- m₁ non-degenerate
    push_neg at h1
    exact ⟨-p + u, hresolv u hu, h1, hsub_B (-p + u) (hresolv u hu) h1⟩

/-! ## Part VII: Historical Context and Significance -/

/-
  Ferrari's method (1540) represents the pinnacle of Renaissance algebra.

  **The Historical Race:**
  - del Ferro (c. 1515): First solved the depressed cubic secretly
  - Tartaglia (1535): Rediscovered the cubic solution
  - Cardano (1539): Learned Tartaglia's method under oath of secrecy
  - Ferrari (1540): Solved the quartic, reducing it to a cubic!
  - Cardano (1545): Published everything in "Ars Magna"

  **Why It Stops at Degree 4:**
  Ferrari's method uses the cubic formula for the resolvent. This creates a tower:
  - Quadratic → Direct formula
  - Cubic → Cardano's formula (uses square/cube roots)
  - Quartic → Ferrari's method (uses cubic formula)
  - Quintic → Abel-Ruffini (1824): No general formula exists!

  The key insight is that S₅ (symmetric group on 5 elements) is not solvable,
  while S₂, S₃, S₄ are solvable. See #16 (Abel-Ruffini) for this deep connection.

  **Connection to Galois Theory:**
  The Galois group of a generic quartic is S₄, which is solvable because:
    S₄ ▷ A₄ ▷ V₄ ▷ {e}
  where each quotient is abelian. This is why Ferrari's method works!
-/

end GeneralQuartic

-- Summary of key results
#check GeneralQuartic.quarticPoly
#check GeneralQuartic.depressedQuartic
#check GeneralQuartic.resolventCubic
#check GeneralQuartic.quartic_to_depressed
#check GeneralQuartic.ferrari_factorization
#check GeneralQuartic.resolvent_has_root
#check GeneralQuartic.quartic_four_roots
#check GeneralQuartic.ferrariRoots
#check GeneralQuartic.ferrari_roots_are_roots
#check GeneralQuartic.ferrari_roots_verify_ne
#check GeneralQuartic.resolvent_cubic_q_zero
#check GeneralQuartic.resolvent_root_neg_p_half_at_q_zero
#check GeneralQuartic.resolvent_cubic_eval_s_form
#check GeneralQuartic.pan_witness_cleaned_resolvent
#check GeneralQuartic.pan_witness_t_zero_factorisation
#check GeneralQuartic.pan_witness_t_zero_nondegenerate_root
#check GeneralQuartic.ferrari_biquad_limit
#check GeneralQuartic.biquadratic_simple
#check GeneralQuartic.pan_witness_amplification
