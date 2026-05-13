import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# The Eisenstein integers ℤ[ω] — bare ring and norm

This file is the S2 ACT deliverable for `zsqrtd-neg-two-oq-03`. It is the
infrastructure layer for the long-term target

  `sq_add_three_sq_of_prime_one_mod_three :`
  `  ∀ {p : ℕ}, p.Prime → p % 3 = 1 → ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 3 * b ^ 2`

which generalises the parent file `Proofs/ZsqrtdNegTwo.lean` (the case
`n = 2`) to the next non-trivial Heegner-number case `n = 3`. Unlike
`n = 2`, the maximal order of `ℚ(√-3)` is **not** `ℤ[√-3]` but the
**Eisenstein integers** `ℤ[ω] = ℤ[exp(2πi/3)]`, with `ω² + ω + 1 = 0`.
Mathlib's `Zsqrtd` therefore does **not** apply directly; we build a
fresh concrete structure on `re, im : ℤ` representing `re + im · ω`.

## Contents of this file (S2 ACT, infrastructure-only)

* `Eisenstein` — the underlying type, two integer coordinates `re, im`.
* `Zero`, `One`, `Add`, `Neg`, `Mul` — primitive instances together with
  `@[simp] rfl` projection lemmas, derived from the rule
  `ω² = -1 - ω` so that
  `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd) · ω`.
* `AddCommGroup`, `AddGroupWithOne`, `CommRing` — built via the same
  `refine ... <;> intros <;> ext <;> simp <;> ring` template that
  Mathlib uses for `Zsqrtd.commRing` (see
  `Mathlib/NumberTheory/Zsqrtd/Basic.lean` ≈ line 164).
* `norm` — the algebraic norm `N(a + bω) = a² - ab + b²`, together with
  the two structural identities
  - `norm_nonneg`: `0 ≤ norm z`, via `4 · norm z = (2re - im)² + 3 im²`,
  - `norm_mul`: `norm (x * y) = norm x * norm y`,
  - `norm_eq_zero_iff`: `norm z = 0 ↔ z = 0`.

## What is **not** in this file

The `EuclideanDomain` instance is deferred to S3, and the splitting /
extraction pipeline (`(-3/p) = (p/3)` via quadratic reciprocity, then
`4p = (2a - b)² + 3 b²` parity case-split) is deferred to S4-S5.

The above is sound foundation for both routes: the EuclideanDomain
instance is the canonical next step (S3), and the multiplicativity of
`norm` is the algebraic spine of every later argument.

This file has 0 axioms, 0 sorries.
-/

namespace Proofs

/-- The Eisenstein integers `ℤ[ω]`, where `ω = exp(2πi/3)` is a
primitive cube root of unity satisfying `ω² + ω + 1 = 0`. An element
`re + im · ω` is represented by its two integer coordinates. -/
@[ext]
structure Eisenstein where
  /-- The "rational" (real) coordinate of `re + im · ω`. -/
  re : ℤ
  /-- The "`ω`" coordinate of `re + im · ω`. -/
  im : ℤ
  deriving DecidableEq

namespace Eisenstein

/-- Convert an integer to an Eisenstein integer. -/
def ofInt (n : ℤ) : Eisenstein := ⟨n, 0⟩

theorem re_ofInt (n : ℤ) : (ofInt n).re = n := rfl
theorem im_ofInt (n : ℤ) : (ofInt n).im = 0 := rfl

instance : Zero Eisenstein := ⟨ofInt 0⟩
instance : One  Eisenstein := ⟨ofInt 1⟩

instance : Add Eisenstein :=
  ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg Eisenstein :=
  ⟨fun x => ⟨-x.re, -x.im⟩⟩

/-- The Eisenstein product. From `ω² = -1 - ω`:
`(a + bω)(c + dω) = ac + (ad + bc) ω + bd · ω²`
`               = ac + (ad + bc) ω + bd · (-1 - ω)`
`               = (ac - bd) + (ad + bc - bd) · ω`. -/
instance : Mul Eisenstein :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im,
               x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

@[simp] theorem zero_re : (0 : Eisenstein).re = 0 := rfl
@[simp] theorem zero_im : (0 : Eisenstein).im = 0 := rfl
@[simp] theorem one_re  : (1 : Eisenstein).re = 1 := rfl
@[simp] theorem one_im  : (1 : Eisenstein).im = 0 := rfl

@[simp] theorem add_re (x y : Eisenstein) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Eisenstein) : (x + y).im = x.im + y.im := rfl

@[simp] theorem neg_re (x : Eisenstein) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Eisenstein) : (-x).im = -x.im := rfl

@[simp] theorem mul_re (x y : Eisenstein) :
    (x * y).re = x.re * y.re - x.im * y.im := rfl

@[simp] theorem mul_im (x y : Eisenstein) :
    (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl

instance addCommGroup : AddCommGroup Eisenstein := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec Eisenstein ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec Eisenstein ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
             (@nsmulRec Eisenstein ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp] theorem sub_re (x y : Eisenstein) : (x - y).re = x.re - y.re := by
  show (x + -y).re = x.re - y.re
  simp [sub_eq_add_neg]

@[simp] theorem sub_im (x y : Eisenstein) : (x - y).im = x.im - y.im := by
  show (x + -y).im = x.im - y.im
  simp [sub_eq_add_neg]

instance addGroupWithOne : AddGroupWithOne Eisenstein :=
  { Eisenstein.addCommGroup with
    natCast := fun n => ofInt (n : ℤ)
    intCast := ofInt }

instance commRing : CommRing Eisenstein := by
  refine
  { Eisenstein.addGroupWithOne with
    npow := @npowRec Eisenstein ⟨1⟩ ⟨(· * ·)⟩
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

/-! ## The Eisenstein norm `N(a + bω) = a² - ab + b²` -/

/-- The Eisenstein norm: `N(a + bω) = a² - ab + b²`. -/
def norm (z : Eisenstein) : ℤ := z.re ^ 2 - z.re * z.im + z.im ^ 2

@[simp] theorem norm_zero : norm (0 : Eisenstein) = 0 := by
  simp [norm]

@[simp] theorem norm_one : norm (1 : Eisenstein) = 1 := by
  simp [norm]

/-- The Eisenstein norm is non-negative, via the algebraic identity
`4 · N(z) = (2 re - im)² + 3 · im²`. -/
theorem norm_nonneg (z : Eisenstein) : 0 ≤ norm z := by
  have h4 : (4 : ℤ) * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
    simp only [norm]; ring
  nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

/-- The Eisenstein norm is multiplicative:
`N((a + bω)(c + dω)) = N(a + bω) · N(c + dω)`. -/
theorem norm_mul (x y : Eisenstein) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_re, mul_im]
  ring

/-- The Eisenstein norm vanishes only on zero. -/
theorem norm_eq_zero_iff (z : Eisenstein) : norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    -- `4 · 0 = (2 re - im)² + 3 · im²`, so both squares vanish.
    have h4 : (4 : ℤ) * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
      simp only [norm]; ring
    rw [hz, mul_zero] at h4
    have him_sq : (3 : ℤ) * z.im ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]
    have him_sq' : z.im ^ 2 = 0 := by linarith [sq_nonneg z.im]
    have him : z.im = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp him_sq'
    have hre_sq : (2 * z.re - z.im) ^ 2 = 0 := by linarith
    have hre' : 2 * z.re - z.im = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hre_sq
    have hre : z.re = 0 := by
      have : 2 * z.re = z.im := by linarith
      rw [him] at this
      linarith
    ext <;> simp [hre, him]
  · rintro rfl
    simp

/-- The Eisenstein norm of a nonzero element is strictly positive. -/
theorem norm_pos_of_ne_zero {z : Eisenstein} (hz : z ≠ 0) : 0 < norm z := by
  have hnn := norm_nonneg z
  rcases lt_or_eq_of_le hnn with hpos | hzero
  · exact hpos
  · exfalso; exact hz ((norm_eq_zero_iff z).mp hzero.symm)

end Eisenstein

end Proofs
