/-
  # Transcendence is Preserved by Algebraic Operations

  The parent gallery proof (`AlgebraicNumbersCountable`) shows that the algebraic
  numbers are a *countable* subset of ℝ and ℂ, and sibling leaves push the
  cardinality/measure/category side of the algebraic–transcendental dichotomy
  (ℝ uncountable, transcendentals have cardinality 𝔠, transcendentals are a dense
  Gδ, the algebraic reals are Lebesgue-null, …).

  This file develops the **arithmetic/field structure** of that dichotomy, which
  none of the existing leaves touch. Two complementary themes:

  ## 1. The algebraic numbers form a subfield

  For any field extension `K ⊆ L`, the elements of `L` that are algebraic over `K`
  are closed under `+`, `-`, `*` and `⁻¹`, hence form a subfield
  `algebraicSubfield K L : Subfield L`. Combined with the parent's countability
  result this upgrades "countable set" to "countable subfield of ℂ".

  The closure proofs route algebraicity through integrality
  (`isAlgebraic_iff_isIntegral`, valid because `K` is a field) where Mathlib already
  proves the integral elements form a subring (`IsIntegral.add/sub/mul/neg`), and
  through `IsAlgebraic.inv` for the multiplicative inverse.

  ## 2. Transcendence is preserved by algebraic operations

  Dually, if `t` is transcendental over `K` and `a` is algebraic over `K`, then
  every "algebraic perturbation" of `t` is again transcendental:

  * `t + a`, `a + t`, `t - a`, `a - t`           (additive translates)
  * `a * t`, `t * a`     for `a ≠ 0`             (nonzero rescalings)
  * `t⁻¹`, `-t`, `t ^ n` for `n > 0`             (inversion, negation, powers)
  * `a * t + b`          for `a ≠ 0`             (arbitrary algebraic affine map)

  Each follows from the subfield structure of §1 by a one-line "back-substitution"
  contradiction: e.g. if `t + a` were algebraic then `t = (t + a) - a` would be a
  difference of algebraics, hence algebraic — contradicting transcendence of `t`.

  These are exactly the elementary closure facts used at the start of every concrete
  transcendence argument (Lindemann–Weierstrass, Baker, …): once `e` is known
  transcendental, `e + 1`, `e²`, `1/e`, `2e - 3` are transcendental for free.

  In contrast, the **transcendentals are not closed** under these operations:
  `t` and `1 - t` are both transcendental but their sum `1` is algebraic
  (`transcendentals_not_add_closed`). So the algebraic numbers are the subfield and
  the transcendentals are exactly its (set-theoretic) complement — never a subfield.

  Tags: field-theory, algebraic-numbers, transcendental-numbers, subfield,
        integral-closure
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic

namespace AlgebraicNumbersCountableOQ01

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/- ============================================================
   § 1 : The algebraic numbers form a subfield
   ============================================================ -/

/-- Sum of algebraic elements is algebraic (over a field, via integral closure). -/
theorem isAlgebraic_add {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x + y) := by
  rw [isAlgebraic_iff_isIntegral] at hx hy ⊢
  exact hx.add hy

/-- Negation of an algebraic element is algebraic. -/
theorem isAlgebraic_neg {x : L} (hx : IsAlgebraic K x) : IsAlgebraic K (-x) := by
  rw [isAlgebraic_iff_isIntegral] at hx ⊢
  exact hx.neg

/-- Difference of algebraic elements is algebraic. -/
theorem isAlgebraic_sub {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x - y) := by
  rw [isAlgebraic_iff_isIntegral] at hx hy ⊢
  exact hx.sub hy

/-- Product of algebraic elements is algebraic. -/
theorem isAlgebraic_mul {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x * y) := by
  rw [isAlgebraic_iff_isIntegral] at hx hy ⊢
  exact hx.mul hy

/-- Inverse of an algebraic element is algebraic (in a field extension). -/
theorem isAlgebraic_inv {x : L} (hx : IsAlgebraic K x) : IsAlgebraic K x⁻¹ := hx.inv

/-- The elements of `L` algebraic over `K` form a subfield of `L`. When `K = ℚ` and
    `L = ℂ` this is the field of algebraic numbers; the parent proof shows it is
    countable, so this is a *countable subfield* of ℂ. -/
def algebraicSubfield (K L : Type*) [Field K] [Field L] [Algebra K L] : Subfield L where
  carrier := {x | IsAlgebraic K x}
  mul_mem' := fun hx hy => isAlgebraic_mul hx hy
  one_mem' := isAlgebraic_one
  add_mem' := fun hx hy => isAlgebraic_add hx hy
  zero_mem' := isAlgebraic_zero
  neg_mem' := fun hx => isAlgebraic_neg hx
  inv_mem' := fun _ hx => isAlgebraic_inv hx

@[simp] theorem mem_algebraicSubfield {x : L} :
    x ∈ algebraicSubfield K L ↔ IsAlgebraic K x := Iff.rfl

/- ============================================================
   § 2 : Transcendence is preserved by algebraic operations
   ============================================================ -/

/-- The negation of a transcendental element is transcendental. -/
theorem transcendental_neg {t : L} (ht : Transcendental K t) : Transcendental K (-t) := by
  intro h
  exact ht (by simpa using isAlgebraic_neg h)

/-- Transcendental plus algebraic is transcendental. -/
theorem transcendental_add_algebraic {t a : L} (ht : Transcendental K t)
    (ha : IsAlgebraic K a) : Transcendental K (t + a) := by
  intro h
  -- if `t + a` is algebraic then `t = (t + a) - a` is algebraic
  exact ht (by simpa using isAlgebraic_sub h ha)

/-- Algebraic plus transcendental is transcendental. -/
theorem transcendental_algebraic_add {t a : L} (ht : Transcendental K t)
    (ha : IsAlgebraic K a) : Transcendental K (a + t) := by
  intro h
  exact ht (by simpa using isAlgebraic_sub h ha)

/-- Transcendental minus algebraic is transcendental. -/
theorem transcendental_sub_algebraic {t a : L} (ht : Transcendental K t)
    (ha : IsAlgebraic K a) : Transcendental K (t - a) := by
  simpa [sub_eq_add_neg] using transcendental_add_algebraic ht (isAlgebraic_neg ha)

/-- Algebraic minus transcendental is transcendental. -/
theorem transcendental_algebraic_sub {t a : L} (ht : Transcendental K t)
    (ha : IsAlgebraic K a) : Transcendental K (a - t) := by
  simpa [sub_eq_add_neg] using transcendental_algebraic_add (transcendental_neg ht) ha

/-- A nonzero algebraic times a transcendental is transcendental. -/
theorem transcendental_algebraic_mul {t a : L} (ht : Transcendental K t)
    (ha : IsAlgebraic K a) (ha0 : a ≠ 0) : Transcendental K (a * t) := by
  intro h
  apply ht
  -- if `a * t` is algebraic then `t = a⁻¹ * (a * t)` is algebraic
  have := isAlgebraic_mul (isAlgebraic_inv ha) h
  simpa [inv_mul_cancel_left₀ ha0] using this

/-- A transcendental times a nonzero algebraic is transcendental. -/
theorem transcendental_mul_algebraic {t a : L} (ht : Transcendental K t)
    (ha : IsAlgebraic K a) (ha0 : a ≠ 0) : Transcendental K (t * a) := by
  rw [mul_comm]
  exact transcendental_algebraic_mul ht ha ha0

/-- The inverse of a transcendental element is transcendental. -/
theorem transcendental_inv {t : L} (ht : Transcendental K t) : Transcendental K t⁻¹ := by
  intro h
  exact ht (by simpa using isAlgebraic_inv h)

/-- A positive power of a transcendental element is transcendental
    (a direct specialization of Mathlib's `Transcendental.pow`). -/
theorem transcendental_pow {t : L} (ht : Transcendental K t) {n : ℕ} (hn : 0 < n) :
    Transcendental K (t ^ n) := ht.pow hn

/-- **Affine images.** For `a ≠ 0` and `a, b` algebraic, the algebraic affine map
    `t ↦ a * t + b` sends every transcendental to a transcendental. This packages
    the additive and multiplicative cases and is the form most often used in
    practice. -/
theorem transcendental_affine {t a b : L} (ht : Transcendental K t)
    (ha : IsAlgebraic K a) (hb : IsAlgebraic K b) (ha0 : a ≠ 0) :
    Transcendental K (a * t + b) :=
  transcendental_add_algebraic (transcendental_algebraic_mul ht ha ha0) hb

/- ============================================================
   § 3 : The transcendentals are NOT closed (contrast with §1)
   ============================================================ -/

/-- The transcendentals do not form a subfield: for any transcendental `t`, the
    element `1 - t` is also transcendental, yet their sum `t + (1 - t) = 1` is
    algebraic. So, unlike the algebraic numbers (§1), the transcendentals are not
    closed under addition. -/
theorem transcendentals_not_add_closed {t : L} (ht : Transcendental K t) :
    Transcendental K (1 - t) ∧ IsAlgebraic K (t + (1 - t)) := by
  refine ⟨transcendental_algebraic_sub ht isAlgebraic_one, ?_⟩
  have h : t + (1 - t) = (1 : L) := by ring
  rw [h]
  exact isAlgebraic_one

/- ============================================================
   § 4 : Sanity checks — concrete consequences over ℚ ⊆ ℂ
   ============================================================ -/

section Examples

variable {t : ℂ} (ht : Transcendental ℚ t)

-- Translating by the algebraic number `1` keeps transcendence.
example : Transcendental ℚ (t + 1) := transcendental_add_algebraic ht isAlgebraic_one

-- The reciprocal of a transcendental is transcendental.
example : Transcendental ℚ t⁻¹ := transcendental_inv ht

-- Squares of transcendentals are transcendental.
example : Transcendental ℚ (t ^ 2) := transcendental_pow ht (by norm_num)

-- `1 - t` is transcendental but the algebraic number `1` is a sum of two transcendentals.
example : Transcendental ℚ (1 - t) := (transcendentals_not_add_closed ht).1

end Examples

end AlgebraicNumbersCountableOQ01
