import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-
# Field-theoretic characterization of origami-constructible numbers (OQ-04 / OQ-02)

## Question
What is the exact field-theoretic characterization of origami-constructible
numbers?

## Answer formalized here

The parent entry (`angle-trisection-oq-04`) and its sibling
(`angle-trisection-oq-04-oq-01`) describe the *arithmetic shadow* of the
characterization: a degree `d` is achievable iff it divides some `2^a · 3^b`
(a "2-3 number").  This entry gives the underlying **field-theoretic** object
and proves the structural theorems that pin it down.

Origami (Huzita–Justin, single-fold) constructions can carry out every
straightedge-and-compass operation *and* extract real cube roots.  The exact
field-theoretic statement is therefore:

> The origami-constructible numbers form the **smallest subfield of `ℂ`
> closed under taking square roots and cube roots.**

We define this field as an inductive closure `IsOrigami : ℂ → Prop`, package it
as a `Subfield ℂ`, and prove:

1. **Structure** — `origamiField` is a subfield of `ℂ` (`origamiField`).
2. **Closure** — it is closed under square roots, cube roots, and complex
   conjugation.
3. **Minimality / exact characterization** — it is the *least* subfield of `ℂ`
   closed under square and cube roots (`origamiField_isLeast`).  This is the
   precise field-theoretic characterization asked for.
4. **It solves quadratics and cubics** — every root of a quadratic or cubic
   with origami coefficients is again origami (`origamiField_root_quadratic`,
   `origamiField_cubic_has_root`, `origamiField_root_cubic`).  This is the
   operational content: cube-root extraction is exactly the new power that
   straightedge-and-compass lacks.
5. **Witnesses** — `i`, a cube root of `2` (doubling the cube), and `cos 20°`
   (angle trisection) are all origami; the last via the triple-angle cubic
   `8x³ - 6x - 1 = 0`.

## Relation to the arithmetic characterization
The minimal-polynomial degree of an origami number divides some `2^a · 3^b`
(necessity is the Galois-theoretic shadow proved arithmetically in the sibling
entry via `IsTwoThreeNumber`).  Sufficiency at the level of *fields* is exactly
the minimality theorem here: any number reachable by a tower of degree-`{2,3}`
extensions lies in `origamiField`, because `origamiField` is closed under the
square and cube roots that generate such towers.

## Status
- All results proved; 0 sorries, 0 `axiom` declarations.
- `Complex.isAlgClosed` is used only to *exhibit* roots; no proof depends on it
  for correctness of the characterization.
-/

namespace AngleTrisectionOQ04OQ02

open Complex

/-- **Origami-constructible numbers.**  The inductive closure of `ℚ` inside `ℂ`
under the field operations together with square-root and cube-root extraction.
This is the field obtained from the Huzita–Justin paper-folding axioms. -/
inductive IsOrigami : ℂ → Prop
  | rat (q : ℚ) : IsOrigami (q : ℂ)
  | add {a b : ℂ} : IsOrigami a → IsOrigami b → IsOrigami (a + b)
  | neg {a : ℂ} : IsOrigami a → IsOrigami (-a)
  | mul {a b : ℂ} : IsOrigami a → IsOrigami b → IsOrigami (a * b)
  | inv {a : ℂ} : IsOrigami a → IsOrigami a⁻¹
  | sqrt {a w : ℂ} : IsOrigami a → w ^ 2 = a → IsOrigami w
  | cbrt {a w : ℂ} : IsOrigami a → w ^ 3 = a → IsOrigami w

namespace IsOrigami

theorem zero : IsOrigami 0 := by simpa using IsOrigami.rat 0

theorem one : IsOrigami 1 := by simpa using IsOrigami.rat 1

theorem sub {a b : ℂ} (ha : IsOrigami a) (hb : IsOrigami b) : IsOrigami (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

theorem div {a b : ℂ} (ha : IsOrigami a) (hb : IsOrigami b) : IsOrigami (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

end IsOrigami

/-- The origami-constructible numbers form a subfield of `ℂ`. -/
def origamiField : Subfield ℂ where
  carrier := {z | IsOrigami z}
  mul_mem' := IsOrigami.mul
  one_mem' := IsOrigami.one
  add_mem' := IsOrigami.add
  zero_mem' := IsOrigami.zero
  neg_mem' := IsOrigami.neg
  inv_mem' := fun _ h => IsOrigami.inv h

@[simp] theorem mem_origamiField {z : ℂ} : z ∈ origamiField ↔ IsOrigami z := Iff.rfl

/-! ### Closure properties -/

/-- `origamiField` is closed under square roots: every square root of an origami
number is origami. -/
theorem origamiField_sqrt_closed {a w : ℂ} (ha : a ∈ origamiField) (hw : w ^ 2 = a) :
    w ∈ origamiField := IsOrigami.sqrt ha hw

/-- `origamiField` is closed under cube roots: every cube root of an origami
number is origami. -/
theorem origamiField_cbrt_closed {a w : ℂ} (ha : a ∈ origamiField) (hw : w ^ 3 = a) :
    w ∈ origamiField := IsOrigami.cbrt ha hw

/-- Origami numbers are closed under complex conjugation. -/
theorem origamiField_conj_closed {z : ℂ} (hz : z ∈ origamiField) :
    (starRingEnd ℂ) z ∈ origamiField := by
  rw [mem_origamiField] at hz ⊢
  induction hz with
  | rat q => simpa using IsOrigami.rat q
  | add _ _ ih1 ih2 => simpa [map_add] using ih1.add ih2
  | neg _ ih => simpa [map_neg] using ih.neg
  | mul _ _ ih1 ih2 => simpa [map_mul] using ih1.mul ih2
  | inv _ ih => simpa [map_inv₀] using ih.inv
  | sqrt _ hw ih => exact IsOrigami.sqrt ih (by rw [← map_pow, hw])
  | cbrt _ hw ih => exact IsOrigami.cbrt ih (by rw [← map_pow, hw])

/-! ### The field-theoretic characterization (minimality) -/

/-- **Minimality.**  Any subfield of `ℂ` that is closed under square roots and
cube roots contains every origami number.  Combined with the closure properties
above, this says `origamiField` is the *smallest* subfield of `ℂ` closed under
both operations — the exact field-theoretic characterization. -/
theorem origamiField_le_of_closed (K : Subfield ℂ)
    (hsq : ∀ a ∈ K, ∀ w : ℂ, w ^ 2 = a → w ∈ K)
    (hcb : ∀ a ∈ K, ∀ w : ℂ, w ^ 3 = a → w ∈ K) :
    origamiField ≤ K := by
  intro z hz
  rw [mem_origamiField] at hz
  induction hz with
  | rat q => exact SubfieldClass.ratCast_mem K q
  | add _ _ ih1 ih2 => exact K.add_mem ih1 ih2
  | neg _ ih => exact K.neg_mem ih
  | mul _ _ ih1 ih2 => exact K.mul_mem ih1 ih2
  | inv _ ih => exact K.inv_mem ih
  | sqrt _ hw ih => exact hsq _ ih _ hw
  | cbrt _ hw ih => exact hcb _ ih _ hw

/-- The closure conditions, packaged as a predicate on subfields of `ℂ`. -/
def ClosedUnderRoots (K : Subfield ℂ) : Prop :=
  (∀ a ∈ K, ∀ w : ℂ, w ^ 2 = a → w ∈ K) ∧ (∀ a ∈ K, ∀ w : ℂ, w ^ 3 = a → w ∈ K)

/-- **Exact field-theoretic characterization.**  `origamiField` is the least
element of the set of subfields of `ℂ` closed under square roots and cube roots. -/
theorem origamiField_isLeast :
    IsLeast {K : Subfield ℂ | ClosedUnderRoots K} origamiField := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact fun a ha w hw => origamiField_sqrt_closed ha hw
  · exact fun a ha w hw => origamiField_cbrt_closed ha hw
  · rintro K ⟨hsq, hcb⟩
    exact origamiField_le_of_closed K hsq hcb

/-! ### Helper memberships for small constants -/

theorem two_mem : (2 : ℂ) ∈ origamiField := by exact_mod_cast SubfieldClass.ratCast_mem origamiField 2

theorem three_mem : (3 : ℂ) ∈ origamiField := by exact_mod_cast SubfieldClass.ratCast_mem origamiField 3

/-! ### Origami solves quadratics and cubics -/

/-- **Every root of an origami quadratic is origami.**  If `b, c` are origami and
`r² + b·r + c = 0`, then `r` is origami.  (Completing the square exhibits
`2r + b` as a square root of the origami number `b² - 4c`.) -/
theorem origamiField_root_quadratic {b c r : ℂ}
    (hb : b ∈ origamiField) (hc : c ∈ origamiField) (hr : r ^ 2 + b * r + c = 0) :
    r ∈ origamiField := by
  -- `2r + b` squares to the origami number `b² - 4c`.
  have hD : (b ^ 2 - 4 * c) ∈ origamiField :=
    sub_mem (origamiField.pow_mem hb 2) (mul_mem (by exact_mod_cast SubfieldClass.ratCast_mem origamiField 4) hc)
  have hsq : (2 * r + b) ^ 2 = b ^ 2 - 4 * c := by linear_combination 4 * hr
  have hmem : (2 * r + b) ∈ origamiField := origamiField_sqrt_closed hD hsq
  -- recover `r = ((2r + b) - b) / 2`.
  have : r = ((2 * r + b) - b) / 2 := by ring
  rw [this]
  exact origamiField.div_mem (sub_mem hmem hb) two_mem

/-- **Origami solves depressed cubics.**  For origami coefficients `p, q` there is
an origami root of `r³ + p·r + q = 0`.  This is Cardano's formula: cube-root
extraction (the new power origami adds over straightedge-and-compass) suffices. -/
theorem origamiField_cubic_has_root {p q : ℂ}
    (hp : p ∈ origamiField) (hq : q ∈ origamiField) :
    ∃ r ∈ origamiField, r ^ 3 + p * r + q = 0 := by
  -- discriminant term `Δ = (q/2)² + (p/3)³`
  have hΔ : ((q / 2) ^ 2 + (p / 3) ^ 3) ∈ origamiField :=
    add_mem (origamiField.pow_mem (origamiField.div_mem hq two_mem) 2)
      (origamiField.pow_mem (origamiField.div_mem hp three_mem) 3)
  -- a square root `s` of `Δ`
  obtain ⟨s, hs2⟩ :=
    IsAlgClosed.exists_pow_nat_eq (k := ℂ) ((q / 2) ^ 2 + (p / 3) ^ 3) (n := 2) (by norm_num)
  have hsO : s ∈ origamiField := origamiField_sqrt_closed hΔ hs2
  -- a cube root `u` of `A = -q/2 + s`
  have hA : (-q / 2 + s) ∈ origamiField :=
    add_mem (origamiField.div_mem (neg_mem hq) two_mem) hsO
  obtain ⟨u, hu3⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (-q / 2 + s) (n := 3) (by norm_num)
  have huO : u ∈ origamiField := origamiField_cbrt_closed hA hu3
  by_cases hu : u = 0
  · -- degenerate branch: `A = 0` forces `p = 0`; then `r³ = -q`.
    have hA0 : (-q / 2 + s) = 0 := by rw [← hu3, hu]; ring
    have hs_eq : s = q / 2 := by linear_combination hA0
    have hp3 : (p / 3) ^ 3 = 0 := by
      have hsΔ : s ^ 2 = (q / 2) ^ 2 + (p / 3) ^ 3 := hs2
      rw [hs_eq] at hsΔ
      linear_combination -hsΔ
    have hp0 : p = 0 := by
      have h3 : p / 3 = 0 := (pow_eq_zero_iff (n := 3) (by norm_num)).mp hp3
      linear_combination 3 * h3
    obtain ⟨r, hr3⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (-q) (n := 3) (by norm_num)
    exact ⟨r, origamiField_cbrt_closed (neg_mem hq) hr3, by rw [hp0, hr3]; ring⟩
  · -- main branch: `v = -p/(3u)`, root is `u + v`.
    have h3u : (3 : ℂ) * u ≠ 0 := mul_ne_zero (by norm_num) hu
    -- `v³ = -q/2 - s` (Cardano's resolvent identity)
    have hv3 : (-p / (3 * u)) ^ 3 = -q / 2 - s := by
      rw [div_pow, div_eq_iff (pow_ne_zero 3 h3u)]
      linear_combination (-27 * (-q / 2 - s)) * hu3 + 27 * hs2
    have hvO : (-p / (3 * u)) ∈ origamiField :=
      origamiField.div_mem (neg_mem hp) (mul_mem three_mem huO)
    have hprod : 3 * u * (-p / (3 * u)) = -p := by
      rw [mul_comm]; exact div_mul_cancel₀ _ h3u
    refine ⟨u + (-p / (3 * u)), add_mem huO hvO, ?_⟩
    have key : (u + (-p / (3 * u))) ^ 3 + p * (u + (-p / (3 * u))) + q
        = (u ^ 3 + (-p / (3 * u)) ^ 3 + q)
          + (3 * u * (-p / (3 * u)) + p) * (u + (-p / (3 * u))) := by ring
    rw [key, hu3, hv3, hprod]
    ring

/-- Repackaging: every root of an origami depressed cubic is origami. -/
theorem origamiField_root_cubic {p q r : ℂ}
    (hp : p ∈ origamiField) (hq : q ∈ origamiField) (hr : r ^ 3 + p * r + q = 0) :
    r ∈ origamiField := by
  obtain ⟨r₀, hr₀mem, hr₀⟩ := origamiField_cubic_has_root hp hq
  -- factor: `(r - r₀) * (r² + r₀·r + (r₀² + p)) = 0`
  have hfac : (r - r₀) * (r ^ 2 + r₀ * r + (r₀ ^ 2 + p)) = 0 := by
    have : r ^ 3 + p * r + q - (r₀ ^ 3 + p * r₀ + q) = 0 := by rw [hr, hr₀]; ring
    linear_combination this
  rcases mul_eq_zero.mp hfac with h | h
  · -- `r = r₀`
    have : r = r₀ := by linear_combination h
    rw [this]; exact hr₀mem
  · -- `r` is a root of the origami quadratic `x² + r₀·x + (r₀² + p)`
    refine origamiField_root_quadratic hr₀mem (add_mem (origamiField.pow_mem hr₀mem 2) hp) ?_
    linear_combination h

/-! ### Witnesses -/

theorem isOrigami_neg_one : IsOrigami (-1 : ℂ) := by
  simpa using (IsOrigami.rat (-1))

/-- The imaginary unit `i` is origami (square root of `-1`). -/
theorem isOrigami_I : IsOrigami Complex.I := by
  apply IsOrigami.sqrt isOrigami_neg_one
  exact Complex.I_sq

/-- **Doubling the cube.**  A cube root of `2` is origami — impossible with
straightedge and compass, possible with origami. -/
theorem exists_origami_cbrt_two : ∃ w : ℂ, w ^ 3 = 2 ∧ IsOrigami w := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (2 : ℂ) (n := 3) (by norm_num)
  exact ⟨w, hw, IsOrigami.cbrt two_mem hw⟩

/-- **Angle trisection.**  `cos 20°` is origami.  It is a root of the depressed
cubic `x³ - (3/4)x - 1/8 = 0` obtained from the triple-angle identity
`4cos³θ - 3cosθ = cos 3θ` at `θ = 20° = π/9`. -/
theorem isOrigami_cos_pi_div_nine :
    (((Real.cos (Real.pi / 9) : ℝ) : ℂ)) ∈ origamiField := by
  have htriple : Real.cos (Real.pi / 9) ^ 3 - (3 / 4) * Real.cos (Real.pi / 9) - 1 / 8 = 0 := by
    have h3 : (3 : ℝ) * (Real.pi / 9) = Real.pi / 3 := by ring
    have hcos := Real.cos_three_mul (Real.pi / 9)
    rw [h3, Real.cos_pi_div_three] at hcos
    -- hcos : 1/2 = 4 cos³ - 3 cos
    linarith [hcos]
  -- transport the cubic to ℂ
  have hcubicC : (((Real.cos (Real.pi / 9) : ℝ) : ℂ)) ^ 3
      + (-(3 / 4)) * (((Real.cos (Real.pi / 9) : ℝ) : ℂ)) + (-(1 / 8)) = 0 := by
    have := htriple
    push_cast
    have hcast : (((Real.cos (Real.pi / 9) ^ 3 - (3 / 4) * Real.cos (Real.pi / 9) - 1 / 8 : ℝ)) : ℂ)
        = 0 := by rw [htriple]; simp
    push_cast at hcast
    linear_combination hcast
  refine origamiField_root_cubic ?_ ?_ hcubicC
  · exact neg_mem (by simpa using SubfieldClass.ratCast_mem origamiField (3 / 4))
  · exact neg_mem (by simpa using SubfieldClass.ratCast_mem origamiField (1 / 8))

end AngleTrisectionOQ04OQ02
