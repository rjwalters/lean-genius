import Mathlib
import Proofs.GreensTheoremOQ01

/-
# OQ-03: Green's Theorem is Additive Under Subdivision

## The Open Question (greens-theorem-oq-01-oq-03)

The parent result `greens_theorem_concrete` (greens-theorem-oq-01) proves Green's
theorem for a *single* rectangle, and its Part VI flags the natural next step:
extending the identity from one rectangle to general regions.  The standard route
is to **tile** a region with rectangles and add the cell-wise identities, relying
on the fact that the contributions along shared interior edges cancel.

**Open question:** Are the two sides of Green's identity — the concrete boundary
line integral `rectLineIntegral` and the concrete double integral
`rectDoubleIntegral` — *additive under subdivision* of the rectangle, with shared
edges canceling by orientation?

## Answer: YES — and the cancellation is exact

We prove that both `rectLineIntegral` and `rectDoubleIntegral` split additively
when a rectangle `[a,b]×[c,d]` is cut by a vertical line `x = e` or a horizontal
line `y = g`:

  rectLineIntegral over [a,b] = rectLineIntegral over [a,e] + rectLineIntegral over [e,b]
  rectDoubleIntegral over [a,b] = rectDoubleIntegral over [a,e] + rectDoubleIntegral over [e,b]

For the **line integral** the interior edge `x = e` is traversed *upward* as the
right edge of the left cell (contribution `+∫_c^d Q(e,y)`) and *downward* as the
left edge of the right cell (contribution `−∫_c^d Q(e,y)`); the two cancel by pure
`ring` arithmetic — no hypothesis is needed for the cancellation itself.  The
outer boundary edges glue via `intervalIntegral.integral_add_adjacent_intervals`.

For the **double integral** the split is the additivity of the iterated integral
over adjacent sub-intervals.

Adding the two facts gives the capstone `greens_additive_vertical`: if Green's
theorem holds on the two sub-rectangles, it holds on their union.  This is exactly
the inductive step that lets one prove Green's theorem on a *staircase region*
(a finite union of rectangles) by proving it cell by cell — the interior edges
take care of themselves.

## What is new relative to the gallery

- The parent (oq-01) and the discharged-Fubini siblings (oq-01-oq-01, oq-01-oq-02)
  all work with a **fixed single rectangle**.  None of them prove that the Green
  identity *tiles*.
- The shared-edge cancellation `∫Q(e,·) − ∫Q(e,·) = 0` is the orientation
  phenomenon at the heart of every "cut the region into pieces" argument, here
  isolated as a reusable algebraic fact.
- No ordering hypotheses (`a ≤ e ≤ b`) are required: `integral_add_adjacent_intervals`
  is sign-aware, so the lemmas hold for signed/overlapping cuts as well.

## Proof Status

- [x] Vertical line-integral additivity (0 sorries)
- [x] Vertical double-integral additivity (0 sorries)
- [x] Horizontal line-integral additivity (0 sorries)
- [x] Horizontal double-integral additivity (0 sorries)
- [x] Capstone: Green's theorem glues across a vertical cut (0 sorries)
- [x] Concrete numeric sanity check (0 sorries)
-/

namespace GreensTheoremOQ01OQ03

open MeasureTheory intervalIntegral
open GreensTheoremOQ01

/-!
## Part I: Vertical subdivision (cut at `x = e`)

The interior edge is the vertical segment `x = e`.  It appears as the right edge
of the left cell `[a,e]×[c,d]` and as the left edge of the right cell
`[e,b]×[c,d]`, with opposite orientations.
-/

/-- **Line integral is additive under a vertical cut.**

    Splitting `[a,b]×[c,d]` at `x = e`, the boundary line integral of the whole
    rectangle equals the sum of the boundary line integrals of the two halves.

    The shared interior edge `x = e` contributes `+∫_c^d Q(e,y)` to the left cell
    and `−∫_c^d Q(e,y)` to the right cell; these cancel identically.  Only the
    outer edges (`P(·,c)` and `P(·,d)` integrated in `x`) need to be glued, via
    `integral_add_adjacent_intervals` — hence the four integrability hypotheses. -/
theorem rectLineIntegral_vsplit (P Q : ℝ × ℝ → ℝ) (a e b c d : ℝ)
    (hPc_ae : IntervalIntegrable (fun x => P (x, c)) volume a e)
    (hPc_eb : IntervalIntegrable (fun x => P (x, c)) volume e b)
    (hPd_ae : IntervalIntegrable (fun x => P (x, d)) volume a e)
    (hPd_eb : IntervalIntegrable (fun x => P (x, d)) volume e b) :
    rectLineIntegral P Q a e c d + rectLineIntegral P Q e b c d =
    rectLineIntegral P Q a b c d := by
  have hc : (∫ x in a..e, P (x, c)) + ∫ x in e..b, P (x, c) = ∫ x in a..b, P (x, c) :=
    integral_add_adjacent_intervals hPc_ae hPc_eb
  have hd : (∫ x in a..e, P (x, d)) + ∫ x in e..b, P (x, d) = ∫ x in a..b, P (x, d) :=
    integral_add_adjacent_intervals hPd_ae hPd_eb
  simp only [rectLineIntegral]
  -- the `∫ Q(e,·)` terms cancel; the `P(·,c)` and `P(·,d)` terms glue via hc, hd
  linarith [hc, hd]

/-- **Double integral is additive under a vertical cut.**

    `∬_{[a,b]×[c,d]} f = ∬_{[a,e]×[c,d]} f + ∬_{[e,b]×[c,d]} f`.

    Inner additivity of `∫_a^e f(·,y) + ∫_e^b f(·,y) = ∫_a^b f(·,y)` (pointwise in
    `y`) is lifted through the outer `y`-integral. -/
theorem rectDoubleIntegral_vsplit (f : ℝ × ℝ → ℝ) (a e b c d : ℝ)
    (hf_ae : ∀ y ∈ Set.uIcc c d, IntervalIntegrable (fun x => f (x, y)) volume a e)
    (hf_eb : ∀ y ∈ Set.uIcc c d, IntervalIntegrable (fun x => f (x, y)) volume e b)
    (hfo_ae : IntervalIntegrable (fun y => ∫ x in a..e, f (x, y)) volume c d)
    (hfo_eb : IntervalIntegrable (fun y => ∫ x in e..b, f (x, y)) volume c d) :
    rectDoubleIntegral f a e c d + rectDoubleIntegral f e b c d =
    rectDoubleIntegral f a b c d := by
  have hinner : ∀ y ∈ Set.uIcc c d,
      (∫ x in a..e, f (x, y)) + (∫ x in e..b, f (x, y)) = ∫ x in a..b, f (x, y) :=
    fun y hy => integral_add_adjacent_intervals (hf_ae y hy) (hf_eb y hy)
  simp only [rectDoubleIntegral]
  rw [← integral_add hfo_ae hfo_eb]
  exact integral_congr hinner

/-!
## Part II: Horizontal subdivision (cut at `y = g`)

By symmetry, the interior edge is the horizontal segment `y = g`, shared (with
opposite orientation) by the bottom cell `[a,b]×[c,g]` and the top cell
`[a,b]×[g,d]`.
-/

/-- **Line integral is additive under a horizontal cut.**

    Splitting `[a,b]×[c,d]` at `y = g`.  The shared edge `y = g` contributes
    `−∫_a^b P(x,g)` to the bottom cell and `+∫_a^b P(x,g)` to the top cell; these
    cancel.  The outer edges (`Q(b,·)` and `Q(a,·)` integrated in `y`) glue via
    `integral_add_adjacent_intervals`. -/
theorem rectLineIntegral_hsplit (P Q : ℝ × ℝ → ℝ) (a b c g d : ℝ)
    (hQb_cg : IntervalIntegrable (fun y => Q (b, y)) volume c g)
    (hQb_gd : IntervalIntegrable (fun y => Q (b, y)) volume g d)
    (hQa_cg : IntervalIntegrable (fun y => Q (a, y)) volume c g)
    (hQa_gd : IntervalIntegrable (fun y => Q (a, y)) volume g d) :
    rectLineIntegral P Q a b c g + rectLineIntegral P Q a b g d =
    rectLineIntegral P Q a b c d := by
  have hb : (∫ y in c..g, Q (b, y)) + ∫ y in g..d, Q (b, y) = ∫ y in c..d, Q (b, y) :=
    integral_add_adjacent_intervals hQb_cg hQb_gd
  have ha : (∫ y in c..g, Q (a, y)) + ∫ y in g..d, Q (a, y) = ∫ y in c..d, Q (a, y) :=
    integral_add_adjacent_intervals hQa_cg hQa_gd
  simp only [rectLineIntegral]
  -- the `∫ P(·,g)` terms cancel; the `Q(b,·)` and `Q(a,·)` terms glue via hb, ha
  linarith [hb, ha]

/-- **Double integral is additive under a horizontal cut.**

    `∬_{[a,b]×[c,d]} f = ∬_{[a,b]×[c,g]} f + ∬_{[a,b]×[g,d]} f`.  Here the split is
    a single application of adjacent-interval additivity on the *outer* integral. -/
theorem rectDoubleIntegral_hsplit (f : ℝ × ℝ → ℝ) (a b c g d : ℝ)
    (hfo_cg : IntervalIntegrable (fun y => ∫ x in a..b, f (x, y)) volume c g)
    (hfo_gd : IntervalIntegrable (fun y => ∫ x in a..b, f (x, y)) volume g d) :
    rectDoubleIntegral f a b c g + rectDoubleIntegral f a b g d =
    rectDoubleIntegral f a b c d := by
  simp only [rectDoubleIntegral]
  exact integral_add_adjacent_intervals hfo_cg hfo_gd

/-!
## Part III: Capstone — Green's theorem glues across a cut

If Green's identity holds on each of two sub-rectangles meeting along a vertical
interior edge, it holds on their union.  Because both sides are additive
(`rectLineIntegral_vsplit`, `rectDoubleIntegral_vsplit`) the proof is a pure
rewrite — the interior edge cancels with no extra input.  This is the inductive
step for proving Green's theorem on any rectangle-tiled region.
-/

/-- **Green's theorem is preserved by vertical subdivision (gluing).**

    Given that the concrete Green identity holds on the left cell `[a,e]×[c,d]`
    and the right cell `[e,b]×[c,d]` for the curl field `F`, it holds on the whole
    rectangle `[a,b]×[c,d]`.  The four line-integral and four double-integral
    integrability hypotheses are exactly those that make the two sides additive. -/
theorem greens_additive_vertical (P Q F : ℝ × ℝ → ℝ) (a e b c d : ℝ)
    -- gluing data for the line integral
    (hPc_ae : IntervalIntegrable (fun x => P (x, c)) volume a e)
    (hPc_eb : IntervalIntegrable (fun x => P (x, c)) volume e b)
    (hPd_ae : IntervalIntegrable (fun x => P (x, d)) volume a e)
    (hPd_eb : IntervalIntegrable (fun x => P (x, d)) volume e b)
    -- gluing data for the double integral
    (hF_ae : ∀ y ∈ Set.uIcc c d, IntervalIntegrable (fun x => F (x, y)) volume a e)
    (hF_eb : ∀ y ∈ Set.uIcc c d, IntervalIntegrable (fun x => F (x, y)) volume e b)
    (hFo_ae : IntervalIntegrable (fun y => ∫ x in a..e, F (x, y)) volume c d)
    (hFo_eb : IntervalIntegrable (fun y => ∫ x in e..b, F (x, y)) volume c d)
    -- Green's theorem on each cell
    (hL : rectLineIntegral P Q a e c d = rectDoubleIntegral F a e c d)
    (hR : rectLineIntegral P Q e b c d = rectDoubleIntegral F e b c d) :
    rectLineIntegral P Q a b c d = rectDoubleIntegral F a b c d := by
  rw [← rectLineIntegral_vsplit P Q a e b c d hPc_ae hPc_eb hPd_ae hPd_eb,
      ← rectDoubleIntegral_vsplit F a e b c d hF_ae hF_eb hFo_ae hFo_eb, hL, hR]

/-!
## Part IV: Concrete sanity check

A fully concrete instance: the area of the unit square computed as
`∬ 1` splits at `x = 1/2` into two half-rectangles of area `1/2` each.
-/

/-- The double integral of `1` over `[0,1]²` equals the sum of its values over the
    two halves `[0,½]×[0,1]` and `[½,1]×[0,1]`, each `½`. -/
theorem area_vsplit_unit_square :
    rectDoubleIntegral (fun _ => 1) 0 (1/2) 0 1 +
    rectDoubleIntegral (fun _ => 1) (1/2) 1 0 1 =
    rectDoubleIntegral (fun _ => 1) 0 1 0 1 := by
  rw [area_double_integral, area_double_integral, area_double_integral]
  ring

#check @rectLineIntegral_vsplit
#check @rectDoubleIntegral_vsplit
#check @rectLineIntegral_hsplit
#check @rectDoubleIntegral_hsplit
#check @greens_additive_vertical

end GreensTheoremOQ01OQ03
