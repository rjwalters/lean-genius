import Mathlib
import Proofs.GreensTheoremOQ01OQ03

/-
# OQ-03 → OQ-02: Green's Theorem Glues Across a 2D Grid of Cells

## The Open Question (greens-theorem-oq-01-oq-03-oq-02)

The parent `greens-theorem-oq-01-oq-03` (`GreensTheoremOQ01OQ03.lean`) proved that
both sides of the concrete Green identity are **additive under a single cut** — a
vertical cut `x = e` *or* a horizontal cut `y = g` — and packaged the vertical
direction into the gluing capstone `greens_additive_vertical`: if Green's theorem
holds on the left and right sub-rectangles meeting along the interior edge `x = e`,
it holds on their union.  It left two natural next steps:

1. the **horizontal** companion capstone `greens_additive_horizontal` (mirror of
   the vertical one, gluing a bottom cell and a top cell across `y = g`);
2. a **two-dimensional** gluing lemma — the first genuine *grid* statement —
   showing Green's theorem tiles across **both** cut directions at once.

This file supplies both.

## Results

* `greens_additive_horizontal` — Green's theorem is preserved by a horizontal cut.
  Given the identity on a bottom cell `[a,b]×[c,g]` and a top cell `[a,b]×[g,d]`,
  it holds on `[a,b]×[c,d]`.  The proof mirrors `greens_additive_vertical`,
  rewriting through the already-verified `rectLineIntegral_hsplit` and
  `rectDoubleIntegral_hsplit`; the shared horizontal edge `y = g` cancels by
  orientation with no extra input.

* `greens_grid_2x2` — **the 2D grid capstone.**  Cut `[a,b]×[c,d]` by the vertical
  line `x = e` *and* the horizontal line `y = g`, producing the four cells

        BL = [a,e]×[c,g]   BR = [e,b]×[c,g]
        TL = [a,e]×[g,d]   TR = [e,b]×[g,d].

  If Green's theorem holds on each of the four cells, it holds on the whole
  rectangle.  The proof first glues the two bottom cells and the two top cells into
  horizontal strips (`greens_additive_vertical`, twice), then glues the two strips
  along `y = g` (`greens_additive_horizontal`).  Both interior edges — the vertical
  `x = e` and the horizontal `y = g` — cancel automatically.

* `area_grid_2x2_unit_square` — a fully concrete sanity check: the area of `[0,1]²`
  is the sum of its four quarter-cells.

## What is new relative to the gallery

The parent and all its siblings glue along a **single** cut in **one** direction.
`greens_grid_2x2` is the first statement in the gallery where the region is tiled in
**two** directions simultaneously: it is the `2 × 2` prototype of "tile a rectangle
with a grid and add the cellwise Green identities," with *both* families of interior
edges cancelling by orientation.  This is exactly the base case from which Green's
theorem on an arbitrary `m × n` rectangular grid follows by iterating the two
single-cut steps.

## Proof Status

- [x] Horizontal gluing capstone (0 sorries)
- [x] 2×2 grid gluing capstone (0 sorries)
- [x] Concrete `[0,1]²` area grid check (0 sorries)
- No `axiom`, no `sorry`, no `native_decide`.
-/

namespace GreensTheoremOQ01OQ03OQ02

open MeasureTheory intervalIntegral
open GreensTheoremOQ01
open GreensTheoremOQ01OQ03

/-!
## Part I: Horizontal gluing capstone

The mirror of `greens_additive_vertical`.  The interior edge is the horizontal
segment `y = g`, shared with opposite orientation by the bottom cell `[a,b]×[c,g]`
and the top cell `[a,b]×[g,d]`.  Both sides of Green's identity are additive across
this cut (`rectLineIntegral_hsplit`, `rectDoubleIntegral_hsplit`), so once the
identity holds on each cell the union follows by a pure rewrite.
-/

/-- **Green's theorem is preserved by horizontal subdivision (gluing).**

    Given that the concrete Green identity holds on the bottom cell `[a,b]×[c,g]`
    and the top cell `[a,b]×[g,d]` for the curl field `F`, it holds on the whole
    rectangle `[a,b]×[c,d]`.  The four line-integral and two double-integral
    integrability hypotheses are exactly those that make the two sides additive
    across `y = g`. -/
theorem greens_additive_horizontal (P Q F : ℝ × ℝ → ℝ) (a b c g d : ℝ)
    -- gluing data for the line integral (vertical edges `x = b`, `x = a`)
    (hQb_cg : IntervalIntegrable (fun y => Q (b, y)) volume c g)
    (hQb_gd : IntervalIntegrable (fun y => Q (b, y)) volume g d)
    (hQa_cg : IntervalIntegrable (fun y => Q (a, y)) volume c g)
    (hQa_gd : IntervalIntegrable (fun y => Q (a, y)) volume g d)
    -- gluing data for the double integral (outer `y`-integral)
    (hFo_cg : IntervalIntegrable (fun y => ∫ x in a..b, F (x, y)) volume c g)
    (hFo_gd : IntervalIntegrable (fun y => ∫ x in a..b, F (x, y)) volume g d)
    -- Green's theorem on each cell
    (hB : rectLineIntegral P Q a b c g = rectDoubleIntegral F a b c g)
    (hT : rectLineIntegral P Q a b g d = rectDoubleIntegral F a b g d) :
    rectLineIntegral P Q a b c d = rectDoubleIntegral F a b c d := by
  rw [← rectLineIntegral_hsplit P Q a b c g d hQb_cg hQb_gd hQa_cg hQa_gd,
      ← rectDoubleIntegral_hsplit F a b c g d hFo_cg hFo_gd, hB, hT]

/-!
## Part II: The 2×2 grid capstone

Cut `[a,b]×[c,d]` by `x = e` and `y = g`.  We glue the two bottom cells and the two
top cells into horizontal strips with `greens_additive_vertical`, then glue the two
strips with `greens_additive_horizontal`.  The vertical interior edge `x = e` is
handled in the two strip glues, the horizontal interior edge `y = g` in the final
glue; neither requires any cancellation input beyond the integrability data.
-/

/-- **Green's theorem glues across a 2×2 grid.**

    With `[a,b]×[c,d]` cut at `x = e` and `y = g` into the four cells

        BL = [a,e]×[c,g]   BR = [e,b]×[c,g]
        TL = [a,e]×[g,d]   TR = [e,b]×[g,d],

    if Green's identity holds on each of the four cells (`hBL, hBR, hTL, hTR`) then
    it holds on the whole rectangle.  The integrability hypotheses are exactly those
    consumed by the two vertical strip glues and the final horizontal glue. -/
theorem greens_grid_2x2 (P Q F : ℝ × ℝ → ℝ) (a e b c g d : ℝ)
    -- horizontal-edge line integrability (P integrated in x over the two columns)
    (hPc_ae : IntervalIntegrable (fun x => P (x, c)) volume a e)
    (hPc_eb : IntervalIntegrable (fun x => P (x, c)) volume e b)
    (hPg_ae : IntervalIntegrable (fun x => P (x, g)) volume a e)
    (hPg_eb : IntervalIntegrable (fun x => P (x, g)) volume e b)
    (hPd_ae : IntervalIntegrable (fun x => P (x, d)) volume a e)
    (hPd_eb : IntervalIntegrable (fun x => P (x, d)) volume e b)
    -- vertical-edge line integrability (Q integrated in y over the two rows)
    (hQb_cg : IntervalIntegrable (fun y => Q (b, y)) volume c g)
    (hQb_gd : IntervalIntegrable (fun y => Q (b, y)) volume g d)
    (hQa_cg : IntervalIntegrable (fun y => Q (a, y)) volume c g)
    (hQa_gd : IntervalIntegrable (fun y => Q (a, y)) volume g d)
    -- inner double-integral integrability of F (in x) over each cell's `y`-range
    (hF_ae_cg : ∀ y ∈ Set.uIcc c g, IntervalIntegrable (fun x => F (x, y)) volume a e)
    (hF_eb_cg : ∀ y ∈ Set.uIcc c g, IntervalIntegrable (fun x => F (x, y)) volume e b)
    (hF_ae_gd : ∀ y ∈ Set.uIcc g d, IntervalIntegrable (fun x => F (x, y)) volume a e)
    (hF_eb_gd : ∀ y ∈ Set.uIcc g d, IntervalIntegrable (fun x => F (x, y)) volume e b)
    -- outer double-integral integrability for the two vertical strip glues
    (hFo_ae_cg : IntervalIntegrable (fun y => ∫ x in a..e, F (x, y)) volume c g)
    (hFo_eb_cg : IntervalIntegrable (fun y => ∫ x in e..b, F (x, y)) volume c g)
    (hFo_ae_gd : IntervalIntegrable (fun y => ∫ x in a..e, F (x, y)) volume g d)
    (hFo_eb_gd : IntervalIntegrable (fun y => ∫ x in e..b, F (x, y)) volume g d)
    -- outer double-integral integrability for the final horizontal glue
    (hFo_ab_cg : IntervalIntegrable (fun y => ∫ x in a..b, F (x, y)) volume c g)
    (hFo_ab_gd : IntervalIntegrable (fun y => ∫ x in a..b, F (x, y)) volume g d)
    -- Green's theorem on each of the four cells
    (hBL : rectLineIntegral P Q a e c g = rectDoubleIntegral F a e c g)
    (hBR : rectLineIntegral P Q e b c g = rectDoubleIntegral F e b c g)
    (hTL : rectLineIntegral P Q a e g d = rectDoubleIntegral F a e g d)
    (hTR : rectLineIntegral P Q e b g d = rectDoubleIntegral F e b g d) :
    rectLineIntegral P Q a b c d = rectDoubleIntegral F a b c d := by
  -- bottom strip `[a,b]×[c,g]`: glue BL + BR across the vertical edge `x = e`
  have hBottom : rectLineIntegral P Q a b c g = rectDoubleIntegral F a b c g :=
    greens_additive_vertical P Q F a e b c g
      hPc_ae hPc_eb hPg_ae hPg_eb
      hF_ae_cg hF_eb_cg hFo_ae_cg hFo_eb_cg
      hBL hBR
  -- top strip `[a,b]×[g,d]`: glue TL + TR across the vertical edge `x = e`
  have hTop : rectLineIntegral P Q a b g d = rectDoubleIntegral F a b g d :=
    greens_additive_vertical P Q F a e b g d
      hPg_ae hPg_eb hPd_ae hPd_eb
      hF_ae_gd hF_eb_gd hFo_ae_gd hFo_eb_gd
      hTL hTR
  -- whole rectangle: glue the two strips across the horizontal edge `y = g`
  exact greens_additive_horizontal P Q F a b c g d
    hQb_cg hQb_gd hQa_cg hQa_gd hFo_ab_cg hFo_ab_gd hBottom hTop

/-!
## Part III: Concrete sanity check

The area of the unit square `[0,1]²` equals the sum of its four quarter-cells of
area `1/4` each, computed through `rectDoubleIntegral` of the constant `1`.
-/

/-- The double integral of `1` over `[0,1]²` equals the sum over the four quarter
    cells `[0,½]×[0,½]`, `[½,1]×[0,½]`, `[0,½]×[½,1]`, `[½,1]×[½,1]`. -/
theorem area_grid_2x2_unit_square :
    rectDoubleIntegral (fun _ => 1) 0 (1/2) 0 (1/2) +
    rectDoubleIntegral (fun _ => 1) (1/2) 1 0 (1/2) +
    rectDoubleIntegral (fun _ => 1) 0 (1/2) (1/2) 1 +
    rectDoubleIntegral (fun _ => 1) (1/2) 1 (1/2) 1 =
    rectDoubleIntegral (fun _ => 1) 0 1 0 1 := by
  rw [area_double_integral, area_double_integral, area_double_integral,
      area_double_integral, area_double_integral]
  ring

#check @greens_additive_horizontal
#check @greens_grid_2x2

end GreensTheoremOQ01OQ03OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms GreensTheoremOQ01OQ03OQ02.greens_additive_horizontal
#print axioms GreensTheoremOQ01OQ03OQ02.greens_grid_2x2
