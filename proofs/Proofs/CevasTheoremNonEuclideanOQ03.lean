/-
# Ceva Non-Euclidean OQ-03 — the hexagon ratio algebra behind Pappus–Brianchon

*Open question (cevas-theorem-non-euclidean-oq-03).* Use the abstract
`GeneralizedCevianConfig` to approach the non-Euclidean Pappus–Brianchon
theorems.

## Background

The parent `CevasTheoremNonEuclidean.lean` packages a Ceva/Menelaus
configuration as six positive "measures" `bd, dc, ce, ea, af, fb`
(`GeneralizedCevianConfig`) and studies the ratio product

  `P(cfg) = (bd/dc)·(ce/ea)·(af/fb)`  (`generalizedCevaProduct`),

with `P(cfg) = 1` the geometry-independent concurrence/collinearity condition.
Specializing the measures to `id`, `sin`, `sinh` recovers the Euclidean,
spherical, and hyperbolic theorems.

Pappus's and Brianchon's theorems are *hexagon* incidence theorems. The six
measures of a `GeneralizedCevianConfig` are exactly the six sides of the Pappus
hexagon (vertices alternating on two geodesics, a degenerate conic). The
algebraic invariant of such a hexagon is the relation between the two
**alternating products** of its side-ratios — and that relation is the same in
every constant-curvature geometry. This file isolates that invariant.

## What is proved (0 axioms, 0 sorries)

* `dualCevaProduct cfg = (dc/ce)·(ea/af)·(fb/bd)` — the *cyclically shifted*
  alternating product (the "other" three sides of the hexagon).
* **`ceva_dual_reciprocal`**: `P(cfg) · dualCevaProduct cfg = 1`. The two
  alternating products of a hexagon are reciprocal — a pure telescoping
  cancellation of all six measures. This is the hexagon closure relation.
* **`ceva_iff_dual`**: `P(cfg) = 1 ↔ dualCevaProduct cfg = 1`. The Ceva
  condition and its Brianchon-style dual hold together — the duality at the
  level of the abstract configuration.
* **`cevaProduct_comp` / `dualProduct_comp`**: both products are multiplicative
  under componentwise composition of configurations (`comp`). This is the
  chaining law by which the classical Pappus proof multiplies several
  transversal relations.
* Non-Euclidean instances `spherical_ceva_dual_reciprocal`,
  `hyperbolic_ceva_dual_reciprocal`: the reciprocity holds verbatim with `sin`
  and `sinh` measures, i.e. on the sphere and in the hyperbolic plane.

## Scope (honest)

This formalizes the *algebraic hexagon invariant* on which the non-Euclidean
Pappus–Brianchon incidence theorems rest — the geometry-independent closure
relation among side-ratios, captured entirely inside `GeneralizedCevianConfig`.
It does **not** derive the full projective incidence statement (which needs the
combinatorics of lines and intersection points); that is future work that can
build on the composition law proved here. Everything below is checked by the
kernel with no axioms.
-/

import Proofs.CevasTheoremNonEuclidean
import Mathlib.Tactic

namespace CevaNonEuclideanOQ03

/-!
## The dual (cyclically shifted) ratio product
-/

/-- The cyclically shifted alternating product `(dc/ce)·(ea/af)·(fb/bd)` — the
"other three sides" of the Pappus hexagon relative to `generalizedCevaProduct`. -/
noncomputable def dualCevaProduct (cfg : GeneralizedCevianConfig) : ℝ :=
  (cfg.dc / cfg.ce) * (cfg.ea / cfg.af) * (cfg.fb / cfg.bd)

/-- **Hexagon closure relation.** The Ceva product and its cyclic dual are
reciprocal: every one of the six measures cancels. -/
theorem ceva_dual_reciprocal (cfg : GeneralizedCevianConfig) :
    generalizedCevaProduct cfg * dualCevaProduct cfg = 1 := by
  unfold generalizedCevaProduct dualCevaProduct
  have h1 := ne_of_gt cfg.bd_pos
  have h2 := ne_of_gt cfg.dc_pos
  have h3 := ne_of_gt cfg.ce_pos
  have h4 := ne_of_gt cfg.ea_pos
  have h5 := ne_of_gt cfg.af_pos
  have h6 := ne_of_gt cfg.fb_pos
  field_simp

/-- **Ceva–Brianchon duality (abstract).** The Ceva concurrence condition and
its hexagon dual hold together. -/
theorem ceva_iff_dual (cfg : GeneralizedCevianConfig) :
    generalizedCevaProduct cfg = 1 ↔ dualCevaProduct cfg = 1 := by
  have hrec := ceva_dual_reciprocal cfg
  constructor
  · intro h; rw [h, one_mul] at hrec; exact hrec
  · intro h; rw [h, mul_one] at hrec; exact hrec

/-- The dual product is positive. -/
theorem dualCevaProduct_pos (cfg : GeneralizedCevianConfig) :
    0 < dualCevaProduct cfg := by
  unfold dualCevaProduct
  have := cfg.bd_pos; have := cfg.ce_pos; have := cfg.af_pos
  have := cfg.dc_pos; have := cfg.ea_pos; have := cfg.fb_pos
  positivity

/-!
## Composition: the chaining law
-/

/-- Componentwise composition of two configurations (multiply matching
measures). The classical Pappus proof multiplies several such relations. -/
noncomputable def comp (c1 c2 : GeneralizedCevianConfig) : GeneralizedCevianConfig where
  bd := c1.bd * c2.bd
  dc := c1.dc * c2.dc
  ce := c1.ce * c2.ce
  ea := c1.ea * c2.ea
  af := c1.af * c2.af
  fb := c1.fb * c2.fb
  bd_pos := mul_pos c1.bd_pos c2.bd_pos
  dc_pos := mul_pos c1.dc_pos c2.dc_pos
  ce_pos := mul_pos c1.ce_pos c2.ce_pos
  ea_pos := mul_pos c1.ea_pos c2.ea_pos
  af_pos := mul_pos c1.af_pos c2.af_pos
  fb_pos := mul_pos c1.fb_pos c2.fb_pos

/-- The Ceva product is multiplicative under composition. -/
theorem cevaProduct_comp (c1 c2 : GeneralizedCevianConfig) :
    generalizedCevaProduct (comp c1 c2)
      = generalizedCevaProduct c1 * generalizedCevaProduct c2 := by
  unfold generalizedCevaProduct comp
  have h1 := ne_of_gt c1.dc_pos
  have h2 := ne_of_gt c2.dc_pos
  have h3 := ne_of_gt c1.ea_pos
  have h4 := ne_of_gt c2.ea_pos
  have h5 := ne_of_gt c1.fb_pos
  have h6 := ne_of_gt c2.fb_pos
  field_simp

/-- The dual product is multiplicative under composition. -/
theorem dualProduct_comp (c1 c2 : GeneralizedCevianConfig) :
    dualCevaProduct (comp c1 c2)
      = dualCevaProduct c1 * dualCevaProduct c2 := by
  unfold dualCevaProduct comp
  have h1 := ne_of_gt c1.ce_pos
  have h2 := ne_of_gt c2.ce_pos
  have h3 := ne_of_gt c1.af_pos
  have h4 := ne_of_gt c2.af_pos
  have h5 := ne_of_gt c1.bd_pos
  have h6 := ne_of_gt c2.bd_pos
  field_simp

/-- **Closure under composition.** If two configurations each satisfy the Ceva
condition, so does their composite — the multiplicative step that assembles a
Pappus-type conclusion from several transversal relations. -/
theorem ceva_comp_of_ceva {c1 c2 : GeneralizedCevianConfig}
    (h1 : generalizedCevaProduct c1 = 1) (h2 : generalizedCevaProduct c2 = 1) :
    generalizedCevaProduct (comp c1 c2) = 1 := by
  rw [cevaProduct_comp, h1, h2, mul_one]

/-!
## Non-Euclidean instances

The reciprocity is a statement about the abstract configuration, so it holds in
every constant-curvature geometry by feeding the geodesic-arc measures through
`sin` (spherical) or `sinh` (hyperbolic).
-/

/-- **Spherical hexagon closure**: the reciprocity with `sin` measures. -/
theorem spherical_ceva_dual_reciprocal (cfg : SphericalCevianConfig) :
    generalizedCevaProduct cfg.toGeneralized
      * dualCevaProduct cfg.toGeneralized = 1 :=
  ceva_dual_reciprocal cfg.toGeneralized

/-- **Hyperbolic hexagon closure**: the reciprocity with `sinh` measures. -/
theorem hyperbolic_ceva_dual_reciprocal (cfg : HyperbolicCevianConfig) :
    generalizedCevaProduct cfg.toGeneralized
      * dualCevaProduct cfg.toGeneralized = 1 :=
  ceva_dual_reciprocal cfg.toGeneralized

end CevaNonEuclideanOQ03
