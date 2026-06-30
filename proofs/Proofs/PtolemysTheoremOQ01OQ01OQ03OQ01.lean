import Mathlib

/-!
# Inversion carries a circle through its centre to a line

## What this proves

Fix a point `a` in a real inner-product (Euclidean) space and invert about `a` with radius `1`.
The classical statement *"inversion centred at `a` maps every circle (sphere) through `a` to a
line (hyperplane) not through `a`, and conversely"* is made precise and **axiom-free** here.

The single computational heart is

  `inversion_inner_eq_half_iff`:
    for `x ≠ a` and any `o`,
      `dist x o = dist a o  ↔  ⟪inversion a 1 x -ᵥ a, o -ᵥ a⟫ = 1/2`.

The left-hand side says `x` lies on the sphere **through `a`** centred at `o`
(`dist a o` is the radius). The right-hand side says the inversion image `x' = inversion a 1 x`
lies on the fixed **affine hyperplane**

  `H_o = { p | ⟪p -ᵥ a, o -ᵥ a⟫ = 1/2 }`,

whose normal is `o -ᵥ a` and which does **not** contain `a` (there the inner product is `0`).
In a plane `H_o` is exactly a line, so this is "circle-through-centre ↦ line".

From this one equivalence we read off both halves of the bijection:

* `cospherical_imp_inversion_image_inner_eq_half` — every cospherical set containing `a` has all
  its other points sent into one common hyperplane `H_o` (circle → line);
* `inner_eq_half_imp_inversion_image_cospherical` — conversely, the inversion images of any set of
  points lying on a hyperplane `H = {⟪· -ᵥ a, n⟫ = 1/2}` (with `n ≠ 0`) are cospherical with `a`
  (line → circle), the centre being `n +ᵥ a`.

The four-point specialisation `cospherical_four_imp_inversion_images_collinear_witness` records the
shape relevant to Ptolemy: if `a, b, c, d` are concyclic then the three images
`b', c', d'` share a common hyperplane normal — the line their circle becomes.

## Relation to the parent entry

The parent `ptolemys-theorem-oq-01-oq-01-oq-03` (`PtolemysTheoremOQ01OQ01OQ03.lean`) proves the
*ordered* facet, `ptolemy_eq_iff_wbtw_inversion`, characterising **equality** in Ptolemy's
inequality by `Wbtw` of the three inversion images and, as a corollary, their `Collinear`-ity.
That `Collinear` conclusion is the *image-side* "line". This file supplies the complementary
*source-side* statement, tying that line back to genuine **concyclicity** (`Cospherical`) of the
four original points — and it does so without the trigonometric ordering axiom
(`positive_ratio_implies_cyclic_order`) that the unit-circle leaf `ptolemys-theorem-oq-01-oq-01`
relied on. Both files are 0-axiom / 0-sorry.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open EuclideanGeometry

namespace Ptolemy.InversionCircleLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## A scalar helper -/

/-- For nonnegative reals, equality is equivalent to equality of squares. -/
private theorem nonneg_sq_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    p = q ↔ p ^ 2 = q ^ 2 := by
  constructor
  · intro h; rw [h]
  · intro h; rw [← Real.sqrt_sq hp, ← Real.sqrt_sq hq, h]

/-! ## The core equivalence: sphere-through-centre ⇔ image-on-hyperplane -/

/-- **Inversion sends the sphere through the centre to a hyperplane.** For `x ≠ a` and any point
`o`, the point `x` lies on the sphere through `a` centred at `o` (i.e. `dist x o = dist a o`, the
radius being `dist a o`) **iff** its inversion image lies on the fixed affine hyperplane with
normal `o -ᵥ a` at affine level `1/2`:

`dist x o = dist a o ↔ ⟪inversion a 1 x -ᵥ a, o -ᵥ a⟫ = 1/2`.

In a plane the hyperplane is a line — this is the analytic form of "a circle through the centre of
inversion maps to a line." -/
theorem inversion_inner_eq_half_iff (a o x : P) (hx : x ≠ a) :
    dist x o = dist a o ↔ inner ℝ (inversion a 1 x -ᵥ a) (o -ᵥ a) = (1 / 2 : ℝ) := by
  set y : V := x -ᵥ a with hyy
  set m : V := o -ᵥ a with hmm
  have hy0 : y ≠ 0 := vsub_ne_zero.mpr hx
  have hnpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hnsq : 0 < ‖y‖ ^ 2 := pow_pos hnpos 2
  -- the image inner product, expressed through `y` and `m`
  have himg : inner ℝ (inversion a 1 x -ᵥ a) m
      = (1 / ‖y‖) ^ 2 * inner ℝ y m := by
    rw [inversion_vsub_center, real_inner_smul_left, dist_eq_norm_vsub V x a, ← hyy]
  -- the distance condition, reduced to a single scalar equation
  have hcentral : (dist x o = dist a o) ↔ ‖y‖ ^ 2 = 2 * inner ℝ y m := by
    rw [nonneg_sq_iff dist_nonneg dist_nonneg,
        dist_eq_norm_vsub V x o, dist_eq_norm_vsub V a o]
    have e1 : x -ᵥ o = y - m := by rw [hyy, hmm]; exact (vsub_sub_vsub_cancel_right x o a).symm
    have e2 : a -ᵥ o = -m := by rw [hmm]; exact (neg_vsub_eq_vsub_rev o a).symm
    rw [e1, e2, norm_neg, norm_sub_sq_real]
    constructor <;> intro h <;> linarith
  rw [hcentral, himg, div_pow, one_pow, div_mul_eq_mul_div, one_mul,
      div_eq_div_iff hnsq.ne' (two_ne_zero)]
  constructor <;> intro h <;> linarith

/-! ## Circle → line: a cospherical set maps into one hyperplane -/

/-- **A circle through `a` maps to a line.** If `ps` is cospherical and contains `a`, then there is
a single normal vector `n = o -ᵥ a` such that the inversion image of every other point of `ps`
satisfies `⟪· -ᵥ a, n⟫ = 1/2`; i.e. all images lie on one affine hyperplane (a line in the plane). -/
theorem cospherical_imp_inversion_image_inner_eq_half
    {ps : Set P} (a : P) (ha : a ∈ ps) (hcs : Cospherical ps) :
    ∃ n : V, ∀ p ∈ ps, p ≠ a → inner ℝ (inversion a 1 p -ᵥ a) n = (1 / 2 : ℝ) := by
  obtain ⟨o, r, hor⟩ := hcs
  refine ⟨o -ᵥ a, fun p hp hpa => ?_⟩
  have hp_o : dist p o = dist a o := by rw [hor p hp, hor a ha]
  exact (inversion_inner_eq_half_iff a o p hpa).mp hp_o

/-! ## Line → circle: a hyperplane maps to a circle through `a` -/

/-- **A line maps to a circle through `a`.** If every point of `qs` differs from `a` and lies on
the hyperplane `{ p | ⟪p -ᵥ a, n⟫ = 1/2 }` (a genuine hyperplane when `n ≠ 0`), then the inversion
images of `qs`, together with `a`, are cospherical — the circle through `a` with centre `n +ᵥ a`. -/
theorem inner_eq_half_imp_inversion_image_cospherical
    {qs : Set P} (a : P) (n : V)
    (hq : ∀ q ∈ qs, q ≠ a ∧ inner ℝ (q -ᵥ a) n = (1 / 2 : ℝ)) :
    Cospherical (insert a (inversion a 1 '' qs)) := by
  refine ⟨n +ᵥ a, dist a (n +ᵥ a), ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_image] at hp
  rcases hp with rfl | ⟨q, hqs, rfl⟩
  · rfl
  · obtain ⟨hqa, hqn⟩ := hq q hqs
    have hxa : inversion a 1 q ≠ a := by
      rw [Ne, inversion_eq_center (one_ne_zero)]; exact hqa
    refine (inversion_inner_eq_half_iff a (n +ᵥ a) (inversion a 1 q) hxa).mpr ?_
    rw [inversion_inversion a (one_ne_zero) q, vadd_vsub]
    exact hqn

/-! ## Four-point form (the Ptolemy shape) -/

/-- **Concyclic ⇒ inversion images share a line.** If `a, b, c, d` are cospherical (e.g. concyclic),
the three inversion images `b', c', d'` of `b, c, d` about `a` share one hyperplane normal `n`,
each satisfying `⟪· -ᵥ a, n⟫ = 1/2`. This is the unordered "the circle through `a, b, c, d` becomes
the line through `b', c', d'`" — the source-side companion to the parent's `Collinear` corollary. -/
theorem cospherical_four_imp_inversion_images_collinear_witness
    (a b c d : P) (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a)
    (hcs : Cospherical ({a, b, c, d} : Set P)) :
    ∃ n : V, inner ℝ (inversion a 1 b -ᵥ a) n = (1 / 2 : ℝ)
           ∧ inner ℝ (inversion a 1 c -ᵥ a) n = (1 / 2 : ℝ)
           ∧ inner ℝ (inversion a 1 d -ᵥ a) n = (1 / 2 : ℝ) := by
  obtain ⟨n, hn⟩ :=
    cospherical_imp_inversion_image_inner_eq_half a (Set.mem_insert a _) hcs
  exact ⟨n, hn b (by simp) hb, hn c (by simp) hc, hn d (by simp) hd⟩

/-! ## Sanity check -/

/-- Consistency: a point already on the hyperplane (here the image of a sphere point) lands at the
prescribed level `1/2`, matching the core equivalence. -/
example (a o x : P) (hx : x ≠ a) (h : dist x o = dist a o) :
    inner ℝ (inversion a 1 x -ᵥ a) (o -ᵥ a) = (1 / 2 : ℝ) :=
  (inversion_inner_eq_half_iff a o x hx).mp h

end Ptolemy.InversionCircleLine
