/-
# Curved-Crease Origami — Constructive Core of Huzita–Hatori Axiom HH-5

This entry **completes** a piece of the open problem
`angle-trisection-oq-05-oq-04` (Curved-Crease Origami: strengthening the
Huzita–Hatori axioms). The parent file
`Proofs/AngleTrisectionOQ05OQ04.lean` builds the seven Huzita–Hatori (HH)
fold operations up constructively, one axiom at a time, and had reached
the frontier:

> "… six of seven HH ingredients are now constructive … only **HH-5**
> (Beloch-light) and **HH-6** (Beloch fold) remain, plus the intersecting
> case of HH-3."

This file discharges the **rational (square-root-free) core of HH-5**.

## HH-5

> Given two distinct points `P₁`, `P₂` and a line `ℓ`, there is a fold
> through `P₂` that places `P₁` onto `ℓ`.

Geometrically the fold is a reflection fixing `P₂`, so the landing point
`P₁'` of `P₁` must satisfy `|P₁' − P₂| = |P₁ − P₂|`: it lies on the
circle centred at `P₂` through `P₁`. HH-5 is therefore solvable **iff**
that circle meets `ℓ`, and *finding* the landing point is a circle-line
intersection — genuinely a `Real.sqrt` step. The present file isolates
that irrational existence step (kept as a hypothesis, a **witness**
landing point `P₁'`) from the fold construction itself, which is purely
rational:

* **`reflectAcross_distSq_fixed`** — reflecting across *any* fold through
  `P₂` preserves the squared distance to `P₂` (reflection is an isometry
  about a fixed point). This shows the equidistance condition on the
  landing point is not merely sufficient but **necessary**.
* **`perpBisector_contains_of_equidistSq`** — `P₂` lies on the
  perpendicular bisector of `P₁` and any equidistant point `P₁'`.
* **`hh5_core` / `hh5_core_exact`** — given a witness landing point
  `P₁' ∈ ℓ` equidistant from `P₂`, the perpendicular bisector of
  `P₁P₁'` is a fold through `P₂` sending `P₁` onto `ℓ` (and onto `P₁'`
  precisely).

Together these give a full **characterisation**: HH-5 is solvable for
`(P₁, P₂, ℓ)` exactly when `ℓ` contains a point at squared-distance
`|P₁ − P₂|²` from `P₂`, and the fold is then explicit and rational in
that point. The only irrational content of HH-5 is the existence of the
witness (circle-line intersection); the fold operation carries no further
degree.

Self-contained: the planar primitives (`Point`, `Line`, `reflectAcross`,
`perpBisector`) are copied verbatim from the parent so this file compiles
against `Mathlib` alone. 0 `sorry`, 0 `axiom`.

## References
- Huzita, H. (1989). Axiomatic Development of Flat Origami.
- Alperin, R.C. & Lang, R.J. (2006). One-, Two-, and Multi-fold Origami
  Axioms. 4OSME, 371-393.
- Demaine, E., Demaine, M., Hart, V., Price, G., Tachi, T. (2011).
  (Non)existence of Pleated Folds.
-/
import Mathlib

namespace AngleTrisectionOQ05OQ04Incomplete01

open Real

/-! ## Planar primitives (copied verbatim from the parent file) -/

/-- A point in the Euclidean plane. -/
abbrev Point := ℝ × ℝ

/-- A line `a x + b y + c = 0` with `(a, b) ≠ (0, 0)`. -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nondeg : a ≠ 0 ∨ b ≠ 0

/-- A point lies on a line. -/
def Line.contains (l : Line) (p : Point) : Prop :=
  l.a * p.1 + l.b * p.2 + l.c = 0

/-- Reflection of a point across a line, `P' = P − 2·((aPx+bPy+c)/(a²+b²))·(a,b)`. -/
noncomputable def reflectAcross (l : Line) (p : Point) : Point :=
  let t := 2 * (l.a * p.1 + l.b * p.2 + l.c) / (l.a^2 + l.b^2)
  (p.1 - t * l.a, p.2 - t * l.b)

/-- The squared norm of a line's normal vector is positive. -/
theorem Line.normSq_pos (l : Line) : 0 < l.a^2 + l.b^2 := by
  rcases l.nondeg with ha | hb
  · have : 0 < l.a^2 := by positivity
    nlinarith [sq_nonneg l.b]
  · have : 0 < l.b^2 := by positivity
    nlinarith [sq_nonneg l.a]

/-- The perpendicular bisector of two distinct points `p₁ ≠ p₂`. -/
noncomputable def perpBisector (p₁ p₂ : Point) (h : p₁ ≠ p₂) : Line where
  a := p₂.1 - p₁.1
  b := p₂.2 - p₁.2
  c := -((p₂.1^2 - p₁.1^2) + (p₂.2^2 - p₁.2^2)) / 2
  nondeg := by
    by_contra hcontra
    push_neg at hcontra
    obtain ⟨ha, hb⟩ := hcontra
    apply h
    have hx : p₁.1 = p₂.1 := by linarith [sub_eq_zero.mp ha]
    have hy : p₁.2 = p₂.2 := by linarith [sub_eq_zero.mp hb]
    exact Prod.ext hx hy

/-- The squared chord length is positive when `p₁ ≠ p₂`. -/
theorem perpBisector_dirSq_pos (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    0 < (p₂.1 - p₁.1)^2 + (p₂.2 - p₁.2)^2 := by
  rcases eq_or_ne p₁.1 p₂.1 with hx | hx
  · have hy : p₁.2 ≠ p₂.2 := fun heq => h (Prod.ext hx heq)
    have h2 : 0 < (p₂.2 - p₁.2)^2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hy))
    nlinarith [sq_nonneg (p₂.1 - p₁.1)]
  · have h1 : 0 < (p₂.1 - p₁.1)^2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hx))
    nlinarith [sq_nonneg (p₂.2 - p₁.2)]

/-- Reflecting `p₁` across the perpendicular bisector of `p₁`, `p₂` yields `p₂`. -/
theorem reflectAcross_perpBisector (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    reflectAcross (perpBisector p₁ p₂ h) p₁ = p₂ := by
  have hD : (p₂.1 - p₁.1)^2 + (p₂.2 - p₁.2)^2 ≠ 0 :=
    ne_of_gt (perpBisector_dirSq_pos p₁ p₂ h)
  refine Prod.ext ?_ ?_
  · simp only [reflectAcross, perpBisector]
    field_simp
    ring
  · simp only [reflectAcross, perpBisector]
    field_simp
    ring

/-! ## New content — HH-5 constructive core (S8) -/

/-- Squared Euclidean distance in the plane. (Note: this is *not* the
default `dist` on `ℝ × ℝ`, which is the sup metric; we work with the
polynomial squared-Euclidean form throughout.) -/
def distSq (p q : Point) : ℝ := (p.1 - q.1)^2 + (p.2 - q.2)^2

/-- **Reflection about a fixed point is an isometry (fixed-point core).**
If a fold line `l` passes through `p₂`, then reflecting any point `p₁`
across `l` preserves its squared distance to `p₂`. Consequently the
landing point of `p₁` under an HH-5 fold through `p₂` is *forced* to lie
at squared-distance `distSq p₁ p₂` from `p₂` — the equidistance condition
below is necessary, not just sufficient. -/
theorem reflectAcross_distSq_fixed (l : Line) (p₁ p₂ : Point)
    (hp₂ : l.contains p₂) :
    distSq (reflectAcross l p₁) p₂ = distSq p₁ p₂ := by
  have hD : l.a^2 + l.b^2 ≠ 0 := ne_of_gt l.normSq_pos
  simp only [distSq, reflectAcross, Line.contains] at hp₂ ⊢
  field_simp
  linear_combination
    (4 * (l.a * p₁.1 + l.b * p₁.2 + l.c) * (l.a^2 + l.b^2)) * hp₂

/-- **Equidistance ⇒ on the perpendicular bisector.** If `q` is
equidistant (in squared Euclidean distance) from `p₁` and `p₂`, then `q`
lies on their perpendicular bisector. -/
theorem perpBisector_contains_of_equidistSq
    (p₁ p₂ q : Point) (h : p₁ ≠ p₂)
    (hequi : distSq q p₁ = distSq q p₂) :
    (perpBisector p₁ p₂ h).contains q := by
  simp only [distSq] at hequi
  simp only [Line.contains, perpBisector]
  linear_combination hequi / 2

/-- **HH-5 constructive core (witnessed form).** Suppose `P₁'` is a point
of the target line `ℓ` that is equidistant from `P₂` as `P₁` is (i.e. a
valid landing point — the circle centred at `P₂` through `P₁` meets `ℓ`
at `P₁'`). Then there is a fold line through `P₂` whose reflection sends
`P₁` onto `ℓ`. The explicit witness is the perpendicular bisector of
`P₁` and `P₁'`, which is rational in the data. -/
theorem hh5_core (p₁ p₂ p₁' : Point) (ℓ : Line)
    (hne : p₁ ≠ p₁')
    (hmem : ℓ.contains p₁')
    (hequi : distSq p₂ p₁ = distSq p₂ p₁') :
    ∃ l : Line, l.contains p₂ ∧ ℓ.contains (reflectAcross l p₁) := by
  refine ⟨perpBisector p₁ p₁' hne, ?_, ?_⟩
  · exact perpBisector_contains_of_equidistSq p₁ p₁' p₂ hne hequi
  · rw [reflectAcross_perpBisector p₁ p₁' hne]; exact hmem

/-- **HH-5 constructive core (exact form).** The same fold not only lands
`P₁` on `ℓ` but sends it precisely to the witness point `P₁'`. -/
theorem hh5_core_exact (p₁ p₂ p₁' : Point) (ℓ : Line)
    (hne : p₁ ≠ p₁')
    (hmem : ℓ.contains p₁')
    (hequi : distSq p₂ p₁ = distSq p₂ p₁') :
    ∃ l : Line, l.contains p₂ ∧ reflectAcross l p₁ = p₁'
      ∧ ℓ.contains (reflectAcross l p₁) := by
  refine ⟨perpBisector p₁ p₁' hne,
    perpBisector_contains_of_equidistSq p₁ p₁' p₂ hne hequi,
    reflectAcross_perpBisector p₁ p₁' hne, ?_⟩
  rw [reflectAcross_perpBisector p₁ p₁' hne]; exact hmem

/-- **HH-5 solvability characterisation.** For distinct `P₁`, `P₂` and a
target line `ℓ`, an HH-5 fold (through `P₂`, sending `P₁` onto `ℓ`) whose
landing point is distinct from `P₁` **exists iff** `ℓ` contains a point at
squared-distance `distSq P₁ P₂` from `P₂`. This pins down exactly the
irrational content of HH-5: the existence of the witness landing point (a
circle-line intersection), everything else being rational. -/
theorem hh5_solvable_iff (p₁ p₂ : Point) (ℓ : Line) :
    (∃ p₁' : Point, p₁ ≠ p₁' ∧ ℓ.contains p₁' ∧ distSq p₂ p₁ = distSq p₂ p₁')
      ↔ (∃ l : Line, l.contains p₂ ∧ (∃ p₁' : Point, p₁ ≠ p₁' ∧
          reflectAcross l p₁ = p₁' ∧ ℓ.contains p₁')) := by
  constructor
  · rintro ⟨p₁', hne, hmem, hequi⟩
    obtain ⟨l, hp₂, hrefl, _⟩ := hh5_core_exact p₁ p₂ p₁' ℓ hne hmem hequi
    exact ⟨l, hp₂, p₁', hne, hrefl, hmem⟩
  · rintro ⟨l, hp₂, p₁', hne, hrefl, hmem⟩
    refine ⟨p₁', hne, hmem, ?_⟩
    have := reflectAcross_distSq_fixed l p₁ p₂ hp₂
    rw [hrefl] at this
    -- `distSq p₁' p₂ = distSq p₁ p₂`; convert to `distSq p₂ _` form.
    simp only [distSq] at this ⊢
    linear_combination -this

end AngleTrisectionOQ05OQ04Incomplete01
