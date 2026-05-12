import Proofs.AngleTrisectionOQ05
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

/-
# Curved-Crease Origami: Strengthening Huzita-Hatori (OQ-05-OQ-04)

## Open Question

The seven straight-crease Huzita-Hatori axioms (`AngleTrisectionOQ05.HHAxioms`,
line 108) characterise origami constructibility for FLAT (straight-line)
creases. This file initiates the S2 ORIENT scaffold for the open
question:

  Can `HHAxioms` be strengthened by a finite extension to capture
  curved-crease origami constructibility?

The mathematical heart of curved-crease theory is the Fuchs-Tabachnikov
compatibility identity (Fuchs-Tabachnikov 1999, Thm 1):

  κ_n(s) = κ_g(s) · cot(θ(s) / 2)

We encode this as a structure field rather than deriving it from
Darboux-frame differential geometry. Deriving it internally would
require ~350 lines of curve-on-surface API currently absent from
Mathlib at the pinned revision (`v4.26.0`). Encoding it as a structure
field makes the rest of the formalisation tractable while keeping the
mathematical content faithful: any concrete `CurvedCrease` witness
still has to supply a proof that FT holds for its `(γ, θ, κg, κn)`.

## This File (S2 ORIENT)

- `CurvedCrease` — a structure carrying `(L, γ, θ, κg, κn)` plus FT.
- `CurvedCrease.IsStraight` — `κ_g ≡ 0` on the parameter interval.
- `normal_curvature_zero_of_straight` — internal lemma (proved):
  straight-fold limit ⇒ `κ_n ≡ 0`.
- `CurvedCrease.ExistsHHFold` — predicate for "curve endpoints lie on
  a straight Huzita-Hatori fold line".
- `straight_fold_recovers_HH` (S3 target) — conservativity statement.
- `CurveAlgebraic` — predicate that the crease curve is algebraic.
- `curved_fold_algebraic_implies_origami` (S4 target) — partial
  sharpness.
- `IsCurvedFoldConstructible` — `α` is a coordinate of some
  curved-crease point.
- `K_curved_eq_K_origami` (S5 / OPEN) — Demaine-Demaine-Hart-Price-
  Tachi 2011 conjecture stated as a Lean theorem.

## Honest Calibration

This S2 file does **not** resolve the mathematical question. It
provides:
1. A formal language (`CurvedCrease`) in which the question is stated.
2. The conservativity statement that any candidate strengthening must
   satisfy (`straight_fold_recovers_HH`).
3. Statement-only theorems for the S3 / S4 / S5 targets.

The intended meta status is `axiomatized` because `ftCompatible` is a
structure-encoded assumption: it counts as +1 toward the meta
`axiomCount`, even though zero `axiom` declarations appear in this
file. 3 intentional `sorry` markers (S3 / S4 / S5 targets).

## References

* Huffman, D. A. (1976). *Curvature and creases: A primer on paper.*
  IEEE Trans. Comput. C-25(10), 1010-1019.
* Fuchs, D.; Tabachnikov, S. (1999). *More on paperfolding.* Amer.
  Math. Monthly 106(1), 27-35. (Theorem 1 is the FT identity.)
* Demaine, E. D.; Demaine, M. L.; Hart, V.; Price, G. N.; Tachi, T.
  (2011). *(Non)existence of pleated folds: How paper folds between
  creases.* Graphs Combin. 27(3), 377-397.
* Alperin, R. C.; Lang, R. J. (2006). *One-, two-, and multi-fold
  origami axioms.* 4OSME, 371-393.
-/

namespace AngleTrisectionOQ05OQ04

open AngleTrisectionOQ05

-- ============================================================
-- PART 1: The Curved-Crease Structure
-- ============================================================

/--
A **curved crease** is the data of
* a parameter length `L > 0`;
* a planar curve `γ : ℝ → ℝ × ℝ` (the crease in the unfolded paper);
* a dihedral fold-angle profile `θ : ℝ → ℝ` taking values in
  `(0, π)` on `[0, L]`;
* a signed geodesic curvature `κ_g : ℝ → ℝ` (intrinsic to the paper,
  equal to the signed planar curvature of `γ` since the paper is flat);
* a normal curvature `κ_n : ℝ → ℝ` of `γ` as a curve on the folded
  surface;
subject to the Fuchs-Tabachnikov compatibility identity.

Two of these fields encode genuine assumptions:
* `hθ_pos` states that the dihedral fold angle is a strict dihedral
  angle (no degeneration to a fully flat or fully closed fold);
* `ftCompatible` is the Fuchs-Tabachnikov identity — the single
  differential-geometric constraint distinguishing smooth curved folds
  from arbitrary `(γ, θ)` pairs.

For the gallery `axiomCount` we count `ftCompatible` as **1**
structure-encoded assumption.
-/
structure CurvedCrease where
  /-- Crease parameter length. -/
  L : ℝ
  /-- The crease is non-degenerate. -/
  hL : 0 < L
  /-- Planar curve carrying the crease (unfolded paper). -/
  γ : ℝ → ℝ × ℝ
  /-- Dihedral fold-angle profile along the crease. -/
  θ : ℝ → ℝ
  /-- Signed geodesic curvature of the crease. -/
  κg : ℝ → ℝ
  /-- Normal curvature of `γ` as a curve on the folded surface. -/
  κn : ℝ → ℝ
  /-- The fold angle is a strict dihedral angle on `[0, L]`. -/
  hθ_pos : ∀ s ∈ Set.Icc (0 : ℝ) L, 0 < θ s ∧ θ s < Real.pi
  /-- Fuchs-Tabachnikov compatibility: `κ_n(s) = κ_g(s) · cot(θ(s)/2)`.

  Encoded with `cot = (tan)⁻¹` to avoid a partial `Real.cot`. Note
  `θ s / 2 ∈ (0, π/2)` on `[0, L]` so `Real.tan (θ s / 2) > 0`. -/
  ftCompatible :
    ∀ s ∈ Set.Icc (0 : ℝ) L,
      κn s = κg s * (Real.tan (θ s / 2))⁻¹

/-- A curved crease is **straight** if its geodesic curvature is
identically zero on the parameter interval `[0, L]`.

The straight-fold limit `κ_g ≡ 0` is the canonical degeneration in
which the curved-crease formalism reduces to the classical
Huzita-Hatori straight-fold theory. -/
def CurvedCrease.IsStraight (c : CurvedCrease) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) c.L, c.κg s = 0

-- ============================================================
-- PART 2: Straight-Limit Lemma (proved internally)
-- ============================================================

/--
**Straight-fold normal-curvature vanishing.**

If `c` is a straight curved crease (geodesic curvature `≡ 0` on
`[0, L]`) then its normal curvature `κ_n` is also identically zero on
`[0, L]`. This is an immediate algebraic consequence of the
Fuchs-Tabachnikov identity `κ_n = κ_g · cot(θ/2)`: setting
`κ_g ≡ 0` forces `κ_n ≡ 0`, no smoothness or analysis required.

This is the **internal proof** of S2: it establishes the first
concrete fact about straight curved folds without depending on any
deferred sorry.
-/
theorem normal_curvature_zero_of_straight (c : CurvedCrease)
    (hStraight : c.IsStraight) :
    ∀ s ∈ Set.Icc (0 : ℝ) c.L, c.κn s = 0 := by
  intro s hs
  have hft : c.κn s = c.κg s * (Real.tan (c.θ s / 2))⁻¹ :=
    c.ftCompatible s hs
  have hκg : c.κg s = 0 := hStraight s hs
  rw [hft, hκg, zero_mul]

-- ============================================================
-- PART 3: S3 Target — Conservativity over `HHAxioms`
-- ============================================================

/-
### Conservativity statement

A **straight** curved crease — one with geodesic curvature identically
zero — should reduce to a fold satisfying one of the seven Huzita-Hatori
axioms.

The minimal claim we capture in S2 is `ExistsHHFold`: there is a Line
through the two endpoints `γ 0` and `γ L`, with the rest of `HHAxioms`
intact. S3 will sharpen this to a full case analysis on the endpoint
incidences (HH-1 through HH-7).
-/

/-- Existence of an HH-axiom-satisfying straight fold extending a given
curved crease. The minimal form: there exists an `HHAxioms` witness
together with a `Line` containing both crease endpoints. -/
def CurvedCrease.ExistsHHFold (c : CurvedCrease) : Prop :=
  ∃ _ : HHAxioms,
    ∃ l : Line, l.contains (c.γ 0) ∧ l.contains (c.γ c.L)

/--
**Conservativity (S3 target).**

A straight curved crease with distinct endpoints reduces to a fold
satisfying the straight-crease Huzita-Hatori axiom HH-1 (line through
two distinct points).

The intended proof outline (deferred to S3):

1. By `normal_curvature_zero_of_straight`, `κ_n ≡ 0` on `[0, L]`.
2. With both signed curvatures vanishing, `γ ∣ [0, L]` is a line
   segment (standard characterisation of plane curves with zero
   curvature).
3. Apply `HHAxioms.hh1` to the endpoints `γ 0` and `γ L` (which are
   distinct by hypothesis) to produce the required line.

This statement is the **minimum useful conservativity claim**: it
asserts that the curved-crease formalism is a genuine extension of the
H-H axioms, not a replacement, and not weaker. -/
theorem straight_fold_recovers_HH (c : CurvedCrease)
    (_hStraight : c.IsStraight)
    (_h_distinct : c.γ 0 ≠ c.γ c.L) :
    c.ExistsHHFold := by
  sorry  -- S3 ACT: reduce κ_g ≡ 0 case to HHAxioms.hh1 / line characterisation.
         -- S3 partial discharge (this file): the *geometric* line-through-
         -- two-distinct-points content is now constructive via
         -- `lineThrough`, `hh1_existence`, and
         -- `straight_fold_endpoints_collinear` below. The remaining gap
         -- is the construction of a full `HHAxioms` witness (HH-2..HH-7).

-- ============================================================
-- PART 3b: Constructive HH-1 — line through two distinct points (S3)
-- ============================================================

/-
### S3 partial discharge: HH-1 standalone construction

The S3 conservativity target `straight_fold_recovers_HH` decomposes into
two ingredients:

1. **Geometric**: given two distinct points in the plane, produce a line
   through both. This is the content of HH-1 (`HHAxioms.hh1`).
2. **Axiomatic**: produce a full `HHAxioms` witness (HH-1 through HH-7).

Ingredient 1 is finite and self-contained; this section discharges it.
Ingredient 2 requires proving each of the remaining six HH axioms (HH-2
through HH-7), which is a separate undertaking (HH-6 alone requires the
Beloch-fold cubic-solving construction). Future iterations should attack
these in turn.

After this section the geometric core of S3 is constructive: a straight
curved crease with distinct endpoints does admit a line through both
endpoints, and that line is computable from the endpoint coordinates.
-/

/-- The line through two points `p₁ ≠ p₂` in ℝ². Coefficients
`(a, b, c) = (y₂ - y₁, x₁ - x₂, x₂·y₁ - x₁·y₂)` cast the standard
two-point form into the `ax + by + c = 0` normalisation. The
non-degeneracy clause `(a, b) ≠ (0, 0)` follows because `p₁ ≠ p₂`
forces at least one coordinate to differ. -/
noncomputable def lineThrough (p₁ p₂ : Point) (h : p₁ ≠ p₂) : Line where
  a := p₂.2 - p₁.2
  b := p₁.1 - p₂.1
  c := p₂.1 * p₁.2 - p₁.1 * p₂.2
  nondeg := by
    by_contra hcontra
    push_neg at hcontra
    obtain ⟨ha, hb⟩ := hcontra
    apply h
    have hx : p₁.1 = p₂.1 := by linarith [sub_eq_zero.mp hb]
    have hy : p₁.2 = p₂.2 := by linarith [sub_eq_zero.mp ha]
    exact Prod.ext hx hy

/-- The line `lineThrough p₁ p₂ h` contains `p₁`. -/
theorem lineThrough_contains_left (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    (lineThrough p₁ p₂ h).contains p₁ := by
  simp only [lineThrough, Line.contains]
  ring

/-- The line `lineThrough p₁ p₂ h` contains `p₂`. -/
theorem lineThrough_contains_right (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    (lineThrough p₁ p₂ h).contains p₂ := by
  simp only [lineThrough, Line.contains]
  ring

/-- **HH-1 (existence form, standalone).** Given two distinct points in
the plane, there exists a line containing both. This is the geometric
content of the HH-1 field of `HHAxioms`; proving it independently is
the first ingredient of the eventual full `HHAxioms` instance and the
witness consumed by `straight_fold_endpoints_collinear`. -/
theorem hh1_existence : ∀ (p₁ p₂ : Point), p₁ ≠ p₂ →
    ∃ l : Line, l.contains p₁ ∧ l.contains p₂ := by
  intro p₁ p₂ h
  exact ⟨lineThrough p₁ p₂ h,
         lineThrough_contains_left p₁ p₂ h,
         lineThrough_contains_right p₁ p₂ h⟩

/-- **Geometric core of S3.** For a curved crease whose endpoints are
distinct, there exists a line through both endpoints. This is the
content of `straight_fold_recovers_HH` modulo the `HHAxioms` wrapper;
the straightness hypothesis is unused for this fragment because the
two-point form of a line does not depend on the curvature data along
`γ`. The straightness hypothesis re-enters in the full theorem when it
witnesses that `γ` actually traces a line segment between the
endpoints (rather than a more general curve happening to share the
endpoints), which is needed for the full reduction to an HH-1 fold. -/
theorem straight_fold_endpoints_collinear (c : CurvedCrease)
    (h_distinct : c.γ 0 ≠ c.γ c.L) :
    ∃ l : Line, l.contains (c.γ 0) ∧ l.contains (c.γ c.L) :=
  hh1_existence (c.γ 0) (c.γ c.L) h_distinct

-- ============================================================
-- PART 4: S4 Target — Algebraic-Curve Sharpness
-- ============================================================

/-
### Algebraic curved folds lie inside the origami field

If `γ` is an algebraic plane curve of degree at most `d` (its image is
contained in the zero set of a non-zero real polynomial of total
degree `≤ d` in two variables), then every coordinate of every point
on `γ` lies in the origami-constructible field.

The strategy combines:
* Rule-line endpoints on `γ` are algebraic over `ℚ(γ-coefficients)`
  (Demaine et al. 2011, Section 5).
* The Fuchs-Tabachnikov compatibility identity is polynomial in
  `(κ_g, κ_n, tan(θ/4))` after rationalising
  `cot(θ/2) = (1 - tan²(θ/4)) / (2 tan(θ/4))`.
* Origami solves cubics and quartics by `origami_degree_classification`
  from the parent file, so the polynomial system reduces to degrees
  dividing some `2^a · 3^b`.
-/

/-- A planar curve `γ : ℝ → ℝ × ℝ` is **algebraic of degree at most
`d`** if its image is contained in the zero set of a non-zero real
polynomial in two variables of total degree at most `d`. -/
def CurveAlgebraic (γ : ℝ → ℝ × ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ,
    p ≠ 0 ∧ p.totalDegree ≤ d ∧
    ∀ s : ℝ,
      MvPolynomial.eval
        (fun i : Fin 2 => if i = 0 then (γ s).1 else (γ s).2) p = 0

/--
**Algebraic sharpness (S4 target).**

If a curved crease `c` has algebraic crease curve `γ` of degree at
most `d`, then each coordinate of any point `γ s` (for `s ∈ [0, c.L]`)
satisfies `IsOrigamiConstructible` at some degree.

The S4 iteration will sharpen the `∃ deg` quantifier to a concrete
function of `d` (likely `deg = 2 ^ (3 * d) * 3 ^ d` or a tighter
bound).
-/
theorem curved_fold_algebraic_implies_origami
    (c : CurvedCrease) (d : ℕ)
    (_hAlg : CurveAlgebraic c.γ d) (s : ℝ)
    (_hs : s ∈ Set.Icc (0 : ℝ) c.L) :
    ∃ deg : ℕ,
      IsOrigamiConstructible (c.γ s).1 deg ∧
      IsOrigamiConstructible (c.γ s).2 deg := by
  sorry  -- S4 ACT: algebraic-curve sharpness via origami_degree_classification.

-- ============================================================
-- PART 5: S5 Target — Formal Statement of OQ-A
-- ============================================================

/-
### OQ-A as a Lean conjecture (statement only)

OQ-A asks whether the field `K_curved` (curved-fold constructible) is
strictly larger than `K_origami`. Demaine et al. 2011 conjecture that
no new POINTS are produced (so `K_curved = K_origami`) despite curved
folds tracing transcendental CURVES (the elastica family).

We state OQ-A as a Lean theorem so that the formal language is fixed;
its proof is genuinely open mathematics dating to Huffman 1976. The
`sorry` is a **permanent placeholder** until the question is settled.

The phrasing below quantifies over all real `α` and asks whether
curved-fold constructibility is equivalent to existence of some
origami-constructible degree witness. This is the natural Lean
analogue of "K_curved = K_origami as subfields of ℝ".
-/

/-- A real number `α` is **curved-fold constructible** if it appears as
the first coordinate of some point on the crease of some `CurvedCrease`,
for some parameter `s ∈ [0, L]`.

This is the simplest possible Lean witness; richer formulations (e.g.
quotient by symmetries, closure under composition, etc.) will be added
in later iterations only if needed. -/
def IsCurvedFoldConstructible (α : ℝ) : Prop :=
  ∃ c : CurvedCrease, ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) c.L ∧ α = (c.γ s).1

/--
**OQ-A (open mathematics; S5 statement only).**

The field of curved-fold-constructible real numbers coincides with the
origami-constructible field. Equivalently, no curved-fold construction
produces a point coordinate beyond what single straight-fold origami
already produces.

Demaine-Demaine-Hart-Price-Tachi 2011 conjecture this is **true**; the
formal proof is open.

This Lean statement is intentionally `sorry`-bearing as a permanent
placeholder until the mathematical question is settled. The value here
is the **formal language**, not the proof.
-/
theorem K_curved_eq_K_origami :
    ∀ α : ℝ,
      IsCurvedFoldConstructible α ↔
        ∃ d : ℕ, IsOrigamiConstructible α d := by
  sorry  -- S5 PERMANENT OPEN: Huffman 1976 / Demaine-DHPT 2011 conjecture.

-- ============================================================
-- Summary
-- ============================================================

/-
## S2 ORIENT deliverable summary

| Decl                                       | Kind      | Sorries  |
|--------------------------------------------|-----------|----------|
| `CurvedCrease`                             | structure | —        |
| `CurvedCrease.IsStraight`                  | def       | 0        |
| `normal_curvature_zero_of_straight`        | theorem   | 0 proved |
| `CurvedCrease.ExistsHHFold`                | def       | 0        |
| `straight_fold_recovers_HH`                | theorem   | 1 (S3)   |
| `CurveAlgebraic`                           | def       | 0        |
| `curved_fold_algebraic_implies_origami`    | theorem   | 1 (S4)   |
| `IsCurvedFoldConstructible`                | def       | 0        |
| `K_curved_eq_K_origami`                    | theorem   | 1 (S5)   |

Totals: **3 theorems with sorry, 1 proved theorem, 4 definitions, 1
structure. 0 `axiom` declarations. 1 structure-encoded assumption
(`ftCompatible`), so `axiomCount = 1`. Status `axiomatized`.**

## Status history

* S1 (researcher-12, 2026-05-12): OBSERVE markdown survey, no Lean.
* S2 (this file, 2026-05-12): ORIENT scaffold — structure + 3 stmts.
* S3 (planned): discharge `straight_fold_recovers_HH`.
* S4 (this file, 2026-05-12): constructive HH-2 (perpendicular
  bisector) — second ingredient of the eventual full `HHAxioms`
  witness. See Part 6 below.
* S5 (planned, OPEN): `K_curved_eq_K_origami` remains a sorry.
-/

-- ============================================================
-- PART 6: Constructive HH-2 — Perpendicular Bisector (S4)
-- ============================================================

/-
### S4 partial discharge: HH-2 standalone construction

The S3 conservativity target `straight_fold_recovers_HH` reduces to
the geometric content of HH-1 plus the construction of a full
`HHAxioms` witness. S3 (open PR, this slug) discharged the HH-1
ingredient via `lineThrough`, `hh1_existence`, and
`straight_fold_endpoints_collinear`. This S4 section discharges the
HH-2 ingredient: for any two distinct points, the perpendicular
bisector is a fold line that places the first point exactly onto the
second.

Concretely we exhibit `perpBisector p₁ p₂ h : Line` for `h : p₁ ≠ p₂`
and prove `reflectAcross (perpBisector p₁ p₂ h) p₁ = p₂`. This is
HH-2 (`AngleTrisectionOQ05.HHAxioms.hh2`) in standalone form, no
longer relying on a witnessing `HHAxioms` instance.

Combined with S3's HH-1 discharge, only HH-3 through HH-7 remain.
HH-4 (perpendicular through a point) is the next natural target;
HH-6 (Beloch fold) is the deepest and last.

After this section the geometric content of HH-2 is constructive:
the perpendicular bisector is computable from the endpoint
coordinates and provably maps one endpoint to the other under
reflection. No new `sorry` is introduced; the file's sorry count is
unchanged at 3.
-/

/-- The perpendicular bisector of two distinct points `p₁ ≠ p₂` in
the plane. Coefficients
`(a, b, c) = (p₂.1 - p₁.1, p₂.2 - p₁.2,
  -((p₂.1² - p₁.1²) + (p₂.2² - p₁.2²)) / 2)`
encode the locus of points equidistant from `p₁` and `p₂`. The
non-degeneracy clause `(a, b) ≠ (0, 0)` follows because `p₁ ≠ p₂`
forces at least one coordinate to differ. -/
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

/-- The squared chord length `(p₂.1 - p₁.1)² + (p₂.2 - p₁.2)²` is
strictly positive when `p₁ ≠ p₂`. Used to discharge the denominator
in `reflectAcross_perpBisector`. -/
theorem perpBisector_dirSq_pos (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    0 < (p₂.1 - p₁.1)^2 + (p₂.2 - p₁.2)^2 := by
  rcases eq_or_ne p₁.1 p₂.1 with hx | hx
  · have hy : p₁.2 ≠ p₂.2 := fun heq => h (Prod.ext hx heq)
    have h2 : 0 < (p₂.2 - p₁.2)^2 :=
      sq_pos_of_ne_zero _ (sub_ne_zero.mpr (Ne.symm hy))
    nlinarith [sq_nonneg (p₂.1 - p₁.1)]
  · have h1 : 0 < (p₂.1 - p₁.1)^2 :=
      sq_pos_of_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))
    nlinarith [sq_nonneg (p₂.2 - p₁.2)]

/-- **HH-2 reflection law.** The perpendicular bisector of `p₁` and
`p₂` reflects `p₁` onto `p₂`. Algebraically, plugging the
`perpBisector` coefficients into `reflectAcross` yields `t = -1` for
`p₁`, so `p₁ - t · (a, b) = p₁ + (a, b) = p₂`. This is the defining
geometric property of HH-2 and the witness consumed by
`hh2_existence` below. -/
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

/-- **HH-2 (existence form, standalone).** Given two distinct points
in the plane, there exists a fold line whose reflection sends the
first onto the second. This is the geometric content of the HH-2
field of `HHAxioms`; the explicit witness is the perpendicular
bisector. Together with `hh1_existence` (S3) this provides two of
the seven HH ingredients required by `straight_fold_recovers_HH`. -/
theorem hh2_existence : ∀ (p₁ p₂ : Point), p₁ ≠ p₂ →
    ∃ l : Line, reflectAcross l p₁ = p₂ := by
  intro p₁ p₂ h
  exact ⟨perpBisector p₁ p₂ h, reflectAcross_perpBisector p₁ p₂ h⟩


-- ============================================================
-- PART 7: Constructive HH-4 — Perpendicular Through a Point (S5)
-- ============================================================

/-
### S5 partial discharge: HH-4 standalone construction

After S3 (HH-1: `lineThrough` / `hh1_existence`) and S4 (HH-2:
`perpBisector` / `hh2_existence`), this S5 section discharges HH-4:
given any point `P` and line `ℓ`, the perpendicular fold through `P`
preserves `ℓ` as a set under reflection.

Concretely we exhibit `perpThroughPoint p ℓ : Line` and prove:

1. `perpThroughPoint_normSq_pos` — denominator non-vanishing (chord
   length of the fold's direction vector is positive);
2. `perpThroughPoint_contains` — the fold passes through `P`;
3. `reflectAcross_perpThroughPoint_preserves` — reflection across the
   fold maps every point of `ℓ` to a point of `ℓ`.

These combine into a standalone `hh4_existence` theorem matching the
`hh4` field of `AngleTrisectionOQ05.HHAxioms` in isolation.

### Geometric content of HH-4

For a line `ℓ : a x + b y + c = 0` (normal vector `(a, b)`) and a point
`P`, the perpendicular fold through `P` has its OWN normal parallel to
the DIRECTION of `ℓ`. Take the fold's normal to be `(-ℓ.b, ℓ.a)` (a 90°
rotation of `(ℓ.a, ℓ.b)`) and choose the constant term to force the
fold to pass through `P`:

  a' = -ℓ.b
  b' =  ℓ.a
  c' =  ℓ.b · P.1 - ℓ.a · P.2

Under reflection across this fold, every point `q ∈ ℓ` satisfies

  ℓ.a · q'.1 + ℓ.b · q'.2 + ℓ.c
    = ℓ.a · (q.1 - t · (-ℓ.b)) + ℓ.b · (q.2 - t · ℓ.a) + ℓ.c
    = (ℓ.a · q.1 + ℓ.b · q.2 + ℓ.c) + t · (ℓ.a · ℓ.b - ℓ.b · ℓ.a)
    = 0 + t · 0 = 0,

so `q' ∈ ℓ` as required.

After this section the geometric content of HH-4 is constructive:
the perpendicular fold is computable from `(P, ℓ)` and provably
preserves `ℓ` setwise. No new `sorry` is introduced; the file's
sorry count is unchanged at 3.

Combined with S3 (HH-1) and S4 (HH-2), three of the seven HH
ingredients are now constructive. The remaining four are HH-3 (angle
bisector), HH-5 (fold through `P₂` placing `P₁` on `ℓ`), HH-6 (Beloch
fold — the cubic one), and HH-7 (Hatori).
-/

/-- The squared norm `ℓ.a² + ℓ.b²` is strictly positive. This is the
denominator that appears in `reflectAcross` and must be non-vanishing
for the reflection to be well-defined. -/
theorem perpThroughPoint_normSq_pos (ℓ : Line) :
    0 < ℓ.a^2 + ℓ.b^2 := by
  rcases ℓ.nondeg with ha | hb
  · nlinarith [sq_pos_of_ne_zero _ ha, sq_nonneg ℓ.b]
  · nlinarith [sq_pos_of_ne_zero _ hb, sq_nonneg ℓ.a]

/-- The **perpendicular fold through `P` orthogonal to `ℓ`**. The
fold's normal vector `(-ℓ.b, ℓ.a)` is a 90° rotation of `ℓ`'s normal
`(ℓ.a, ℓ.b)`, so the fold is perpendicular to `ℓ`. The constant term
`ℓ.b · P.1 - ℓ.a · P.2` makes the fold pass through `P`.

Non-degeneracy follows from `ℓ`'s non-degeneracy: at least one of
`ℓ.a`, `ℓ.b` is nonzero, hence at least one of the fold's coefficients
`(-ℓ.b, ℓ.a)` is nonzero. -/
noncomputable def perpThroughPoint (p : Point) (ℓ : Line) : Line where
  a := -ℓ.b
  b := ℓ.a
  c := ℓ.b * p.1 - ℓ.a * p.2
  nondeg := by
    rcases ℓ.nondeg with ha | hb
    · exact Or.inr ha
    · exact Or.inl (neg_ne_zero.mpr hb)

/-- The perpendicular fold passes through its anchor point. Routine
algebra: the fold's defining equation evaluated at `p` yields
`-ℓ.b · p.1 + ℓ.a · p.2 + (ℓ.b · p.1 - ℓ.a · p.2) = 0`. -/
theorem perpThroughPoint_contains (p : Point) (ℓ : Line) :
    (perpThroughPoint p ℓ).contains p := by
  simp only [Line.contains, perpThroughPoint]
  ring

/-- **HH-4 line-preservation law.** Reflection across the
perpendicular fold through `p` (orthogonal to `ℓ`) maps every point of
`ℓ` to a point of `ℓ`. Geometrically, the fold is parallel to `ℓ`'s
normal, so it acts on `ℓ` by reversing direction while preserving the
locus.

Algebraically: writing the fold as `(-ℓ.b, ℓ.a, ℓ.b · p.1 - ℓ.a · p.2)`
and applying `reflectAcross`, the cross-term `ℓ.a · ℓ.b - ℓ.b · ℓ.a`
vanishes, so the image satisfies `ℓ`'s equation iff `q` did. -/
theorem reflectAcross_perpThroughPoint_preserves
    (p : Point) (ℓ : Line) (q : Point) (hq : ℓ.contains q) :
    ℓ.contains (reflectAcross (perpThroughPoint p ℓ) q) := by
  have hPos : 0 < ℓ.a^2 + ℓ.b^2 := perpThroughPoint_normSq_pos ℓ
  have hD : (-ℓ.b)^2 + ℓ.a^2 ≠ 0 := by
    have hEq : (-ℓ.b)^2 + ℓ.a^2 = ℓ.a^2 + ℓ.b^2 := by ring
    rw [hEq]; exact ne_of_gt hPos
  simp only [Line.contains, reflectAcross, perpThroughPoint] at hq ⊢
  field_simp
  linear_combination ((-ℓ.b)^2 + ℓ.a^2) * hq

/-- **HH-4 (existence form, standalone).** Given any point `P` and any
line `ℓ`, there exists a fold line that passes through `P` and
preserves `ℓ` as a set under reflection. This is the geometric content
of the HH-4 field of `HHAxioms`; the explicit witness is the
perpendicular fold through `P`. Together with `hh1_existence` (S3) and
`hh2_existence` (S4) this provides three of the seven HH ingredients
required by `straight_fold_recovers_HH`. -/
theorem hh4_existence : ∀ (p : Point) (ℓ : Line),
    ∃ l : Line, l.contains p ∧
      ∀ q : Point, ℓ.contains q → ℓ.contains (reflectAcross l q) := by
  intro p ℓ
  refine ⟨perpThroughPoint p ℓ, perpThroughPoint_contains p ℓ, ?_⟩
  intro q hq
  exact reflectAcross_perpThroughPoint_preserves p ℓ q hq

end AngleTrisectionOQ05OQ04
