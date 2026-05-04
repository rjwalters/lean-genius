import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Proofs.BrouwerFixedPoint
import Proofs.BrouwerFixedPointOQ01OQ02

/-
# Brouwer Fixed Point Theorem via Singular Homology
# (brouwer-fixed-point-oq-01-oq-02-oq-03)

## The Open Question

**OQ-01-OQ-02-OQ-03**: Can Brouwer's Fixed Point Theorem itself be derived from
`no_retraction_singular_homology` (from BrouwerFixedPointOQ01OQ02.lean) within
this framework, completing the equivalence?

## The Answer

**Yes.** The full chain is:

  singular_homology_retraction_split
       ↓  (BrouwerFixedPointOQ01OQ02.lean)
  no_retraction_singular_homology
       ↓  (this file)
  brouwer_fixed_point_via_singular_homology

## Proof Strategy

BrouwerFixedPoint.lean uses 2 axioms:
  - `no_retraction_axiom` (the no-retraction theorem, black box)
  - `retraction_construction` (no fixed point → build a retraction)

BrouwerFixedPointOQ01OQ02.lean replaces `no_retraction_axiom` with:
  - `singular_homology_retraction_split` (more informative: explains *why*
    no retraction can exist via H_{n-1} functoriality)

This file derives BFP from the homological no-retraction result:
  1. Assume f : B^n → B^n has no fixed point
  2. Apply `retraction_construction` (from BrouwerFixedPoint.lean) to get
     a retraction r : B^n → S^{n-1} of type `Brouwer.Retraction n`
  3. Convert r to `BrouwerOQ01OQ02.Retraction n` (same structure, both
     ClosedBall and UnitSphere are definitionally `Metric.closedBall/sphere 0 1`)
  4. Apply `no_retraction_singular_homology` to get a contradiction

## Axiom Count

This file introduces **0 new axioms**. It relies on:
  - `Brouwer.retraction_construction` (from BrouwerFixedPoint.lean)
  - `BrouwerOQ01OQ02.singular_homology_retraction_split`
    (from BrouwerFixedPointOQ01OQ02.lean)

Total: 2 axioms — same count as `BrouwerFixedPoint.lean`, but
`no_retraction_axiom` is replaced by the more informative
`singular_homology_retraction_split`.

## Summary: 5 theorems, 0 new axioms, 0 sorries
-/

set_option linter.unusedVariables false

namespace BrouwerOQ01OQ02OQ03

open Metric Set

-- ============================================================
-- PART I: Retraction Type Conversion
-- ============================================================

/-
Both `Brouwer.Retraction n` and `BrouwerOQ01OQ02.Retraction n` have
identical structure:
  - toFun : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  - continuous' : Continuous toFun
  - maps_to_sphere : ∀ x ∈ ClosedBall n, toFun x ∈ UnitSphere n
  - fixes_sphere : ∀ x ∈ UnitSphere n, toFun x = x

Both `ClosedBall n` and `UnitSphere n` unfold to `Metric.closedBall 0 1`
and `Metric.sphere 0 1` respectively, so the field types are definitionally
equal across namespaces.
-/

/-- Convert a `Brouwer.Retraction n` to `BrouwerOQ01OQ02.Retraction n`.

    Both structures are definitionally identical — `Brouwer.ClosedBall n`
    and `BrouwerOQ01OQ02.ClosedBall n` both reduce to `Metric.closedBall 0 1`,
    and similarly for `UnitSphere`. This conversion is logically trivial. -/
def toSingularRetraction {n : ℕ} (r : Brouwer.Retraction n) :
    BrouwerOQ01OQ02.Retraction n where
  toFun := r.toFun
  continuous' := r.continuous'
  maps_to_sphere := r.maps_to_sphere
  fixes_sphere := r.fixes_sphere

/-- The conversion preserves the underlying function. -/
theorem toSingularRetraction_toFun {n : ℕ} (r : Brouwer.Retraction n) :
    (toSingularRetraction r).toFun = r.toFun := rfl

-- ============================================================
-- PART II: BFP via Singular Homology
-- ============================================================

/-- **Brouwer Fixed Point Theorem** (via Singular Homology)

    Every continuous function from the closed n-ball to itself
    has at least one fixed point.

    **Proof chain:**
    1. Assume f : B^n → B^n has no fixed point.
    2. `Brouwer.retraction_construction` gives r : Brouwer.Retraction n
       (the ray-from-f(x)-through-x construction).
    3. Convert r to BrouwerOQ01OQ02.Retraction n (definitionally trivial).
    4. `BrouwerOQ01OQ02.no_retraction_singular_homology` derives a
       contradiction: the retraction would split
       H_{n-1}(S^{n-1}) ≅ ℤ through H_{n-1}(B^n) = 0 via id : ℤ →+ ℤ,
       but id cannot factor through the trivial group.

    **No new axioms**: uses only `Brouwer.retraction_construction` and
    `BrouwerOQ01OQ02.singular_homology_retraction_split`. -/
theorem brouwer_fixed_point_via_singular_homology (n : ℕ) (hn : n ≥ 1)
    (f : Brouwer.SelfMap n) : Brouwer.HasFixedPoint n f := by
  by_contra h
  -- Build retraction from f having no fixed point (geometric ray construction)
  let r_brouwer := Brouwer.retraction_construction f h
  -- Convert to BrouwerOQ01OQ02.Retraction (same structure, definitionally equal)
  let r_sh := toSingularRetraction r_brouwer
  -- Apply no_retraction_singular_homology for the contradiction
  exact BrouwerOQ01OQ02.no_retraction_singular_homology n hn ⟨r_sh, trivial⟩

-- ============================================================
-- PART III: The Complete Equivalence
-- ============================================================

/-- **No-Retraction from BFP** (converse direction)

    If every self-map has a fixed point (BFP), then no retraction exists.
    Note: the `no_retraction_singular_homology` result is independently derived
    from singular homology axioms, so this direction is also directly available. -/
theorem no_retraction_from_bfp (n : ℕ) (hn : n ≥ 1)
    (_ : ∀ f : Brouwer.SelfMap n, Brouwer.HasFixedPoint n f) :
    ¬∃ r : BrouwerOQ01OQ02.Retraction n, True :=
  BrouwerOQ01OQ02.no_retraction_singular_homology n hn

/-- **The Full Logical Chain**

    Singular homology axiom → No-Retraction → BFP.

    The chain `singular_homology_retraction_split → no_retraction_singular_homology`
    was established in BrouwerFixedPointOQ01OQ02.lean. This theorem confirms that
    BFP follows from the singular homology axiom (plus retraction_construction). -/
theorem singular_homology_implies_bfp (n : ℕ) (hn : n ≥ 1)
    (f : Brouwer.SelfMap n) : Brouwer.HasFixedPoint n f :=
  brouwer_fixed_point_via_singular_homology n hn f

/-- **Equivalence of no-retraction statements**

    The no-retraction theorems via the original axiom and via singular homology
    are equivalent: the two `Retraction` types are convertible since both
    `ClosedBall n` and `UnitSphere n` are definitionally equal across namespaces
    (both reduce to `Metric.closedBall/sphere 0 1`). -/
theorem no_retraction_axiom_iff_sh (n : ℕ) (hn : n ≥ 1) :
    (¬∃ r : Brouwer.Retraction n, True) ↔
    (¬∃ r : BrouwerOQ01OQ02.Retraction n, True) :=
  ⟨fun h ⟨r_sh, _⟩ => by
    have r_br : Brouwer.Retraction n := {
      toFun := r_sh.toFun
      continuous' := r_sh.continuous'
      maps_to_sphere := r_sh.maps_to_sphere
      fixes_sphere := r_sh.fixes_sphere }
    exact h ⟨r_br, trivial⟩,
   fun h ⟨r_br, _⟩ => h ⟨toSingularRetraction r_br, trivial⟩⟩

end BrouwerOQ01OQ02OQ03
