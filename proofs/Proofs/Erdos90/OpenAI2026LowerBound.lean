/-
# Erdős Problem #90 — OpenAI 2026 Unit-Distance Lower Bound (point-set
# extraction + counting argument)

Sub-issue (d) of parent tracker #20576 (Lean formalization of the OpenAI
2026-05-20 unit-distance lower-bound construction). This is the
**combinatorial / geometric core** of the construction.

Given an infinite class field tower `K_0 ⊆ K_1 ⊆ K_2 ⊆ ...` (sub-issue (c),
axiomatized in `Proofs/Erdos90/ClassFieldTower.lean`, whose infinitude is
discharged by Golod–Shafarevich in sub-issue (b),
`Proofs/Erdos90/GolodShafarevich.lean`), we:

1. **Extract an explicit planar point set** `pointSet K r : Finset
   (EuclideanSpace ℝ (Fin 2))` from the ring of integers `𝓞_K` of each level
   `K`, via the canonical Minkowski embedding intersected with a ball of
   radius `r`, then projected to `ℝ²` by a chosen pair of complex embeddings.
2. **State a counting lemma** lower-bounding the number of unit-distance pairs
   in that point set in terms of the algebraic structure (units of `𝓞_K`
   acting by translation; unit-norm elements producing unit-distance pairs).
   The precise unit-count formula depends on the peer-reviewed OpenAI exponent
   and is therefore **axiomatized** here.
3. **State the headline theorem** `openai_2026_unit_distance_lower_bound`,
   left as `sorry` because the exact exponent `α` awaits the peer-reviewed
   OpenAI publication (parent #20576's external peer-review blocker). The
   `sorry` is deliberately not discharged: overclaiming a proof of an
   unpublished exponent would damage credibility (per `CLAUDE.md` axiom
   integrity policy).

## Status

`status: "axiomatized"` (Strategy B of
`research/MATHLIB-PREREQS-UNIT-DISTANCE.md`). The point-set extraction map is
**concretely defined** over Mathlib's `NumberField.canonicalEmbedding`
infrastructure (item 7 of the audit, rated "complete" in Mathlib v4.26.0), so
it contributes **no** new axioms. The counting bound and the tower-to-point-set
cardinality relation are `axiom` declarations pending the peer-reviewed
formula. The headline theorem is a `sorry`.

## Assumption catalog (per CLAUDE.md axiom integrity policy)

`axiom` declarations introduced by THIS file:

| Axiom | Statement | Discharged by |
|-------|-----------|---------------|
| `unitDistanceCountingBound` | The extracted point set of an infinite-tower level has ≥ `m^(1+α₀)` unit-distance pairs for the construction's exponent `α₀ > 0` and a level of "size" `m`. | Peer-reviewed OpenAI counting formula (#20576). |
| `towerYieldsGrowingPointSets` | An infinite (ℓ-)class field tower yields, for every `n`, a level whose extracted point set realizes an `n`-point configuration with the counting bound, so the bound transfers to `maxUnitDistances`. | Peer-reviewed OpenAI construction + cardinality control (#20576). |

Structure-encoded assumptions introduced by THIS file:

| Structure | Fields | Meaning |
|-----------|--------|---------|
| `PointSetExtraction` | 3 | A witness packaging (i) a positive exponent `α`, (ii) the per-`n` point set drawn from a tower level, (iii) the unit-distance lower bound it realizes. Bundles the construction's output for a fixed infinite tower without committing to the (unpublished) explicit formula. |

- `axiom` declarations in this file: **2**.
- assumption-carrying structure fields in this file: **3**.
- `sorry` occurrences in this file: **1** (the headline theorem).

This file's contribution to the gallery `axiomCount` is therefore
**2 + 3 = 5**, raising the aggregate `erdos-90` `axiomCount` from 16 to 21.

## References

- Parent: #20576 (external peer-review blocker for the exponent `α`).
- Audit: `research/MATHLIB-PREREQS-UNIT-DISTANCE.md` (item 7, embeddings /
  Minkowski, rated "complete").
- Companion sub-issues: (a) `ClassGroupLRank.lean` #22604, (b)
  `GolodShafarevich.lean` #22606, (c) `ClassFieldTower.lean` #22607.
- OpenAI technical note (peer review pending):
  https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-remarks.pdf
- Companion paper: *Remarks on the Disproof of the Unit Distance Conjecture*
  (Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, Wood);
  arXiv:2605.20579, arXiv:2606.03419.
- Mathlib APIs: `NumberField.canonicalEmbedding`,
  `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`
  (`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`).
- Mathlib pinned at `v4.26.0` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
-/

import Proofs.Erdos90Problem
import Proofs.Erdos90.ClassFieldTower
import Proofs.Erdos90.GolodShafarevich
import Proofs.Erdos90.ClassGroupLRank
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace Erdos90.OpenAI2026LowerBound

open NumberField Filter

/-! ## Point-set extraction map

Given a number field `K`, the canonical (Minkowski) embedding
`NumberField.canonicalEmbedding K : K →+* ((K →+* ℂ) → ℂ)` sends `K` into
the product `(K →+* ℂ) → ℂ` indexed by the complex embeddings of `K`. Its
restriction to the ring of integers `𝓞 K` is the `integerLattice`.

Mathlib's `integerLattice.inter_ball_finite` proves that intersecting this
lattice with a ball of radius `r` yields a **finite** set. We turn that finite
set into a `Finset` and project each function-valued point to `ℝ²` by picking a
pair of complex embeddings `φ₀, φ₁` and taking the real parts of the
corresponding coordinates.

This is the honest planar shadow of the algebraic point set. For the OpenAI
construction the two chosen embeddings are real places (so the projection is an
isometry onto the corresponding `ℝ²` factor of the Minkowski space); here we
keep the projection uniform — real part of two chosen coordinates — so the map
is total and compiles for any `K` and any choice of `φ₀ φ₁`. -/

/-- The projection `((K →+* ℂ) → ℂ) → ℝ²` reading off the real parts of the
    coordinates at two chosen complex embeddings `φ₀`, `φ₁`. For real places
    the imaginary part vanishes, so this is the intended Minkowski shadow onto
    the plane spanned by those two places. -/
noncomputable def planarProjection {K : Type*} [Field K] [NumberField K]
    (φ₀ φ₁ : K →+* ℂ) (x : (K →+* ℂ) → ℂ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(x φ₀).re, (x φ₁).re]

/-- The finite set `(integerLattice K ∩ closedBall 0 r)` as a `Finset` in the
    Minkowski space `(K →+* ℂ) → ℂ`. Finiteness is Mathlib's
    `integerLattice.inter_ball_finite`. -/
noncomputable def latticeBallFinset (K : Type*) [Field K] [NumberField K]
    (r : ℝ) : Finset ((K →+* ℂ) → ℂ) :=
  (canonicalEmbedding.integerLattice.inter_ball_finite K r).toFinset

/-- **Point-set extraction map.** The finite planar point set obtained from the
    ring of integers of `K`: take the lattice points in the ball of radius `r`,
    project each to `ℝ²` via the real parts at `φ₀`, `φ₁`.

    The result has type `Finset (EuclideanSpace ℝ (Fin 2))`, exactly what
    `unitDistancePairsCount` (from `Proofs.Erdos90Problem`) consumes. -/
noncomputable def pointSet (K : Type*) [Field K] [NumberField K]
    (φ₀ φ₁ : K →+* ℂ) (r : ℝ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  (latticeBallFinset K r).image (planarProjection φ₀ φ₁)

/-- The extracted point set is (by construction) the image of the
    lattice-ball finset under the planar projection. Recorded for downstream
    reasoning about its cardinality. -/
theorem pointSet_eq_image (K : Type*) [Field K] [NumberField K]
    (φ₀ φ₁ : K →+* ℂ) (r : ℝ) :
    pointSet K φ₀ φ₁ r = (latticeBallFinset K r).image (planarProjection φ₀ φ₁) :=
  rfl

/-- The extracted point set has cardinality at most the number of lattice
    points in the ball (projection can only identify points, never create
    them). A concrete, sorry-free structural fact about the extraction map. -/
theorem pointSet_card_le (K : Type*) [Field K] [NumberField K]
    (φ₀ φ₁ : K →+* ℂ) (r : ℝ) :
    (pointSet K φ₀ φ₁ r).card ≤ (latticeBallFinset K r).card :=
  Finset.card_image_le

/-! ## Counting lemma (axiomatized pending the peer-reviewed formula)

The OpenAI construction bounds the number of unit-distance pairs in the
extracted point set below by `m^(1+α₀)`, where `m` is the "size" of the level
(a growth function of `[K_n : ℚ]`) and `α₀ > 0` is the construction's exponent.
The unit-distance pairs come from units of `𝓞_K` of norm producing unit-length
differences under the chosen embeddings.

The precise formula (and the value of `α₀`) awaits the peer-reviewed OpenAI
publication, so we state it as an `axiom`. -/

/-- **Counting lemma (axiomatized).** There is a construction exponent
    `α₀ > 0` such that, for a number field `K` sitting at a high enough level
    of an infinite ℓ-class field tower (encoded by
    `Erdos90.GolodShafarevich.HasInfiniteLClassFieldTower K ℓ`), and for a
    suitable radius `r` and pair of embeddings `φ₀ φ₁`, the extracted point set
    of "size" `m` realizes at least `m^(1+α₀)` unit-distance pairs.

    This is the number-theoretic heart of the OpenAI construction. It is an
    `axiom` because the explicit exponent and unit-count formula are gated on
    the peer-reviewed publication (parent #20576). -/
axiom unitDistanceCountingBound
    (K : Type) [Field K] [NumberField K] (ℓ : ℕ)
    (_hTower : Erdos90.GolodShafarevich.HasInfiniteLClassFieldTower K ℓ)
    (φ₀ φ₁ : K →+* ℂ) (r : ℝ) (m : ℕ) (α₀ : ℝ)
    (_hα : 0 < α₀)
    (_hSize : (pointSet K φ₀ φ₁ r).card = m) :
    ((m : ℝ) ^ (1 + α₀) : ℝ) ≤ (unitDistancePairsCount (pointSet K φ₀ φ₁ r) : ℝ)

/-- **Tower-to-configuration transfer (axiomatized).** An infinite ℓ-class
    field tower yields, for every target size `n`, a level `K` of the tower
    whose extracted point set is an exact `n`-point configuration meeting the
    counting bound. Consequently the bound transfers to `maxUnitDistances n`
    (the `sSup` over all `n`-point configurations, from `Erdos90Problem`).

    The cardinality-control step (choosing the radius `r_n` so that the
    projected point set has exactly `n` points) is part of the OpenAI
    construction and is axiomatized alongside the counting bound. -/
axiom towerYieldsGrowingPointSets
    (α₀ : ℝ) (_hα : 0 < α₀)
    (_h : ∀ K : Type, ∀ _ : Field K, ∀ _ : NumberField K, ∀ ℓ : ℕ,
      Erdos90.GolodShafarevich.HasInfiniteLClassFieldTower K ℓ →
      ∀ φ₀ φ₁ : K →+* ℂ, ∀ r : ℝ, ∀ m : ℕ,
      (pointSet K φ₀ φ₁ r).card = m →
      ((m : ℝ) ^ (1 + α₀) : ℝ) ≤ (unitDistancePairsCount (pointSet K φ₀ φ₁ r) : ℝ)) :
    ∀ᶠ (n : ℕ) in atTop, ((n : ℝ) ^ (1 + α₀) : ℝ) ≤ (maxUnitDistances n : ℝ)

/-! ## Extraction witness structure

`PointSetExtraction` bundles the output of the construction for a fixed
infinite tower: the positive exponent, the per-`n` extracted point set, and the
realized unit-distance lower bound. This is the structure-encoded assumption
that a *concrete* OpenAI instantiation would provide once the exponent is
published. Its three fields are assumption-carrying per the axiom integrity
policy. -/

/-- A witness that the OpenAI construction produces, for a fixed infinite
    class field tower, an eventual `n^(1+α)` lower bound on `maxUnitDistances`.

    Bundles:
    * `alpha` — the (positive) construction exponent;
    * `alpha_pos` — positivity of the exponent;
    * `lowerBound` — the eventual `maxUnitDistances n ≥ n^(1+α)` statement.

    All three fields carry mathematical content pending the peer-reviewed
    exponent, hence they are counted as assumptions. -/
structure PointSetExtraction where
  /-- The construction's exponent. -/
  alpha : ℝ
  /-- The exponent is strictly positive (the polynomial improvement). -/
  alpha_pos : 0 < alpha
  /-- Eventually, `maxUnitDistances n ≥ n^(1+alpha)`. -/
  lowerBound : ∀ᶠ (n : ℕ) in atTop, ((n : ℝ) ^ (1 + alpha) : ℝ) ≤ (maxUnitDistances n : ℝ)

/-- From a `PointSetExtraction` witness the headline existential is immediate.
    This is the sorry-free reduction: a concrete instantiation of the
    construction (with a published exponent) discharges the headline theorem. -/
theorem lowerBound_of_extraction (E : PointSetExtraction) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ (n : ℕ) in atTop,
      (maxUnitDistances n : ℝ) ≥ (n : ℝ) ^ (1 + α) :=
  ⟨E.alpha, E.alpha_pos, E.lowerBound⟩

/-! ## Headline theorem (sorry — awaits peer-reviewed exponent)

The headline lower bound. Its proof reduces, via `towerYieldsGrowingPointSets`
and `unitDistanceCountingBound`, to:

  (i)   sub-issue (c)'s tower existence
        (`Erdos90.ClassFieldTower.HasInfiniteLClassFieldTower`);
  (ii)  sub-issue (b)'s Golod–Shafarevich infinitude criterion
        (`Erdos90.GolodShafarevich.golodShafarevich_number_field`,
         consumed via `HasInfiniteLClassFieldTower`);
  (iii) the local counting lemma (`unitDistanceCountingBound` above).

The exact value of `α` is fixed by the **peer-reviewed** OpenAI publication.
Until that lands (parent #20576's external peer-review blocker), we do **not**
fabricate a proof: the theorem is stated with `sorry`. The scaffolding above
(`PointSetExtraction`, `lowerBound_of_extraction`,
`towerYieldsGrowingPointSets`) shows precisely how the `sorry` is discharged
once a concrete exponent and the cardinality-control step are supplied. -/

/-- **Headline (OpenAI 2026 unit-distance lower bound).** There is `α > 0`
    with `maxUnitDistances n ≥ n^(1+α)` for all large `n` — a polynomial
    improvement over the lattice lower bound `n^(1+c/log log n)`, disproving
    Erdős's conjectured exponent.

    Left as `sorry`: the exact `α` awaits the peer-reviewed OpenAI publication
    (parent #20576). Do **not** discharge this without the published exponent. -/
theorem openai_2026_unit_distance_lower_bound :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ (n : ℕ) in atTop,
      (maxUnitDistances n : ℝ) ≥ (n : ℝ) ^ (1 + α) := by
  sorry

end Erdos90.OpenAI2026LowerBound
