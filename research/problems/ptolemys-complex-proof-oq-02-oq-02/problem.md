# Problem: Ptolemy → Chord/Radius-r Generalization + Law of Cosines

**Slug**: ptolemys-complex-proof-oq-02-oq-02
**Created**: 2026-05-12 (seeker-init)
**Status**: Active (S1 OBSERVE complete)
**Source**: seeker-selected (parent: `ptolemys-complex-proof-oq-02`, openQuestions[1])
**Grandparent**: `ptolemys-complex-proof` — Ptolemy's inequality via complex-number algebraic identity, COMPLETED.
**Parent**: `ptolemys-complex-proof-oq-02` (`Proofs.PtolemysComplexProofOQ02`, 351 LOC) —
sine addition formula `sin(α+β) = sin α cos β + cos α sin β` derived from Ptolemy applied
to four specific points on the **unit circle**, COMPLETED.

## Problem Statement

### Formal Statement (informal)

Generalize the parent's unit-circle chord lemmas (six `norm_…` lemmas around line 70–179
of `PtolemysComplexProofOQ02.lean`) to a circle of arbitrary radius $r > 0$. The
key chord-length identity is:

$$
\| z - w \| = 2r \cdot \sin\left(\tfrac{|\theta_z - \theta_w|}{2}\right)
$$

for any two points $z = r e^{i \theta_z}$ and $w = r e^{i \theta_w}$ on the circle of
radius $r$. Apply Ptolemy's theorem to a generic cyclic quadrilateral on a radius-$r$
circle to derive the **law of cosines** for arbitrary triangles, completing the historical
chord-table → trigonometry transition.

### Plain Language

The parent slug proves sine-addition on a **unit** circle (radius 1) by picking four
specific points: $1, e^{2i\alpha}, -1, e^{-2i\beta}$. The chord lengths come out as $2\sin\alpha$,
$2\cos\alpha$, etc. — each carrying a factor of $2$ that traces back to the radius.

The sub-question asks: do the lemmas work on a circle of **arbitrary radius** $r$? The
chord lengths become $2r \sin(\alpha)$, $2r \cos(\alpha)$, etc., and Ptolemy applied to
a generic inscribed quadrilateral should give the **law of cosines**: for a triangle
with sides $a, b, c$ and opposite angles $A, B, C$,
$c^2 = a^2 + b^2 - 2ab\cos C$.

### Why This Matters

- **Historical**: Ptolemy (c. 150 AD) computed his chord tables on a circle of radius 60
  (the sexagesimal "unit"), not radius 1. Generalizing to radius $r$ matches the
  historical setup and makes the chord-table derivation faithful.
- **Mathematical**: the law of cosines is a *consequence* of Ptolemy + chord-on-radius-r
  formulas. This route is rarely presented in modern textbooks (which derive it from the
  dot product), but it is the historically correct one. Formalizing it closes the
  history-of-trigonometry loop that started with `PtolemysComplexProof`.
- **Mathlib coverage**: Mathlib v4.26.0 has `Real.cos_sq_half`, `Real.sin_sq_half`,
  and the dot-product law of cosines via `EuclideanSpace.norm_sub_sq` etc., but **does
  not derive the law of cosines from Ptolemy** anywhere.

## Known Results

### What's Already Proven

- **`Proofs.PtolemysComplexProofOQ02` (parent slug, COMPLETED)**: sine addition formula
  on the unit circle, 351 LOC, 0 sorries. Uses six chord-length lemmas
  (`norm_one_sub_exp_two_alpha`, etc.) all specialized to radius 1.
- **`Proofs.PtolemysComplexProof` (grandparent)**: Ptolemy's inequality via the
  complex-number algebraic identity `(z₁−z₃)(z₂−z₄) = (z₁−z₂)(z₃−z₄) + (z₂−z₃)(z₁−z₄)`,
  taking norms + triangle inequality. CommRing-level identity, ℂ-level inequality.
- **Mathlib `Real.cos_sub_cos`, `Real.sin_sub`, etc.**: identities for chord lengths
  on the unit circle (used by the parent).
- **Mathlib `EuclideanSpace.norm_sub_sq_eq`**: dot-product law of cosines (an alternative
  proof of the same law, but **not** via Ptolemy).

### What's Still Open

1. **The chord-length lemmas are written for radius 1.** Each of the six
   `norm_…_alpha_…` / `norm_…_beta_…` lemmas in
   `PtolemysComplexProofOQ02.lean:71–179` computes `‖exp(2αi) − 1‖ = 2 sin α` or similar.
   To generalize to radius $r$, factor $r$ out: `‖r·exp(2αi) − r·1‖ = r · 2 sin α`.
2. **No `chord_length_radius_r` helper** packages the general formula
   `‖r·e^{iθ_z} − r·e^{iθ_w}‖ = 2r·|sin((θ_z−θ_w)/2)|`.
3. **Law of cosines via Ptolemy is not in the project.** The standard textbook proof uses
   dot products (already in Mathlib `EuclideanSpace.norm_sub_sq`). The Ptolemy proof
   constructs a specific cyclic quadrilateral: for a triangle $\triangle ABC$ inscribed
   in its circumcircle (radius $R$), reflect $C$ across the perpendicular bisector of
   $AB$ to get a fourth point $C'$; the quadrilateral $ABCC'$ is cyclic, and Ptolemy +
   law of sines yield the law of cosines.

### Our Goal

**S1 OBSERVE deliverable** (this iteration): map the parent's chord-length lemmas, identify
the radius-$r$ generalization pattern, survey Mathlib for the dot-product law of cosines
(to confirm the Ptolemy-route is genuinely new project content), and propose a concrete
S2 plan.

**Recommended S2 plan** (3 sub-iterations, all in `Proofs/PtolemysComplexProofOQ02OQ02.lean`):

- **S2a (~80 LOC, easy-medium)**: a single helper
  `chord_length_at_radius_r : ‖r·e^{iα} − r·e^{iβ}‖ = 2r · sin(|α−β|/2)`
  derived by factoring $r$ out of the parent's `norm_exp_diff` lemma. This subsumes the
  six radius-1 lemmas and is the structural improvement.
- **S2b (~70 LOC, medium)**: `ptolemy_radius_r` — Ptolemy's equality for four points
  $r·z_1, r·z_2, r·z_3, r·z_4$ on the radius-$r$ circle, deduced from the parent's
  unit-circle Ptolemy by linearity. Factor $r^2$ out of both sides.
- **S2c (~120 LOC, medium-hard)**: `law_of_cosines_via_ptolemy` — using the inscribed
  quadrilateral $ABCC'$ where $C'$ is the reflection of $C$ across the perpendicular
  bisector of $AB$, apply Ptolemy + the law of sines (`Real.law_of_sines` if available;
  else a 30-line helper) to derive $c^2 = a^2 + b^2 - 2ab \cos C$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `ptolemys-complex-proof-oq-02` | **Parent**: sin(α+β) on unit circle from Ptolemy. Direct base for S2a (chord_length_radius_r). | Complex-exponential parametrization; six chord-length lemmas |
| `ptolemys-complex-proof` | Grandparent: Ptolemy's inequality via algebraic identity. | CommRing identity + ℂ triangle inequality |
| `ptolemys-theorem` | Sibling family (real-geometry proofs). | Mathlib `Affine.cospherical` + Euclidean geometry |
| `law-of-cosines` (if exists) | Cross-reference for the eventual S2c statement. | dot-product or area-based proofs |

## Initial Thoughts

### Potential Approaches

See "Our Goal" → "Recommended S2 plan" (S2a/S2b/S2c). Full details in
`sessions/2026-05-12-s1-observe-radius-r-and-law-of-cosines.md`.

### Likely Tools / Lemmas

- The parent's six `norm_…` chord-length lemmas (factor $r$ out).
- `Complex.norm_mul` to handle `‖r · w‖ = r · ‖w‖`.
- `Real.sin_pos_of_pos_of_lt_pi` (chord-positivity, already used by parent).
- `Real.sin_add`, `Real.cos_sub` (for the law of sines / cosines derivation).
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` for trig identities.
- The grandparent's `algebraic_identity` (for the radius-$r$ Ptolemy).

### Expected Difficulty

- **S1 OBSERVE** (this iteration): doc-only ~600 LOC, easy.
- **S2a `chord_length_radius_r`**: ~80 LOC, easy-medium (linear factoring).
- **S2b `ptolemy_radius_r`**: ~70 LOC, medium (scale-invariance of the algebraic identity).
- **S2c `law_of_cosines_via_ptolemy`**: ~120 LOC, medium-hard (geometric construction
  + chord-arc identities).

Total S2 budget: ~270 LOC. Build-safe (no Mathlib gaps; everything builds on
`Complex.exp`, `Real.sin/cos`, `Norm.norm` — all stable since v4.26.0).
