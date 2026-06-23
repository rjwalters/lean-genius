# Problem: Four-Parts Formula (Cotangent Rule) for Spherical Triangles

**Slug**: spherical-law-of-sines-oq-03
**Created**: 2026-05-12
**Status**: Active
**Source**: parent gallery `spherical-law-of-sines` open-question #3

## Problem Statement

### Classical Formal Statement

For a spherical triangle on the unit sphere with unit-vector vertices $A, B, C
\in \mathbb{R}^3$, arc-length sides $a = \mathrm{arcLen}(B, C)$,
$b = \mathrm{arcLen}(A, C)$, $c = \mathrm{arcLen}(A, B)$, and dihedral angles
$\alpha, \beta, \gamma$ at $A, B, C$, the **four-parts formula** (also known
as the **cotangent rule** or **cotangent four-parts formula**) states:

$$
\cot a \cdot \sin b \;=\; \cos b \cdot \cos \gamma \;+\; \sin\gamma \cdot \cot\alpha
$$

equivalently (cleared of cotangents, working when $\sin a, \sin\alpha \ne 0$):

$$
\sin\alpha \cdot \cos a \cdot \sin b
\;=\; \sin a \,\bigl[\sin\alpha \cdot \cos b \cdot \cos\gamma + \cos\alpha \cdot \sin\gamma\bigr]
$$

This connects **four consecutive parts** of the triangle in the cyclic order

$$
(\text{side } a,\ \text{angle } \gamma,\ \text{side } b,\ \text{angle } \alpha),
$$

with the "outer" elements $a, \alpha$ taking the cotangent and the "inner"
elements $b, \gamma$ keeping cos/sin/etc. There are six cyclic permutations
of the formula obtained by relabelling $(A, B, C) \mapsto$ any cyclic
rotation.

### Equivalent Algebraic Form (no cot, single polynomial identity)

Multiplying through by $\sin a \cdot \sin \alpha$ (both nonzero on a
non-degenerate triangle):

$$
\boxed{\;\sin\alpha \cdot \cos a \cdot \sin b
\;=\; \sin a \cdot \sin\alpha \cdot \cos b \cdot \cos\gamma
\;+\; \sin a \cdot \cos\alpha \cdot \sin\gamma\;}
$$

This is preferable as a Lean target because Mathlib's `Real.cot` is a
partial function and is conventionally encoded by hand (see
`AngleTrisectionOQ05OQ04.lean` line 22: "Encoded with `cot = (tan)⁻¹` to
avoid a partial `Real.cot`"). The boxed polynomial-style identity is
universally quantified over all `(A, B, C)` and avoids the partiality
issue entirely.

### Cross-Product Encoding (Parent Framework)

Translated into the parent's `Fin 3 → ℝ` framework with the parent's
existing `dot`, `arcLen`, `tripleProduct`, `projPerp`, and `dihedralAngle`
definitions:

```lean
theorem spherical_cotangent_rule
    (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    -- non-degeneracy hypotheses to ensure sin a, sin α ≠ 0 :
    (hpBC : normSq (projPerp C B) ≠ 0)              -- sin(a) ≠ 0
    (hpBA : normSq (projPerp B A) ≠ 0)              -- sin(c) ≠ 0
    (hpCA : normSq (projPerp C A) ≠ 0) :            -- sin(b) ≠ 0
    Real.sin (dihedralAngle A B C)
      * Real.cos (arcLen B C) * Real.sin (arcLen A C)
    = Real.sin (arcLen B C)
      * Real.sin (dihedralAngle A B C)
      * Real.cos (arcLen A C)
      * Real.cos (dihedralAngle C A B)
    + Real.sin (arcLen B C)
      * Real.cos (dihedralAngle A B C)
      * Real.sin (dihedralAngle C A B)
```

(Here `dihedralAngle A B C = α` is the angle at vertex `A`, and
`dihedralAngle C A B = γ` is the angle at vertex `C`. The parent's
`dihedralAngle_comm_last` shows symmetry in the last two arguments.)

## Why This Matters

1. **Closes the parent's third open question**. The parent gallery
   `spherical-law-of-sines` lists exactly three open questions: the
   spherical excess formula (OQ-01), the dual spherical law of cosines
   (OQ-02), and the four-parts formula (this OQ-03). OQ-01 and OQ-02 are
   already partitioned into separate gallery entries at OBSERVE phase;
   OQ-03 was the last missing sibling.

2. **Pure consequence of existing parent infrastructure + standard
   spherical law of cosines**. Unlike OQ-01 (needs spherical area theory)
   and OQ-02 (needs a duality argument or independent proof), the
   four-parts formula is derivable as a 60–100-line algebraic consequence
   of the parent's `spherical_law_of_sines_sq` plus the standard spherical
   law of cosines (which is already verified at `spherical-law-of-cosines`,
   `Proofs/SphericalLawOfCosines.lean`). This makes it the most tractable
   of the three siblings — `tractability = 7` in the seeker pool versus
   `4–5` for OQ-01 and OQ-02.

3. **Bridges two parent gallery proofs**. Successful formalisation links
   `Proofs/SphericalLawOfSines.lean` and `Proofs/SphericalLawOfCosines.lean`
   directly. Currently each parent is verified standalone; the cotangent
   rule is the natural shared corollary and provides cross-citation
   infrastructure for the spherical-geometry corner of the gallery.

4. **Concrete application: navigation and astronomy**. The cotangent
   rule is the workhorse formula in classical celestial navigation, used
   for computing intercepts from a Sumner line and for converting between
   equatorial and horizontal coordinates given local sidereal time. While
   navigation is a stated educational application of the
   `spherical-law-of-cosines` gallery entry, the cotangent rule is the
   formula one actually uses in tables (Smart 1977, §3.7; Bowditch 2002,
   §22).

## What's Already in the Gallery

* **Parent `spherical-law-of-sines`** (`Proofs/SphericalLawOfSines.lean`,
  323 lines, 0 axioms, 0 sorries, `verified`). Provides:
  - `dot, normSq, IsUnit3, arcLen, tripleProduct, projPerp` (Fin 3 → ℝ
    framework, sec I).
  - `lagrange_identity` (sec I).
  - `projPerp_dot_zero, normSq_projPerp, normSq_projPerp_unit` (sec II).
  - `projPerp_cross_eq, normSq_projPerp_cross` (sec III, key identity).
  - `dihedralAngle, sin_sq_dihedralAngle` (sec IV).
  - `sin_sq_arcLen, spherical_law_of_sines_sq,
    spherical_law_of_sines_all_sq` (sec V).
* **Sibling `spherical-law-of-cosines`**
  (`Proofs/SphericalLawOfCosines.lean`, verified). Provides the standard
  spherical law of cosines `cos(a) = cos(b) cos(c) + sin(b) sin(c) cos(α)`.
* **Sibling `spherical-law-of-cosines-oq-05`** (haversine formula, verified
  via projection-inner-product bridge, PR #17898).
* **Sibling `spherical-law-of-sines-oq-01`** (spherical excess formula,
  OBSERVE phase, no Lean code yet, dir `research/problems/...-oq-01/`).
* **Sibling `spherical-law-of-sines-oq-02`** (dual spherical law of
  cosines, OBSERVE phase, no Lean code yet).
* **Mathlib v4.26.0 status**: provides `Real.sin, Real.cos, Real.tan,
  Real.arccos, Real.sin_arccos`, `Matrix.crossProduct`,
  `Fin.sum_univ_three`, `linear_combination`, `nlinarith`, `field_simp`,
  `ring`, `polyrith`. No top-level `Real.cot`; this OQ-03 will encode
  `cot` as `cos/sin` (or avoid it altogether via the polynomial form).

## Proof Strategy

### Route A (preferred): law-of-cosines + algebra (~60-100 LOC, low risk)

1. **Spherical law of cosines twice**. The parent
   `spherical-law-of-cosines` (or a direct re-derivation if the namespace
   is awkward) gives, for any spherical triangle:
   $$\cos a = \cos b \cos c + \sin b \sin c \cos\alpha$$
   $$\cos b = \cos c \cos a + \sin c \sin a \cos\beta$$

2. **Substitute the second into the first**.
   $$\cos a = \cos b\,[\cos a \cos b + \sin a \sin b \cos\gamma] + \sin b \sin c \cos\alpha$$
   (using the third permutation
   $\cos c = \cos a \cos b + \sin a \sin b \cos\gamma$).
   Algebra:
   $$\cos a (1 - \cos^2 b) = \sin a \sin b \cos b \cos\gamma + \sin b \sin c \cos\alpha$$
   $$\cos a \sin^2 b = \sin b (\sin a \cos b \cos\gamma + \sin c \cos\alpha)$$
   $$\cos a \sin b = \sin a \cos b \cos\gamma + \sin c \cos\alpha \qquad (\star)$$

3. **Law of sines**. From parent's `spherical_law_of_sines_all_sq` plus a
   sign argument (sine is non-negative on $[0, \pi]$):
   $$\frac{\sin c}{\sin\gamma} = \frac{\sin a}{\sin\alpha}, \quad\text{i.e.,}\quad
   \sin\alpha \sin c = \sin a \sin\gamma$$
   Substitute into $(\star)$ multiplied by $\sin\alpha$:
   $$\sin\alpha \cos a \sin b = \sin\alpha \sin a \cos b \cos\gamma + \sin a \sin\gamma \cos\alpha$$
   which is exactly the boxed polynomial identity.

4. **Optional**: divide both sides by $\sin a \cdot \sin\alpha$ to recover
   the classical $\cot a \sin b = \cos b \cos\gamma + \sin\gamma \cot\alpha$.

Estimated LOC: 60-100 (depending on how heavy the import path is for the
sister-proof's law of cosines and how cleanly Mathlib's
`linear_combination`/`field_simp` handles the substitution step).

### Route B (alternative): independent cross-product derivation (~150-200 LOC)

Re-derive in the parent's `Fin 3 → ℝ` framework from scratch, mirroring the
parent's component-by-component `linear_combination` style. Heavier but
self-contained (no dependency on the sibling spherical-law-of-cosines
proof's namespace, which may have a different unit-vector convention).
Reserve for S2-ORIENT review if Route A's namespace bridge proves brittle.

### Honest Calibration

* **Mathematical novelty**: zero. The cotangent rule is in every
  classical textbook (Smart 1977 §3.7; Todhunter 1886 §62; Wikipedia
  "Spherical trigonometry §Cotangent four-part formula"). It is a
  one-line derivation in classical notation.
* **Lean contribution**: packaging the rule into the parent's `Fin 3 → ℝ`
  framework, plus the careful sign argument (sine non-negative) needed to
  pass from the parent's `sq` law-of-sines to the linear form. The
  parent provides `sin_sq_arcLen` but not a linear `sin(arcLen) = ...`
  lemma — that's a 5-10 LOC addition.
* **Closes OQ-03 of the parent's `openQuestions` field** and unlocks
  the cross-reference between `spherical-law-of-sines` and
  `spherical-law-of-cosines` galleries.

## Sanity Checks

* **Right triangle test**: when $\gamma = \pi/2$, formula reduces to
  $\cot a \sin b = \cos b \cdot 0 + 1 \cdot \cot\alpha$, i.e.,
  $\cot a \sin b = \cot\alpha$ which is **Napier's rule** for a
  right-spherical triangle ($\tan a = \tan \alpha \sin b$). ✓
* **Small-triangle limit** (flat geometry): $\cot a \approx 1/a$,
  $\sin b \approx b$, $\cos b \approx 1$, $\cos\gamma$ and $\cot\alpha$
  unchanged. Get $b/a = \cos\gamma + \sin\gamma \cot\alpha$. For the
  Euclidean triangle with $\beta = \pi - \alpha - \gamma$ and law of
  sines $b/a = \sin\beta/\sin\alpha = \sin(\alpha+\gamma)/\sin\alpha
  = \cos\gamma + \cot\alpha\sin\gamma$. ✓
* **Symmetry**: cyclic relabelling $(A,B,C) \to (B,C,A)$ gives
  $\cot b \sin c = \cos c \cos\alpha + \sin\alpha \cot\beta$.
  Five other variants by further relabelling. The proof should produce
  the general statement directly, not case-by-case.

## S1 OBSERVE Deliverable Summary

This S1 OBSERVE PR is **doc-only**: it establishes the problem statement,
surveys parent infrastructure, and sketches Route A's proof. No Lean
files are modified.

Next step (S2 ORIENT, separate PR):
1. Create `proofs/Proofs/SphericalLawOfSinesOQ03.lean`.
2. State `spherical_cotangent_rule` as a `theorem … := by sorry` with
   non-degeneracy hypotheses.
3. Add a helper lemma `sin_arcLen_nonneg` (sine of an arccos value is
   non-negative because arccos returns to $[0, \pi]$).
4. Add a helper lemma `sin_arcLen_eq` extracting
   `sin(arcLen u v) = Real.sqrt (1 - (dot u v)^2)` from the parent's
   `sin_sq_arcLen` plus non-negativity.
5. Stub Route A's two-line-of-cosines substitution as a sorry-ed
   `cotangent_rule_from_cosines` lemma, with the algebra carefully
   spelled out in a docstring.
6. Build verify (no new sorries beyond the strategic one for `S2`).
