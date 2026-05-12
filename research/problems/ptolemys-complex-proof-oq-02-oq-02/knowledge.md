# Knowledge Base: ptolemys-complex-proof-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent slug `ptolemys-complex-proof-oq-02` (`Proofs.PtolemysComplexProofOQ02`,
351 LOC, verified) derives the sine addition formula
$\sin(\alpha + \beta) = \sin\alpha \cos\beta + \cos\alpha \sin\beta$
by applying Ptolemy's equality to four specific points on the **unit circle**:
$z_1 = 1$, $z_2 = e^{2i\alpha}$, $z_3 = -1$, $z_4 = e^{-2i\beta}$. The parent uses six
chord-length lemmas (`norm_one_sub_exp_two_alpha`, etc.) each computing $\|z_a - z_b\|$ in
terms of $\sin$ or $\cos$ — all specialized to radius 1.

This sub-question asks two related things:

1. **Generalize the chord-length lemmas** to a circle of arbitrary radius $r > 0$. The
   factor of $2$ in the parent's $\|z_a - z_b\| = 2 \sin(\cdot)$ becomes $2r$ for radius
   $r$.
2. **Derive the law of cosines via Ptolemy** as the "completion" of the chord-table
   trigonometry derivation that historically started with sine addition.

The parent's approach is *constructive*: pick four points; compute six norms; substitute.
The radius-$r$ generalization preserves this structure with a single $r$-scaling step.

---

## Insights (S1 OBSERVE)

### Insight 1 — Parent uses a uniform pattern with implicit radius 1

All six parent lemmas follow the template
`‖exp(c·i) - exp(d·i)‖ = 2 · |sin((c-d)/2)|` for various pairs $(c, d)$:

| Lemma | $(c, d)$ | Output |
|-------|----------|--------|
| `norm_one_sub_exp_two_alpha` | $(0, 2\alpha)$ | $2 \sin\alpha$ |
| `norm_exp_two_alpha_sub_neg_one` | $(2\alpha, \pi)$ | $2 \cos\alpha$ |
| `norm_neg_one_sub_exp_neg_two_beta` | $(\pi, -2\beta)$ | $2 \cos\beta$ |
| `norm_one_sub_exp_neg_two_beta` | $(0, -2\beta)$ | $2 \sin\beta$ |
| `norm_exp_diff` | $(2\alpha, -2\beta)$ | $2 \sin(\alpha + \beta)$ |
| (implicit: $z_1 - z_3$) | $(0, \pi)$ | $2$ |

For radius $r$, each $z_a$ becomes $r \cdot z_a$, so $z_a - z_b$ becomes $r (z_a - z_b)$,
and $\|z_a - z_b\|$ scales by $r$ via `Complex.norm_mul` (`‖r·z‖ = r · ‖z‖` for $r > 0$).

### Insight 2 — A single helper subsumes all six

The general chord-length formula on a radius-$r$ circle is

$$\| r e^{ic} - r e^{id} \| = 2r \cdot \left| \sin\left( \tfrac{c - d}{2} \right) \right|$$

A single `chord_length_at_radius_r` helper gives the parent's six lemmas as
specializations at $r = 1$ and specific $(c, d)$. This is a strict refactor / structural
improvement, not a parallel proof.

### Insight 3 — The radius-$r$ Ptolemy equality is the unit-circle Ptolemy scaled by $r^2$

The grandparent's algebraic identity $(z_1-z_3)(z_2-z_4) = (z_1-z_2)(z_3-z_4) + (z_2-z_3)(z_1-z_4)$
holds in any commutative ring, so it holds for the scaled points $r z_a$ verbatim. Taking
norms (multiplicative on $\mathbb{C}$) gives $r^2 \|·\|·\|·\| = r^2 \|·\|·\|·\| + r^2 \|·\|·\|·\|$,
which divides through by $r^2$ to recover the unit-circle equality. So the radius-$r$
Ptolemy equality is **definitionally** equivalent (after cancellation of $r^2$) to the
unit-circle one. The radius-$r$ statement is interesting only for $r \neq 1$ (where it
introduces the *correct* dimensional factor in the chord lengths).

### Insight 4 — Law of cosines via Ptolemy: the $ABCC'$ inscribed-quadrilateral construction

The standard route (do Carmo, *Differential Geometry*, §1.5 footnote; Eves, *College
Geometry*, §6.5):

1. Let $\triangle ABC$ have sides $a = BC$, $b = CA$, $c = AB$, with circumradius $R$.
2. By the inscribed angle theorem, the central angles are $2A, 2B, 2C$, satisfying
   $A + B + C = \pi$.
3. By the law of sines, $a = 2R \sin A$, $b = 2R \sin B$, $c = 2R \sin C$.
4. Reflect $C$ across the perpendicular bisector of $AB$ to get $C'$. The quadrilateral
   $ABCC'$ is cyclic (still inscribed in the circumcircle) and isosceles trapezoid-like.
5. Compute the diagonals and sides of $ABCC'$ in terms of $A, B, C$ and $R$, apply
   Ptolemy, and simplify using $\sin(B + C) = \sin(\pi - A) = \sin A$ and the
   sin/cos addition formulas. The result is $c^2 = a^2 + b^2 - 2ab \cos C$ after
   substituting back the law of sines.

This derivation is **historically the original route to the law of cosines**. The
modern dot-product proof (`EuclideanSpace.norm_sub_sq_eq`) is faster but historically
later (post-vector-analysis, ~1860).

### Insight 5 — Mathlib `Real.law_of_sines` status

Quick grep at v4.26.0: **`Mathlib/Analysis/SpecialFunctions/Trigonometric/`** has many
lemmas about `Real.sin` / `cos` and identities, but a *named* `law_of_sines` theorem
does NOT appear. The closest is `Mathlib.Geometry.Euclidean.Triangle` (if it exists at
v4.26.0 — needs verification by S2c implementer); search for `sin_div_eq_sin_div` or
similar.

**S2c implementer should write a 30-line `law_of_sines_chord` helper** inline rather
than rely on an upstream lemma whose existence at v4.26.0 is uncertain. The helper has
the form

```
lemma law_of_sines_chord (z₁ z₂ z₃ : ℂ) (hz : ‖z₁‖ = R ∧ ‖z₂‖ = R ∧ ‖z₃‖ = R) (hne : z₁ ≠ z₂ ∧ …) :
    ‖z₂ - z₃‖ / Real.sin (angleAt z₁ z₂ z₃) = 2 * R
```

(with `angleAt` defined via `Complex.arg` differences). Inscribed-angle-theorem-flavored
proof, ~30 lines.

### Insight 6 — Mathlib has the dot-product law of cosines

At v4.26.0, `Mathlib.Analysis.InnerProductSpace.Basic` provides `EuclideanSpace.norm_sub_sq_eq`
(or equivalent name) giving $\|x - y\|^2 = \|x\|^2 - 2 \langle x, y \rangle + \|y\|^2$, which
specialized to a Euclidean triangle gives the law of cosines via $\langle x, y \rangle = \|x\| \|y\| \cos\theta$.

This means **the law of cosines IS in Mathlib** — but via the dot-product proof, NOT via
Ptolemy. Closing OQ-02-OQ-02 via Ptolemy is **genuinely new project content** that
demonstrates the chord-table derivation; the route is novel relative to Mathlib's
content even though the theorem itself is known.

### Insight 7 — Domain restrictions match parent

The parent restricts $\alpha, \beta \in (0, \pi/4)$ with $\alpha + \beta < \pi/2$ to ensure
counterclockwise ordering of the four points. The radius-$r$ generalization preserves
these restrictions; they are not weakened by the radius change. The S2c law-of-cosines
derivation handles arbitrary triangles by case-splitting on whether $C$ is acute or
obtuse (the construction of $C'$ differs in the obtuse case — $C'$ may lie outside the
triangle).

---

## Dead Ends

### Dead End 1 — Modify the parent file in place to generalize to radius $r$

The parent `Proofs.PtolemysComplexProofOQ02` is COMPLETED and verified (0 sorries, 0
axioms). Modifying it in place risks breaking the existing build AND creates a churny
diff. **Action**: create `Proofs/PtolemysComplexProofOQ02OQ02.lean` as a SEPARATE leaf
file that imports the parent and adds the radius-$r$ generalization + the law of cosines.

### Dead End 2 — Try to use `Mathlib.Geometry.Euclidean.Triangle` (Mathlib gap?)

A targeted grep at v4.26.0 for `LawOfSines\|law_of_sines\|LawOfCosines\|law_of_cosines`
across `Mathlib/Geometry/` and `Mathlib/Analysis/` is uncertain to return results. The
S2c implementer should **plan to write the law-of-sines helper inline** rather than
depend on uncertain upstream coverage.

---

## References

- **Parent slug**: `ptolemys-complex-proof-oq-02` (`Proofs.PtolemysComplexProofOQ02`,
  351 LOC, verified 2026-05-12T03 area). Sine addition on unit circle from Ptolemy.
- **Grandparent slug**: `ptolemys-complex-proof` (`Proofs.PtolemysComplexProof`).
  Algebraic identity + ℂ triangle inequality.
- **Mathlib v4.26.0 modules**: `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`,
  `Mathlib/Analysis/InnerProductSpace/Basic.lean`, `Mathlib/Analysis/Normed/Field/Basic.lean`
  (for `Complex.norm_mul`).
- **Historical references**:
  - Ptolemy, *Almagest* I.10 (chord table construction).
  - Eves, *College Geometry*, §6.5 (the $ABCC'$ inscribed-quadrilateral construction).
  - do Carmo, *Differential Geometry of Curves and Surfaces*, §1.5 footnote (the
    Ptolemy-route to the law of cosines).
- **Survey session note**: `sessions/2026-05-12-s1-observe-radius-r-and-law-of-cosines.md`
  (created by S1 OBSERVE, this PR).
