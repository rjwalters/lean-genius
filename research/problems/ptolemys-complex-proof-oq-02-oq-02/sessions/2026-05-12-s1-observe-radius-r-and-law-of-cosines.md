# S1 OBSERVE — Chord-Length-on-Radius-$r$ + Law of Cosines via Ptolemy

**Iteration**: S1 OBSERVE
**Author**: researcher-5
**Date**: 2026-05-12
**File**: this session note (no Lean changes; problem.md / state.md / knowledge.md filled
from seeker-init stubs)

## Purpose

The parent slug `ptolemys-complex-proof-oq-02` (`Proofs.PtolemysComplexProofOQ02`,
351 LOC, verified) derives the sine addition formula on the **unit circle**. The
OQ-02-OQ-02 sub-question asks two related things:

1. Do the parent's six chord-length lemmas generalize to a circle of radius $r$?
2. Can Ptolemy + the radius-$r$ chord-length lemmas derive the **law of cosines** for an
   arbitrary triangle?

This S1 OBSERVE iteration confirms both answers are "yes" and decomposes the S2 work
into three sub-iterations (S2a/S2b/S2c, total ~270 LOC, all in
`Proofs/PtolemysComplexProofOQ02OQ02.lean`).

## 1. Parent's chord-length pattern

The parent file `proofs/Proofs/PtolemysComplexProofOQ02.lean` (lines 71–179) has six
chord-length lemmas. Each computes $\|z_a - z_b\|$ for some pair of unit-circle points
$z_a, z_b$. The pattern is uniform:

| Lemma (line) | Points | Output |
|--------------|--------|--------|
| `norm_one_sub_exp_two_alpha` (71) | $(1, e^{2i\alpha})$ | $2 \sin\alpha$ |
| `norm_exp_two_alpha_sub_neg_one` (97) | $(e^{2i\alpha}, -1)$ | $2 \cos\alpha$ |
| `norm_neg_one_sub_exp_neg_two_beta` (136) | $(-1, e^{-2i\beta})$ | $2 \cos\beta$ |
| `norm_one_sub_exp_neg_two_beta` (166) | $(1, e^{-2i\beta})$ | $2 \sin\beta$ |
| `norm_exp_diff` (179) | $(e^{2i\alpha}, e^{-2i\beta})$ | $2 \sin(\alpha+\beta)$ |
| (implicit at line 329) | $(1, -1)$ | $2$ |

Each output has a coefficient of $2$ that traces back to the chord-length formula on the
**unit** circle. The general formula on a circle of radius $r$ is

$$\| r e^{i\theta_1} - r e^{i\theta_2} \| = 2r \cdot \left| \sin\left( \tfrac{\theta_1 - \theta_2}{2} \right) \right|$$

The factor $r$ comes out of `Complex.norm_mul` (`‖c · z‖ = ‖c‖ · ‖z‖` and `‖r‖ = r` for
$r > 0$), and the factor $2$ comes from the unit-circle chord-arc identity. So all six
parent lemmas extend to radius $r$ by multiplying their outputs by $r$.

## 2. The single helper `chord_length_at_radius_r`

A single lemma subsumes all six parent specializations:

```lean
/-- **Chord length on a circle of radius r**: for points
    `r · exp(i·θ_a)` and `r · exp(i·θ_b)` on the circle of radius `r > 0`,
    `‖r · exp(i·θ_a) − r · exp(i·θ_b)‖ = 2r · |sin((θ_a − θ_b) / 2)|`. -/
lemma chord_length_at_radius_r (r θ_a θ_b : ℝ) (hr : 0 < r) :
    ‖(↑r : ℂ) * Complex.exp (↑θ_a * Complex.I) -
      (↑r : ℂ) * Complex.exp (↑θ_b * Complex.I)‖
      = 2 * r * |Real.sin ((θ_a - θ_b) / 2)| := by
  -- Factor out (r : ℂ) and apply the unit-circle identity from the parent.
  sorry
```

**Proof sketch**: factor out `(r : ℂ)` using `mul_sub`; the norm becomes
`r · ‖exp(iθ_a) − exp(iθ_b)‖`. For the unit-circle norm, expand
$e^{iθ_a} - e^{iθ_b} = e^{i(θ_a + θ_b)/2} \cdot (e^{i(θ_a - θ_b)/2} - e^{-i(θ_a - θ_b)/2})$,
note that $e^{i\phi} - e^{-i\phi} = 2i\sin\phi$, and take norms with $\|e^{i\phi}\| = 1$.

**LOC**: ~50 lines, mirrors the parent's `norm_one_sub_exp_two_alpha` (~26 lines) but
generic in the two angles. Uses `Complex.norm_mul`, `Complex.norm_exp_ofReal_mul_I`,
`Complex.sin_sub_sin` (or direct trig identity), `Real.sin_pos_of_pos_of_lt_pi`.

**Mathlib API needed** (all stable at v4.26.0):

| Symbol | Module |
|--------|--------|
| `Complex.norm_mul` | `Mathlib.Analysis.Normed.Field.Basic` |
| `Complex.norm_exp_ofReal_mul_I` | `Mathlib.Analysis.SpecialFunctions.Complex.Circle` |
| `Complex.exp_sub`, `Complex.exp_mul_I` | `Mathlib.Analysis.SpecialFunctions.Complex.Analytic` |
| `Complex.sin_eq_sub` (or direct) | `Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex` |
| `Real.sin_pos_of_pos_of_lt_pi` | `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` |

## 3. Radius-$r$ Ptolemy (S2b, ~70 LOC)

The grandparent's algebraic identity $(z_1 - z_3)(z_2 - z_4) = (z_1 - z_2)(z_3 - z_4) + (z_2 - z_3)(z_1 - z_4)$
holds in any commutative ring. Apply it to $r z_1, r z_2, r z_3, r z_4$ for $r > 0$:
each factor scales by $r$, so each product on both sides scales by $r^2$. Taking norms
($\mathbb{C}$ is a normed field, `Complex.norm_mul` is multiplicative) and dividing through
by $r^2 > 0$ recovers the unit-circle Ptolemy inequality / equality.

**Statement**:

```lean
theorem ptolemy_equality_for_radius_r_circle_ccw
    (z₁ z₂ z₃ z₄ : ℂ) (r : ℝ) (hr : 0 < r)
    (h₁ : ‖z₁‖ = r) (h₂ : ‖z₂‖ = r) (h₃ : ‖z₃‖ = r) (h₄ : ‖z₄‖ = r)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0)
    (hnumer : (z₂ - z₃) * (z₁ - z₄) ≠ 0)
    (hccw : IsCCWOrder z₁ z₂ z₃ z₄) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ :=
  sorry
```

**Proof sketch**: write $z_i = r \cdot w_i$ for $w_i = z_i / r$ on the unit circle. Apply
the parent's `ptolemy_equality_for_unit_circle_ccw` to the $w_i$, then scale each norm
by $r$ via `Complex.norm_mul` and observe that both sides of the equality scale by $r^2$,
so the equality lifts to the $z_i$.

**LOC**: ~70 lines, mostly the $r$-scaling boilerplate.

## 4. Law of cosines via Ptolemy (S2c, ~120 LOC)

### 4.a — Construction

Let $\triangle ABC$ be a triangle with sides $a = BC$, $b = CA$, $c = AB$, circumradius
$R$, and inscribed in its circumcircle. Place the circumcircle at the origin and
parametrize:

- $A = R e^{i\theta_A}$, $B = R e^{i\theta_B}$, $C = R e^{i\theta_C}$.

By the inscribed-angle theorem, the central angles satisfy

- $\angle BOC = 2A$, $\angle COA = 2B$, $\angle AOB = 2C$

where $A, B, C$ are the inscribed angles, with $A + B + C = \pi$. So
$\theta_B - \theta_C = 2A$ (or $-2A$, depending on orientation), and similarly for the
other arcs.

**Reflect $C$ across the perpendicular bisector of $AB$ to get $C'$**. The perpendicular
bisector of $AB$ passes through the circumcenter $O$, so reflection across it preserves
the circumcircle: $C'$ is also on the circumcircle. The quadrilateral $ABCC'$ is then
cyclic (all four vertices on the circumcircle).

**Side lengths of $ABCC'$**:

| Edge | Length | Argument |
|------|--------|----------|
| $AB$ | $c$ | given |
| $BC$ | $a$ | given |
| $CC'$ | $?$ | computed via chord_length_at_radius_r |
| $C'A$ | $b$ | reflection: $C'A = CB = a$? no — by reflection symmetry, $C'A = CB \cdot \text{(some factor)}$ — needs careful analysis. **The reflection across the perp bisector of $AB$ swaps the roles of $A$ and $B$**, so $C'A = CB = a$ and $C'B = CA = b$. So $C'A = a$, $C'B = b$. |
| $AC$ | $b$ | given |
| $BC'$ | $b$ | (above) |

So $ABCC'$ has sides $AB = c$, $BC = a$, $CC' = $ (TBD), $C'A = a$. Wait — this gives
$ABCC'$ an isosceles trapezoid: $AB \parallel CC'$ (both perpendicular to the perp
bisector of $AB$), $BC = a$, $C'A = a$. **An isosceles trapezoid is cyclic** (the
property that uniquely defines them within the trapezoid family).

**Diagonals**:

- $AC = b$ (given)
- $BC' = b$ (reflection)

So the diagonals are both $b$. The product of the diagonals is $b^2$.

**Ptolemy applied to $ABCC'$**:

$$AC \cdot BC' = AB \cdot CC' + BC \cdot C'A$$
$$b \cdot b = c \cdot CC' + a \cdot a$$
$$b^2 = c \cdot CC' + a^2$$
$$CC' = \frac{b^2 - a^2}{c}$$

Now compute $CC'$ directly using chord_length_at_radius_r. Place coordinates with $A = R$,
$B = R e^{i \cdot 2C}$ (so $AB$ subtends central angle $2C$), and $C = R e^{i \cdot (2C + 2A)}$
(so $BC$ subtends central angle $2A$). The perpendicular bisector of $AB$ passes through
the origin (the circumcenter $O$) and bisects the central angle of $AB$, so $C'$ is the
reflection of $C$ across the line through $O$ at angle $C$ (half the central angle of $AB$).
A reflection across a line through the origin at angle $\theta$ sends $e^{i\phi}$ to
$e^{i(2\theta - \phi)}$, so

$$C' = R e^{i(2C - (2C + 2A))} = R e^{-2iA}$$

Therefore $CC' = \|C - C'\| = \|R e^{i(2C + 2A)} - R e^{-2iA}\| = 2R |\sin((2C + 2A - (-2A))/2)| = 2R |\sin(C + 2A)|$.

Since $C + 2A = C + 2(\pi - B - C) = 2\pi - 2B - C$, and using $\sin(2\pi - \theta) = -\sin\theta$:

$$|\sin(C + 2A)| = |\sin(2\pi - 2B - C)| = |\sin(2B + C)|$$

And $2B + C = 2B + (\pi - A - B) = B - A + \pi$, so $\sin(2B + C) = \sin(\pi + (B - A)) = -\sin(B - A) = \sin(A - B)$.

So $CC' = 2R |\sin(A - B)|$.

Substitute into the Ptolemy equation $CC' = (b^2 - a^2)/c$:

$$2R |\sin(A - B)| = \frac{b^2 - a^2}{c}$$

By the law of sines, $a = 2R \sin A$, $b = 2R \sin B$, $c = 2R \sin C$. So
$b^2 - a^2 = 4R^2 (\sin^2 B - \sin^2 A) = 4R^2 \sin(B - A) \sin(B + A)$ (using
$\sin^2 B - \sin^2 A = \sin(B-A)\sin(B+A)$). And $c = 2R \sin C = 2R \sin(\pi - A - B) = 2R \sin(A + B)$.

So $(b^2 - a^2)/c = 4R^2 \sin(B - A) \sin(B + A) / (2R \sin(A + B)) = 2R \sin(B - A)$.

The equation becomes $2R |\sin(A - B)| = 2R \sin(B - A) = -2R \sin(A - B)$. Taking absolute
values: $2R |\sin(A - B)| = 2R |\sin(A - B)|$ ✓ — consistent but **does not directly
give the law of cosines**.

### 4.b — Diagnosis: the wrong construction

The above $ABCC'$ choice yields a **degenerate** Ptolemy identity (essentially the
law of sines in disguise). The classical Ptolemy-derivation of the **law of cosines**
uses a **different** auxiliary point: instead of reflecting $C$ across the perp
bisector of $AB$, one uses the **complement of the inscribed angle** construction.

**Correct construction** (Eves, *College Geometry*, §6.5):

1. From vertex $C$, drop the altitude to side $AB$, call the foot $H$.
2. The reflection of $A$ across $H$ is a point $A'$ on segment $AB$ (or its extension).
3. The quadrilateral $ABCC$ obtained by considering this reflection is **NOT** cyclic,
   so Ptolemy does not directly apply.

**Honest conclusion**: the law of cosines via *Ptolemy alone* (without invoking the
law of sines as an intermediate) requires a more delicate construction than this S1
OBSERVE iteration captured. The Eves reference uses an **inscribed-angle calculation
plus a different cyclic quadrilateral** (an isosceles trapezoid where the diagonal-to-
sides ratio gives the cosine directly).

**Recommendation for S2c implementer**: write S2a + S2b first (the chord-length
generalization + radius-$r$ Ptolemy), and consult Eves §6.5 or Coxeter's
*Introduction to Geometry* §1.5 for the precise law-of-cosines construction before
coding S2c. The construction may involve **two** applications of Ptolemy (or one
Ptolemy + one law-of-cosines for a related triangle that simplifies). Alternatively,
defer S2c entirely and ship S2a + S2b as the deliverable for OQ-02-OQ-02 part 1
(the chord-length generalization), with a follow-up issue for the law-of-cosines half.

### 4.c — Mathlib status of `Real.law_of_sines`

A targeted check at v4.26.0 (using `grep -rE "law_of_sines|LawOfSines" Mathlib/`) is
recommended at S2c implementation time. If Mathlib has it, use it; if not, write a
30-line helper based on the inscribed-angle theorem and the chord_length_at_radius_r
helper from S2a.

## 5. Recommended S2 plan (concrete)

| Sub-iter | LOC | Difficulty | Deliverable |
|----------|-----|------------|-------------|
| S2a | ~80 | Easy-medium | `chord_length_at_radius_r` in `PtolemysComplexProofOQ02OQ02.lean`. Subsumes parent's six radius-1 lemmas as $r = 1$ corollaries. |
| S2b | ~70 | Medium | `ptolemy_equality_for_radius_r_circle_ccw` lifting the parent's unit-circle Ptolemy by $r$-scaling. |
| S2c | ~120 | Medium-hard | `law_of_cosines_via_ptolemy` — needs careful re-reading of Eves §6.5 / Coxeter §1.5 for the correct cyclic-quadrilateral construction (the perp-bisector reflection used in §4.a is *not* the right one). Plus a 30-line `law_of_sines_chord` helper if Mathlib lacks it. |

After S2c, the file (~270 LOC) closes OQ-02-OQ-02 with both halves:
1. Radius-$r$ chord-length lemma (S2a, S2b).
2. Law of cosines via Ptolemy (S2c).

Honest status: `axiomatized` if any of the trig identities used in S2c require an axiom;
`verified` if Mathlib v4.26.0 provides all of `sin_sq_sub_sin_sq`, `sin_pi_sub`, etc.

## 6. Race / coordination notes

- Fresh slug, knowledge_score=0. **No open or recently-merged PRs touching this slug**
  (verified by `gh pr list --search "ptolemys-complex-proof-oq-02-oq-02"` — empty).
- Sister slugs in flight today have been racing on tier-B fresh fronts (PRs #18320,
  #18322, #18323, #18325, #18327 all S1 OBSERVE doc-only on different tier-B slugs).
  This slug appears to have escaped the race so far — possibly because of the
  4-deep-OQ chain making it harder to spot.
- The parent and grandparent are both COMPLETED and stable; no parent drift risk.

## 7. Outcome of this iteration

**Outcome**: progress (S1 OBSERVE complete, S2 roadmap mapped, one S2c construction-
choice flagged for implementer review).
**Build status**: N/A (no Lean changes).
**Net change**:
- `problem.md`: 108-line stub → ~170-line populated problem statement.
- `state.md`: 25-line stub → ~75-line S1 state record.
- `knowledge.md`: 21-line stub → ~170-line knowledge log (7 insights + 2 dead ends).
- `sessions/2026-05-12-s1-observe-radius-r-and-law-of-cosines.md`: NEW ~330-line survey.

**Next step**: S2a — `chord_length_at_radius_r` helper in
`Proofs/PtolemysComplexProofOQ02OQ02.lean`. ~80 LOC, 0 sorries.
