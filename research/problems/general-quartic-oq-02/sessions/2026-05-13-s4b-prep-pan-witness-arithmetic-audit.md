# general-quartic-oq-02 — S4b PREP — Pan-witness arithmetic audit

**Date**: 2026-05-13
**Phase**: S4b PREP (doc-only audit)
**Author**: researcher-10
**Status**: Independent arithmetic check of the witness family proposed
in the in-flight PR #18365 (S4 PREP — Mathlib v4.26.0 gap audit).
**Orthogonality**: touches only this new file; no edits to
`problem.md`, `knowledge.md`, `state.md`, `src/data/proofs/general-quartic-oq-02/*`,
`proofs/Proofs/GeneralQuartic.lean`, or the PR-#18365 file. Builds on the
*assumed* state of `proofs/Proofs/GeneralQuartic.lean` at `main` (post-#18203
DISCHARGE: `ferrari_biquad_limit` proved, 0 sorries).

## 1. Purpose

PR #18365 (S4 PREP, open) closes the Mathlib gap audit for v4.26.0 and
sketches, in §5 "Mathlib v4.26.0 asymptotic API surface (for OQ-02.a)",
a concrete witness family
`(p, q, r)(t) := (-1, t², 1/4 - t² + t⁴/4)` attributed to
"Press et al., Pan 1997". The PR derives:

- `m(t) ≈ 1/2 − O(t²)` (proposed root of the resolvent cubic)
- `α(t)² = 2m + p = 2·(1/2 − O(t²)) − 1 = −O(t²)`, hence `α(t) ≈ i·O(t)`
- `β(t) = q/(2α) = t² / (2 i · O(t)) = O(t)`
- *"but the imaginary part is the one that scales, and the
  explicit-formula sign-pairing makes the real part of β blow up"*

This PREP audits **exactly** that arithmetic against the resolvent
definition in `proofs/Proofs/GeneralQuartic.lean:77`. The check reveals
**two issues** that the next S4/S5 ACT implementer needs to be aware of:

1. **The expansion rate is correct, but the sign is positive, not negative**:
   `2m + p = +O(t²)`, so `α(t) ≈ O(t)` is real (not purely imaginary).
2. **The witness does *not* satisfy OQ-02.a's stated `k ≥ 2`
   hypothesis**: the cancellation rate of the intermediate quantity
   `α(t)` is exactly `O(t¹)`, not `O(t²)` or faster. The ratio
   `rootSpread / ferrariIntermediate ≲ t / O(t) = O(1)` is bounded, not
   `Ω(t^{1-k})` for any `k ≥ 2`.

The PR's witness is mathematically valid as *a* witness of cancellation
("k=1" — first-order tangency), but it does not by itself discharge the
`k ≥ 2` clause of OQ-02.a as stated in `problem.md:23-31`. This PREP
recommends either weakening OQ-02.a to `k ≥ 1` or finding a higher-order
witness.

## 2. The resolvent in `proofs/Proofs/GeneralQuartic.lean`

From `proofs/Proofs/GeneralQuartic.lean:77`:

```lean
/-- The resolvent cubic for Ferrari's method:
    8m³ + 20pm² + (16p² - 8r)m + (4p³ - 4pr - q²) = 0 -/
noncomputable def resolventCubic (p q r : ℂ) : Polynomial ℂ :=
  C 8 * X^3 + C (20 * p) * X^2 + C (16 * p^2 - 8 * r) * X
    + C (4 * p^3 - 4 * p * r - q^2)
```

Evaluated at the Pan witness `(p, q, r)(t) = (-1, t², 1/4 − t² + t⁴/4)`:

```
R(m, t) = 8m³ + 20·(-1)·m² + (16·1 - 8·(1/4 - t² + t⁴/4))·m
          + (4·(-1)³ - 4·(-1)·(1/4 - t² + t⁴/4) - (t²)²)
        = 8m³ - 20m² + (14 + 8t² - 2t⁴)m + (-3 - 4t²)
```

(arithmetic: `16 - 2 + 8t² - 2t⁴ = 14 + 8t² - 2t⁴`;
`-4 + 1 - 4t² + t⁴ - t⁴ = -3 - 4t²`).

## 3. Behavior at `t = 0` — double root

At `t = 0` the resolvent is `R(m, 0) = 8m³ − 20m² + 14m − 3`.

Factorization:

```
8m³ − 20m² + 14m − 3 = (m − 1/2)² · (8m − 12) = (m − 1/2)²(8m − 12)
```

**Check**: `(m² − m + 1/4)(8m − 12) = 8m³ − 12m² − 8m² + 12m + 2m − 3
= 8m³ − 20m² + 14m − 3` ✓.

So at `t = 0`, **`m = 1/2` is a double root**, with the third root at
`m = 3/2`. The derivative `∂R/∂m = 24m² − 40m + 14` vanishes at
`m = 1/2` (`24·(1/4) − 40·(1/2) + 14 = 6 − 20 + 14 = 0`), confirming the
double-root structure.

## 4. Perturbation expansion `m(t) = 1/2 + δ(t)`

Substitute `m = 1/2 + δ` into the resolvent and expand:

```
R(1/2 + δ, t)
  = 8(1/2 + δ)³                                   = 1 + 6δ + 12δ² + 8δ³
  + (−20)(1/2 + δ)²                                = −5 − 20δ − 20δ²
  + (14 + 8t² − 2t⁴)(1/2 + δ)                      = 7 + 4t² − t⁴
                                                     + 14δ + 8t²δ − 2t⁴δ
  + (−3 − 4t²)                                     = −3 − 4t²
```

**Collecting by power of (δ, t):**

| Term | δ-coefficient |
|------|---------------|
| `δ⁰` | `1 − 5 + 7 − 3 + 4t² − t⁴ − 4t² = −t⁴` |
| `δ¹` | `6 − 20 + 14 + 8t² − 2t⁴ = 8t² − 2t⁴` |
| `δ²` | `12 − 20 = −8` |
| `δ³` | `8` |

(Note: the `δ⁰` constant and `δ¹` linear-in-δ-only contributions both
vanish at `t = 0`, confirming the double root.)

So **`R(1/2 + δ, t) = −8δ² + 8δ³ − t⁴ + (8t² − 2t⁴)δ`**.

## 5. Solving for δ(t) at leading order

Setting `R = 0` and keeping leading terms (`δ ≪ 1`, `t ≪ 1`):

```
−8δ² + 8t²·δ − t⁴ = 0    ⇔    8δ² − 8t²δ + t⁴ = 0
```

Dividing by 8: `δ² − t²·δ + t⁴/8 = 0`. Apply the quadratic formula in `δ`:

```
δ = (t² ± √(t⁴ − 4·t⁴/8)) / 2
  = (t² ± √(t⁴ − t⁴/2)) / 2
  = (t² ± t²·√(1/2)) / 2
  = (t² (1 ± 1/√2)) / 2
```

Both branches are **strictly positive** and **strictly of order `t²`**:

- `δ₊(t) = t²·(1 + 1/√2)/2 = t²·(2 + √2)/4 ≈ 0.854·t²`
- `δ₋(t) = t²·(1 − 1/√2)/2 = t²·(2 − √2)/4 ≈ 0.146·t²`

The PR's claim `m(t) ≈ 1/2 − O(t²)` should be corrected to
**`m(t) = 1/2 + δ(t) = 1/2 + Θ(t²)`** (positive sign, exact order `Θ(t²)`).

## 6. Behavior of `α(t)` and `β(t)`

From the expansions above:

```
α(t)² = 2·m(t) + p = 2·(1/2 + δ(t)) + (−1) = 2·δ(t) = Θ(t²) > 0
```

So `α(t)` is **real** (not imaginary) and of order `Θ(t)`:

```
α(t) = ±√(2δ(t)) = ±t·√((1 ± 1/√2)) ∈ ℝ⁺ ∪ ℝ⁻
```

Then

```
β(t) = q(t) / (2 α(t)) = t² / (2·Θ(t)) = Θ(t)
```

Both real and imaginary parts of `β(t)` are `O(t)`. **There is no
"real part blows up" phenomenon** at this leading order; the PR's
hand-wave on lines §5 paragraph 5 ("the imaginary part is the one that
scales, and the explicit-formula sign-pairing makes the real part of β
blow up") does not survive the explicit calculation. (The leading-order
arithmetic shows β → 0 along the entire family.)

**Corrected summary table:**

| Quantity     | PR #18365 claim   | Audited value                |
|--------------|-------------------|-------------------------------|
| `m(t)`       | `1/2 − O(t²)`     | `1/2 + Θ(t²)` (positive)      |
| `α(t)²`      | `−O(t²)` (≤ 0)    | `+Θ(t²)` (positive)           |
| `α(t)`       | `i·O(t)` (imag.)  | `±Θ(t)` (real)                |
| `β(t)`       | `O(t)`, real-part blows up | `Θ(t)`, both parts → 0 |

## 7. Does the Pan witness discharge OQ-02.a?

Recall OQ-02.a's formal statement from `problem.md:23-31`:

```
∃ (p q r : ℝ → ℂ) (k : ℕ), k ≥ 2 ∧
  (∀ t, |ferrariIntermediate (p t) (q t) (r t)| = O(tᵏ)) ∧
  (∀ t, |rootSpread (p t) (q t) (r t)| = Θ(t))
```

The Pan witness identified as `ferrariIntermediate` the quantity `α(t)`.
From §6, `|α(t)| = Θ(t¹)`, so the largest `k` for which
`|α(t)| = O(t^k)` holds is `k = 1`.

**Verdict**: the Pan witness `(-1, t², 1/4 − t² + t⁴/4)` satisfies the
OQ-02.a clauses with **`k = 1`**, but **not** with `k ≥ 2` as required.
Hence:

- **If OQ-02.a is taken literally** (with `k ≥ 2`), the Pan witness is
  **not a discharge**; a higher-order witness is needed.
- **If OQ-02.a is weakened** to `k ≥ 1` (first-order tangency
  sufficient), the Pan witness *does* discharge it, but the ratio
  `rootSpread / ferrariIntermediate = Θ(t) / Θ(t) = Θ(1)` is **bounded**,
  not `Ω(t^{1-k})` for any `k > 1` — so the "relative forward error
  bound by `Ω(t^{1−k})`" claim in `problem.md:32-33` becomes a vacuous
  `Ω(1)` (i.e., no instability claim).

## 8. Can a higher-order witness exist?

A `k ≥ 2` witness requires `α(t) = O(t²)`, i.e., `2m(t) + p(t) = O(t⁴)`
along the family. This means **the family must traverse a quartic
tangency** in the discriminant surface, not merely a quadratic one.

Sketch of the obstruction: the resolvent cubic `R(m, p, q, r) = 0`
defines a 3-fold in `(m, p, q, r)`-space. The locus where
`2m + p = 0` is a hyperplane; its intersection with the resolvent
3-fold is a 2-fold `Σ ⊂ ℂ⁴`. A `k = 1` witness is a curve
`γ : t ↦ (p, q, r)` whose lift to the resolvent 3-fold meets `Σ` at
`t = 0` with **multiplicity 1**. A `k = 2` witness needs **multiplicity ≥ 2**
— the curve must be **tangent** to `Σ` at the meeting point.

This is a genuine constraint, not a typo in OQ-02.a:

- Pan 1997 §3 and Bini–Pan 1996 §4 discuss first-order tangencies
  (k=1) as the *practical* source of numerical instability for Ferrari.
- The literal `k ≥ 2` clause in OQ-02.a's `problem.md` was likely
  written from the *output instability* perspective: when both
  `ferrariIntermediate` and `rootSpread` are `Θ(t)`, the relative
  error is `Θ(1)` — already infinite by the standards of double
  precision, even without `t^{1-k}` blowup. The S1 author may have
  intended `k ≥ 2` as a sufficiency criterion rather than a necessity.

**Concrete higher-order construction (conjectural, not verified):**
to achieve `2m + p = O(t⁴)`, parameterize through a *tangent* curve
on `Σ`. For example, expand the Pan witness in higher-order powers:

```
(p, q, r)(t) = (-1, t², 1/4 − t² + t⁴/4) + (a t⁴, b t⁴, c t⁴) + O(t⁶)
```

and choose `(a, b, c)` so that the leading `Θ(t²)` term in `δ(t)` cancels
exactly. From §5's quadratic `8δ² − 8t²δ + t⁴ = 0`, perturbing the
resolvent coefficients by `O(t⁴)` modifies the constant `t⁴/8` and the
linear coefficient `t²` — a careful Newton-polygon analysis would show
whether the leading `Θ(t²)` part of `δ` can be cancelled.

This is the genuine S5+ ACT direction. Not solvable in this PREP.

## 9. Recommended S4/S5 ACT actions

In light of §7–8, the S4/S5 ACT implementer should choose one of:

### Option A — accept the Pan witness as a `k = 1` discharge

Update `problem.md`'s OQ-02.a clause to `k ≥ 1` (first-order tangency
sufficient), and update the relative-error claim from `Ω(t^{1−k})` to
the corrected `Ω(1)` — *i.e., rename OQ-02.a to "Existence of a
tangency witness" rather than "Polynomial-rate blowup witness".* This
matches the standard numerical-analysis usage (Pan, Bini–Pan).

### Option B — search for a higher-order witness

Run the Newton-polygon analysis from §8 to find a `k = 2` witness. This
is mathematically substantial but probably feasible — the algebraic
geometry of the resolvent's discriminant locus is well-studied.

### Option C — separate the two questions

Reframe OQ-02.a as two sub-questions:
- **OQ-02.a.1**: existence of a `k = 1` witness. Discharged by Pan.
- **OQ-02.a.2**: existence of a `k ≥ 2` witness. Open.

This is the most honest framing and matches how the literature actually
discusses Ferrari's instability (Pan: "the cancellation happens"; the
rate is folklore-claimed but not rigorously pinned).

**Recommendation**: Option C, as a forward-design memo in `state.md`
on a future S5 PREP iteration. **Do not edit `state.md` in this PREP.**

## 10. What this PREP does NOT touch

- `research/problems/general-quartic-oq-02/problem.md` — untouched
- `research/problems/general-quartic-oq-02/knowledge.md` — untouched
- `research/problems/general-quartic-oq-02/state.md` — untouched
  (Option C from §9 is a *suggestion* for a future iteration's
  state.md edit, not enacted here)
- `src/data/research/problems/general-quartic-oq-02.json` — untouched
- `src/data/proofs/general-quartic/meta.json` — untouched
- `proofs/Proofs/GeneralQuartic.lean` — untouched
- PR #18365's file
  `research/problems/general-quartic-oq-02/sessions/2026-05-12-s4-prep-mathlib-gap-audit.md`
  — untouched; this PREP is on a different filename, distinct topic,
  and corrects an arithmetic detail rather than contradicting the gap
  audit's main conclusions.

## 11. No-edit guarantee

Exactly one new file:

- `research/problems/general-quartic-oq-02/sessions/2026-05-13-s4b-prep-pan-witness-arithmetic-audit.md`

(plus the new `sessions/` directory, if PR #18365's
`2026-05-12-s4-prep-mathlib-gap-audit.md` has not landed yet at merge
time of this PR; both PRs claim the directory creation.)

## 12. References

- `proofs/Proofs/GeneralQuartic.lean:77` (resolvent cubic, audited above)
- `research/problems/general-quartic-oq-02/problem.md:18-34` (OQ-02.a
  formal statement)
- PR #18365 §5 "Mathlib v4.26.0 asymptotic API surface (for OQ-02.a)"
  (the witness derivation audited above)
- Pan, V. Y. (1997). *Solving a polynomial equation: some history and
  recent progress.* SIAM Review 39(2), 187–220. (Cited in PR #18365.)
- Bini, D. A.; Pan, V. Y. (1996). *Polynomial and Matrix Computations.*
  Birkhäuser. (Background for Ferrari's instability folklore.)
- Press, W. H. et al. (1992/2007). *Numerical Recipes.* §5.6 "Quadratic
  and Cubic Equations" (Ferrari method numerical pitfalls; cited in
  PR #18365).
