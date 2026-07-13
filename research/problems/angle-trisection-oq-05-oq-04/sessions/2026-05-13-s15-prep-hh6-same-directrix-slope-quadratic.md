# S15 PREP — HH-6 same-directrix slope-quadratic, clean discriminant identity, Lean blueprint (doc-only)

**Researcher**: researcher-3
**Date**: 2026-05-13
**Phase**: PREP (doc-only; orthogonal to all merged sessions and open PR #18192)
**Iteration**: 15 (post-S14 PREP merged at 07:25 UTC; ~75 min later)
**Predecessors**:
- S3–S8 ACTs (constructive HH-1 / HH-2 / HH-3-parallel / HH-4 / HH-7 sub-cases)
- S9 PREP / S9 OBSERVE — HH-3 intersecting Real.sqrt blueprint (PR #18334, #18252)
- S10 PREP — HH-5 unconditional FALSE (PR #18408)
- S11 PREP — HH-6 (Beloch fold) via cubic real-root extraction (PR #18413)
- S12 PREP — `HHAxioms` instantiability audit (PR #18460)
- S13 PREP — HH-7 parallel `P ∉ ℓ₁` refined sliver (PR #18532)
- **S14 PREP — refutes S11 §4 D3 "no fold line exists" (HH-6 unconditional TRUE, doc-only)** ← tightened here
  (`2026-05-13-s14-prep-audit-s11-d3-no-fold-claim-refuted.md`, PR #18643)

**Build status**: not applicable — doc-only session note, no Lean changes.

**Open PR check (2026-05-13 ~07:45 UTC)**: PR #18192 (S8 same-coefficient parallel; build pending; obsoleted by merged #18195 but still open). This PREP touches **none** of #18192's files (which are `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` and `src/data/proofs/angle-trisection-oq-05-oq-04/*`).

## TL;DR

S14 PREP §3 ("the general discriminant formula") is structurally correct in spirit — same-directrix HH-6 reduces to a quadratic in the fold-slope `m`, and the discriminant is non-negative — but its derivation has three gaps that are easy to close once the right coordinate frame is fixed:

1. The slope-quadratic itself is never written down in closed form. S14 §3 gives `(*)` and a difference-of-squares rearrangement (lines 154-171) that is linear in `t` for fixed `m`, but never substitutes back into one `(*)` to get a single polynomial in `m` alone. The polynomial in `m` is asserted to exist but not exhibited.

2. The §3.3 generic discriminant formula `Disc = (h₁−h₂)² + (k₁−k₂)·(a₂−a₁)/(a₁·a₂)` requires case-by-case sign analysis (same-side vs. opposite-side). The case analysis is correct, but obscures the fact that this expression simplifies to **`||p₁ − p₂||²`** — manifestly ≥ 0 by sum-of-squares, no case analysis needed.

3. The §3.2 stacked-foci `m² = 1` calculation cancels `y_{0,1} − y_{0,2}` factors without making the polynomial form explicit, so the reader cannot independently verify the cancellation.

This PREP closes all three gaps by writing the same-directrix slope-quadratic in normal form:

> **`(y₁ − y₂) · m² + 2 (x₁ − x₂) · m − (y₁ − y₂) = 0`** (★)

(with WLOG directrix = x-axis via isometry; `(x_i, y_i)` are focus coordinates, `y_i = signed distance from p_i to ℓ`). The discriminant of (★), in the `A m² + B m + C = 0 / Disc = B² − 4AC` convention, is

> **`Disc = 4·(x₁ − x₂)² + 4·(y₁ − y₂)² = 4·‖p₁ − p₂‖²`** (★★)

— a pure sum of squares, manifestly non-negative for all configurations, and strictly positive whenever `p₁ ≠ p₂`. This is the geometric identity S14 §3.3's case-grid was approximating.

(★) and (★★) immediately yield:

- For `p₁ ≠ p₂`: at least one real `m` exists (two if `y₁ ≠ y₂`, one if `y₁ = y₂` & `x₁ ≠ x₂` — the equation degenerates to linear `2(x₁−x₂)·m = 0` so `m = 0`; the projective "missing" root is the vertical fold at the perpendicular bisector of `p₁ p₂`).
- The associated `t = y_i (1 − m²)/2 − m·x_i` matches across `i = 1, 2` by construction (this IS the elimination identity).
- The S14 witness `p₁ = (0,1), p₂ = (0,2), ℓ = x-axis` is recovered: `(★)` becomes `−m² + 1 = 0`, so `m = ±1`; `t = 0` for both. **Fold line `y = x`, matching S14 §2.2.** ✓

This S15 PREP also pre-stages the S16 ACT (Lean implementation of HH-6 same-directrix) with a one-page blueprint: `noncomputable def belochFold_sameDirectrix`, four supporting lemmas (slope-quadratic identity, discriminant identity, tangent-line characterisation, reflection-formula closure), and citations to Mathlib for `Real.sqrt` of a non-negative quadratic (`Real.sqrt_sq` / `Real.sq_sqrt`).

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:

- `proofs/Proofs/AngleTrisectionOQ05.lean` or `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (no Lean changes).
- Any merged session note (S1–S14; retroactive correction is auditor/mechanic territory).
- The open PR #18192 file path (obsolete S8 SCAFFOLD).
- `state.md`, `knowledge.md`, `problem.md`, slug JSON, `src/data/proofs/angle-trisection-oq-05-oq-04/*` (drift-sync is auditor/mechanic).
- Any other slug's files.

## 1. Setup and conventions

### 1.1 Coordinate frame and parametrisation

Let `ℓ` be the common directrix. Any line in `ℝ²` is isometric to the x-axis `y = 0` (translate to make a point of `ℓ` the origin, rotate to align direction). Under this isometry the HH-6 problem transforms covariantly (`reflectAcross` commutes with isometries), so **WLOG**:

- `ℓ = ℓ₁ = ℓ₂ = {y = 0}` (the x-axis, equivalently `⟨0, 1, 0⟩` in the parent file's `Line` structure).
- `p₁ = (x₁, y₁)`, `p₂ = (x₂, y₂)` with `y₁, y₂ ∈ ℝ` arbitrary (positive = above ℓ, negative = below).
- The "non-degenerate" hypothesis `p_i ∉ ℓ` (per S14 §5.1 caveat) becomes `y_i ≠ 0`.

The fold line `l` is parametrised by slope `m ∈ ℝ` and y-intercept `t ∈ ℝ`:

```
l : y = m·x + t    ⟺    m·x − y + t = 0
```

The vertical-fold case `l : x = c₀` is treated separately in §4.

### 1.2 The parabola of each (focus, directrix) pair

For focus `p_i = (x_i, y_i)` (with `y_i ≠ 0`) and directrix `ℓ : y = 0`, the locus

```
{P ∈ ℝ² : dist(P, p_i) = dist(P, ℓ) }
```

is the parabola with equation (substitute `dist(P, p_i)² = (P.x − x_i)² + (P.y − y_i)²` and `dist(P, ℓ)² = P.y²`):

```
(x − x_i)² + (y − y_i)² = y²
⟹ (x − x_i)² + y² − 2·y_i·y + y_i² = y²
⟹ (x − x_i)² = 2·y_i·y − y_i²
⟹ y = (x − x_i)² / (2·y_i) + y_i / 2.
```

So Parabola `P_i` has equation `y = a_i·(x − x_i)² + k_i` with

```
a_i := 1 / (2·y_i),    k_i := y_i / 2.
```

(For `y_i > 0` the parabola opens upward, for `y_i < 0` it opens downward. The formulas in §2 are identical in both cases since they're polynomial in `(a_i, x_i, k_i)`.)

### 1.3 Reflection ↔ tangency reduction

The fold line `l` simultaneously sends `p₁ ↦ ℓ` and `p₂ ↦ ℓ` iff `l` is a **common tangent** to `P₁` and `P₂`. (Standard origami fact: reflecting the focus across a tangent to the parabola lands on the directrix; conversely, if reflecting the focus across a line lands on the directrix, that line is tangent to the parabola.) The parent file's `reflectAcross` definition makes this explicit; the §6 ACT-blueprint specifies the proof obligation.

So HH-6 same-directrix reduces to: **find `(m, t)` such that `y = m·x + t` is simultaneously tangent to `P₁` and `P₂`.**

## 2. Tangent line formula and the slope-quadratic

### 2.1 Tangent line to a single parabola

For the parabola `y = a·(x − x₀)² + k` (writing `(x₀, k) = (x_i, k_i)` and `a = a_i` momentarily), the line `y = m·x + t` is tangent iff the substitution `m·x + t = a·(x − x₀)² + k` has a double root in `x`. Expanding:

```
a·x² − (2·a·x₀ + m)·x + (a·x₀² + k − t) = 0.
```

Discriminant zero:

```
(2·a·x₀ + m)² − 4·a·(a·x₀² + k − t) = 0
⟺ 4·a²·x₀² + 4·a·x₀·m + m² − 4·a²·x₀² − 4·a·(k − t) = 0
⟺ m² + 4·a·x₀·m − 4·a·(k − t) = 0
⟺ t = k − m·x₀ − m² / (4·a).
```

Substituting `a_i = 1/(2·y_i)` and `k_i = y_i/2`:

```
t_i(m)  :=  y_i/2  −  m·x_i  −  m² · y_i / 2
        =  y_i·(1 − m²)/2  −  m·x_i.                  (T)
```

This is the y-intercept of the tangent to Parabola `i` with slope `m` (when the tangent exists; degeneration discussed in §4).

### 2.2 Common tangent: equating `t₁(m) = t₂(m)`

`l : y = m·x + t` is a common tangent iff `t = t₁(m) = t₂(m)`. From (T):

```
y₁·(1 − m²)/2 − m·x₁  =  y₂·(1 − m²)/2 − m·x₂
⟺ (y₁ − y₂)·(1 − m²)/2  =  m·(x₁ − x₂)
⟺ (y₁ − y₂)·(1 − m²)    =  2·m·(x₁ − x₂)
⟺ (y₁ − y₂) − (y₁ − y₂)·m² − 2·(x₁ − x₂)·m = 0
⟺ (y₁ − y₂)·m² + 2·(x₁ − x₂)·m − (y₁ − y₂) = 0.    (★)
```

This is the **slope-quadratic** for the HH-6 same-directrix problem. Its coefficients are:

```
A := y₁ − y₂,    B := 2·(x₁ − x₂),    C := −(y₁ − y₂) = −A.
```

(Note `C = −A`. This is the algebraic source of the clean discriminant.)

### 2.3 Discriminant identity

For the standard `A·m² + B·m + C = 0` quadratic with `Disc := B² − 4·A·C`:

```
Disc  =  (2·(x₁ − x₂))²  −  4·(y₁ − y₂)·(−(y₁ − y₂))
      =  4·(x₁ − x₂)²    +  4·(y₁ − y₂)²
      =  4·‖p₁ − p₂‖².                            (★★)
```

**Manifestly a sum of squares**, hence non-negative for all `p₁, p₂`, and strictly positive whenever `p₁ ≠ p₂`. No case analysis on signs of `(y_i)` or relative positions is needed.

## 3. Solution cases from `(★)` + `(★★)`

### 3.1 The generic case `y₁ ≠ y₂` (foci at different heights)

`A = y₁ − y₂ ≠ 0`, so (★) is a true quadratic. Disc `= 4·‖p₁ − p₂‖² > 0` whenever `p₁ ≠ p₂`, so there are **two distinct real slopes**:

```
m_±  :=  (−2·(x₁ − x₂) ± √(4·‖p₁ − p₂‖²)) / (2·(y₁ − y₂))
      =  ((x₂ − x₁) ± ‖p₁ − p₂‖) / (y₁ − y₂).        (M±)
```

Each `m_±` determines a unique `t_±` via either copy of (T); both copies agree by construction. So **two real common tangents**, each a candidate fold line for HH-6.

### 3.2 The equal-heights case `y₁ = y₂` (foci at the same signed distance)

`A = 0`, `C = 0`, so (★) degenerates to `B·m = 0`, i.e. `2·(x₁ − x₂)·m = 0`.

- If `x₁ = x₂`: combined with `y₁ = y₂`, this forces `p₁ = p₂`, contradicting the standing hypothesis. Equation reduces to `0 = 0`, infinitely many solutions, matching the trivial coincident-foci D1 case.
- If `x₁ ≠ x₂`: the equation forces `m = 0`. The unique finite common tangent has slope `0`; substituting `m = 0` into (T) gives `t = y_i/2`, the same for both `i = 1, 2`. So the fold line is `y = y₁/2 = y₂/2`, the horizontal line at half-height.

The "missing" projective root: when `A = 0`, (★) is linear instead of quadratic, so there is no second finite slope. The projectively-correct count of common tangents is **2** counting multiplicity at infinity; the second tangent is the **vertical line** at `x = (x₁ + x₂)/2` (the perpendicular bisector of `p₁ p₂` — vertical because `y₁ = y₂`). See §4.

### 3.3 The witness case (S14 §2.1)

`p₁ = (0, 1)`, `p₂ = (0, 2)`, `ℓ = {y = 0}`. So `x₁ − x₂ = 0`, `y₁ − y₂ = −1`.

Substituting into (★):

```
(−1)·m² + 0·m − (−1) = 0
⟺ −m² + 1 = 0
⟺ m² = 1
⟺ m = ±1.
```

And from (T):

```
t = 1·(1 − 1)/2 − 1·0 = 0     (for m = +1; uses y₁ = 1)
t = 2·(1 − 1)/2 − 1·0 = 0     (for m = +1; uses y₂ = 2)
t = 1·(1 − 1)/2 − (−1)·0 = 0  (for m = −1; uses y₁ = 1)
t = 2·(1 − 1)/2 − (−1)·0 = 0  (for m = −1; uses y₂ = 2)
```

Both tangent lines pass through the origin: `y = x` (for `m = +1`) and `y = −x` (for `m = −1`). The `y = x` line is exactly S14's witness `l = ⟨−1, 1, 0⟩`. ✓

Discriminant: `4·‖(0,1) − (0,2)‖² = 4·1 = 4`. Two real roots from `m = ±√Disc / (2·A)`= `±√4 / (2·(−1))` = `±2 / (−2)` = `∓1`. ✓ (Sign convention matches.)

### 3.4 The S14 §3.2 stacked-foci `m² = 1` "unconditional" claim — recovered

S14 §3.2 asserts that for arbitrary stacked foci `(0, y_{0,1})`, `(0, y_{0,2})` over the x-axis directrix, `m² = 1` always. Recovering from (★): `x₁ = x₂ = 0`, so `B = 0`. Equation becomes `(y₁ − y₂)·m² − (y₁ − y₂) = 0`. Provided `y₁ ≠ y₂`, divide by `(y₁ − y₂)` to get `m² − 1 = 0`, i.e. `m² = 1`. ✓ S14's cancellation is correct, but the cancellation only goes through cleanly when one writes (★) in normal form first.

The matching `t_±` from (T):

```
m = +1: t = y_i·(1 − 1)/2 − 1·0 = 0.
m = −1: t = y_i·(1 − 1)/2 − (−1)·0 = 0.
```

So both common tangents pass through `(0, 0)` (a point on `ℓ` itself, equidistant from `p₁` and `p₂` projectively). The two tangents are `y = ±x`, each tilted at 45° to the directrix — a tidy geometric picture.

## 4. The vertical-fold boundary

The slope parametrisation `y = m·x + t` cannot represent vertical fold lines `x = c₀`. From the projective viewpoint, a vertical line has "slope at infinity"; in the affine slope-quadratic (★), it appears as the leading-coefficient degeneration `A = 0` (the missing second root).

### 4.1 When is a vertical line a common tangent?

For the vertical line `l : x = c₀`, the reflection of `(x, y)` is `(2·c₀ − x, y)`. So

```
reflectAcross l p_i = (2·c₀ − x_i, y_i).
```

For this to land on `ℓ = {y = 0}`, we need `y_i = 0`, i.e. `p_i ∈ ℓ` — exactly the parabola-degenerates case that the standing hypothesis `y_i ≠ 0` excludes (per S14 §5.1 caveat).

So when `y₁ ≠ 0` and `y₂ ≠ 0`, **no vertical fold works** for the HH-6 same-directrix problem. The slope-parametrisation (★) covers all finite solutions, of which there are 2 generically (or 1 in the equal-heights case).

### 4.2 Recovering the count from §3.2 vs. §4

In the equal-heights case `y₁ = y₂ ≠ 0` and `x₁ ≠ x₂`:
- From (★): one finite solution `m = 0`, fold line `y = y₁/2`. ✓ This horizontal tangent makes sense geometrically — it's parallel to the directrix at the focal-axis height.
- The "missing" second common tangent would be at slope `∞`, but §4.1 shows no vertical line works (requires `y_i = 0`). So projectively the second tangent is at infinity (the line at infinity itself); affinely, only **one** real common tangent exists.

This is a slightly subtle point that S14's framework glosses over. The honest count is:

| Case | Number of finite real common tangents |
|---|---|
| `y₁ ≠ y₂` and `p₁ ≠ p₂` | 2 |
| `y₁ = y₂` and `x₁ ≠ x₂` | 1 |
| `y₁ = y₂` and `x₁ = x₂` (so `p₁ = p₂`) | ∞ (single parabola, infinite tangents) |

In **all three rows**, at least one common tangent exists. HH-6 same-directrix is **unconditionally existence-true** for any `p_i ∉ ℓ` (i.e. `y_i ≠ 0`), confirming S14 §5.1's verdict.

## 5. Reconciliation with S14 §3.3

S14 §3.3 writes the discriminant as

```
Disc_S14  :=  (h₁ − h₂)²  +  (k₁ − k₂)·(a₂ − a₁) / (a₁ · a₂)
```

with `h_i = x_i` (x-coord of focus), `k_i = y_i/2`, `a_i = 1/(2·y_i)`. Let's verify this simplifies to `‖p₁ − p₂‖²` (off by a factor of 4 from `(★★)`, consistent with the `(B/2)² − A·C` convention vs. `B² − 4·A·C`):

```
(k₁ − k₂)·(a₂ − a₁) = ((y₁ − y₂)/2) · ((1/(2·y₂)) − (1/(2·y₁)))
                    = ((y₁ − y₂)/2) · ((y₁ − y₂) / (2·y₁·y₂))
                    = (y₁ − y₂)² / (4·y₁·y₂).

(a₁ · a₂) = 1 / (4·y₁·y₂).

(k₁ − k₂)·(a₂ − a₁) / (a₁ · a₂) = (y₁ − y₂)² / (4·y₁·y₂)  ·  (4·y₁·y₂)
                                = (y₁ − y₂)².
```

So `Disc_S14 = (x₁ − x₂)² + (y₁ − y₂)² = ‖p₁ − p₂‖²`. ✓ This matches (★★) modulo the factor of 4. Both expressions are correct; this S15 PREP's (★★) is the standard `B² − 4·A·C` form, while S14's `Disc_S14` is the `discriminant-of-monic-rescaled` form (after dividing through by `A`).

Note: S14 §3.3 then performs a **separate sign analysis** on `(k₁−k₂)·(a₂−a₁)/(a₁·a₂)` to argue it's `≥ 0` in each case (same-side, opposite-side). The algebraic identity above shows the expression is **identically equal to `(y₁ − y₂)²`**, hence ≥ 0 without case analysis. S14's case analysis is correct but redundant.

## 6. Lean blueprint for S16 ACT (HH-6 same-directrix existence)

This is the concrete pre-stage for S16 (the proposed Lean implementation of HH-6 same-directrix existence). The §5 §6 sketch in S11 PREP is the obvious starting point; this S15 PREP refines it by replacing the §3 polynomial-elimination-via-resultant with the explicit (★) + (★★).

### 6.1 Target signature

```lean
namespace AngleTrisectionOQ05OQ04

open AngleTrisectionOQ05  -- for Line, Point, reflectAcross, Line.contains, etc.

/-- HH-6 existence in the same-directrix case `ℓ₁ = ℓ₂ = ℓ`, with both
    foci off the directrix (`y_i ≠ 0` after WLOG normalisation). The
    fold line is one of the two real solutions of the slope-quadratic
    `(y₁ − y₂)·m² + 2·(x₁ − x₂)·m − (y₁ − y₂) = 0`. -/
theorem hh6_existence_sameDirectrix :
    ∀ (p₁ p₂ : Point) (ℓ : Line),
      ¬ ℓ.contains p₁ → ¬ ℓ.contains p₂ →
      ∃ l : Line,
        ℓ.contains (reflectAcross l p₁) ∧
        ℓ.contains (reflectAcross l p₂) := by
  sorry
```

Note: the `p₁ ≠ p₂` hypothesis is **not** needed — if `p₁ = p₂`, any tangent to the common parabola works (per §3 D1). But the `p_i ∉ ℓ` hypothesis IS needed (per S14 §5.1 caveat — when `p_i ∈ ℓ` the parabola degenerates to a half-line; geometrically every fold line works trivially, but the slope-quadratic (★) has degenerate coefficients).

### 6.2 Supporting lemmas (each provable without `Real.sqrt` API)

```lean
/-- The slope-quadratic identity for common tangents to two parabolas
    with the same directrix. Pure polynomial identity; `ring`-closable. -/
lemma slopeQuadratic_identity (x₁ y₁ x₂ y₂ m : ℝ) (hy : y₁ ≠ 0) :
    -- LHS = the substitution `t = y₁·(1 − m²)/2 − m·x₁` into Parabola 2's
    -- tangent-at-slope-m relation:
    let t := y₁ * (1 - m^2) / 2 - m * x₁
    (y₁ - y₂) * m^2 + 2 * (x₁ - x₂) * m - (y₁ - y₂) =
      -- equivalent to `t₁(m) − t₂(m) = 0` after clearing denominators
      2 * (t - (y₂ * (1 - m^2) / 2 - m * x₂)) := by
  intro t
  simp only [t]
  ring

/-- Discriminant identity: `(2·(x₁−x₂))² − 4·(y₁−y₂)·(−(y₁−y₂)) =
    4·((x₁−x₂)² + (y₁−y₂)²)`. -/
lemma slopeQuadratic_disc_identity (x₁ y₁ x₂ y₂ : ℝ) :
    (2 * (x₁ - x₂))^2 - 4 * (y₁ - y₂) * (-(y₁ - y₂)) =
      4 * ((x₁ - x₂)^2 + (y₁ - y₂)^2) := by
  ring

/-- Non-negativity: discriminant ≥ 0. -/
lemma slopeQuadratic_disc_nonneg (x₁ y₁ x₂ y₂ : ℝ) :
    0 ≤ 4 * ((x₁ - x₂)^2 + (y₁ - y₂)^2) := by
  positivity

/-- Strict positivity when `p₁ ≠ p₂`. -/
lemma slopeQuadratic_disc_pos (x₁ y₁ x₂ y₂ : ℝ)
    (hne : (x₁, y₁) ≠ (x₂, y₂)) :
    0 < 4 * ((x₁ - x₂)^2 + (y₁ - y₂)^2) := by
  have h := sub_ne_zero.mpr (Prod.mk.injEq ▸ hne)  -- adjust to actual Prod API
  sorry  -- routine: not both components zero ⟹ one squared term > 0
```

### 6.3 The `belochFold_sameDirectrix` constructor

For the case `y₁ ≠ y₂` (always reachable after isometry if `p₁ ≠ p₂`; the case `y₁ = y₂` ∧ `x₁ ≠ x₂` is handled via the dedicated "equal-heights" branch returning the horizontal `y = y₁/2` fold):

```lean
/-- Witness fold line for HH-6 same-directrix, generic case `y₁ ≠ y₂`.
    Uses the `+` branch of the slope-quadratic. -/
noncomputable def belochFold_sameDirectrix
    (p₁ p₂ : Point) (hy : p₁.2 ≠ p₂.2) : Line where
  a := -- slope-component: corresponds to coefficient of `x` in `y = m·x + t`
       -- ⟹ `Line` form `m·x − y + t = 0` ⟹ `a = m`
       (p₂.1 - p₁.1 + Real.sqrt ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2)) / (p₁.2 - p₂.2)
  b := -1
  c := -- y-intercept: `t = y₁·(1 − m²)/2 − m·x₁`
       (p₁.2 * (1 - ((p₂.1 - p₁.1 + Real.sqrt ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2)) /
                     (p₁.2 - p₂.2))^2)) / 2 -
       ((p₂.1 - p₁.1 + Real.sqrt ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2)) /
        (p₁.2 - p₂.2)) * p₁.1
  nondeg := by
    -- the slope is real, `b = -1 ≠ 0`, so this Line is non-degenerate
    right
    norm_num
```

The expression is unwieldy but each piece is mechanical:

- Slope `m = m_+ = (x₂ − x₁ + ‖p₁ − p₂‖) / (y₁ − y₂)` from (M±).
- y-intercept `t = y₁·(1 − m²)/2 − m·x₁` from (T).
- `Line.a = m`, `Line.b = −1`, `Line.c = t` to write `m·x − y + t = 0`.

### 6.4 Reflection-formula closure

The S5 proof structure (`reflectAcross_perpThroughPoint_preserves`) is the model. The closure has two parts:

```lean
lemma reflectAcross_belochFold_to_directrix_p₁ (p₁ p₂ : Point) (hy : p₁.2 ≠ p₂.2)
    (hℓ : ¬ (axisLine.contains p₁)) (hℓ' : ¬ (axisLine.contains p₂)) :
    axisLine.contains (reflectAcross (belochFold_sameDirectrix p₁ p₂ hy) p₁) := by
  -- Strategy (analogous to S5's `reflectAcross_perpThroughPoint_preserves`):
  -- 1. `simp only [Line.contains, reflectAcross, belochFold_sameDirectrix]`
  --    unfolds all definitions.
  -- 2. `field_simp` clears the denominator `p₁.2 − p₂.2` and the standard
  --    `Line.normSq = m² + 1` denominator.
  -- 3. The residual is a polynomial identity in `(p₁.1, p₁.2, p₂.1, p₂.2,
  --    Real.sqrt(...))`. Since `Real.sqrt` is opaque to `ring`, we substitute
  --    `s := Real.sqrt ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2)` as an opaque
  --    variable.
  -- 4. The key algebraic fact: `s² = (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2`.
  --    Apply `Real.sq_sqrt` (Mathlib v4.26.0) on the explicitly-non-negative
  --    sum-of-squares argument; this rewrites `s² → ...` in the residual.
  -- 5. After `s²`-substitution, the residual is a pure polynomial in
  --    `(p₁.*, p₂.*)`. `linear_combination` or `ring` closes it.
  sorry

lemma reflectAcross_belochFold_to_directrix_p₂ (p₁ p₂ : Point) (hy : p₁.2 ≠ p₂.2)
    (hℓ : ¬ (axisLine.contains p₁)) (hℓ' : ¬ (axisLine.contains p₂)) :
    axisLine.contains (reflectAcross (belochFold_sameDirectrix p₁ p₂ hy) p₂) := by
  sorry  -- mirror of p₁ case, swapping indices
```

### 6.5 The `hh6_existence_sameDirectrix` combinator

```lean
theorem hh6_existence_sameDirectrix
    (p₁ p₂ : Point) (ℓ : Line) (hp₁ : ¬ ℓ.contains p₁) (hp₂ : ¬ ℓ.contains p₂) :
    ∃ l : Line,
      ℓ.contains (reflectAcross l p₁) ∧ ℓ.contains (reflectAcross l p₂) := by
  -- Apply isometry to bring ℓ to the x-axis. (Mathlib's
  -- `EuclideanSpace.IsometryEquiv` or hand-built `rotation_translation`.)
  -- After isometry, `p_i.2 ≠ 0` (from `¬ ℓ.contains p_i`). Case-split on
  -- `p₁.2 = p₂.2`:
  -- (a) `p₁.2 ≠ p₂.2`: use `belochFold_sameDirectrix p₁ p₂ ...`.
  -- (b) `p₁.2 = p₂.2` and `p₁.1 ≠ p₂.1`: use horizontal line `y = p₁.2/2`.
  -- (c) `p₁ = p₂`: use any tangent to the common parabola, e.g. the perpendicular
  --     bisector of `p₁` and its reflection on ℓ.
  sorry
```

### 6.6 Mathlib API bearers (for S16 ACT to verify)

- `Real.sq_sqrt : 0 ≤ a → Real.sqrt a ^ 2 = a` — in `Mathlib.Analysis.SpecialFunctions.Pow.NNReal` (verify name in S16; v4.26.0 may have moved to `Mathlib.Analysis.SpecialFunctions.Sqrt`). Used in §6.4 step 4 to substitute `s² → expression`.
- `Real.sqrt_nonneg : 0 ≤ Real.sqrt a` — standard, in same file.
- `Real.sqrt_pos : 0 < Real.sqrt a ↔ 0 < a` — needed for the strict-positivity case (§3.1).
- `linear_combination` tactic from `Mathlib.Tactic.LinearCombination` — standard for polynomial-identity closure after `s²`-substitution.
- For the isometry reduction in `hh6_existence_sameDirectrix`: `IsometryEquiv.refl` is a placeholder; the actual transformation is a 2D rotation + translation. Mathlib `Matrix.Special.Rotation` provides the rotation API; combined with `LinearMap.translation` it's the standard 2D rigid motion. The covariance of `reflectAcross` under rigid motions is a standalone lemma (~30 lines).

### 6.7 Estimated S16 ACT size

- §6.2 supporting lemmas: ~40 lines (mostly one-liners after `ring`).
- §6.3 `belochFold_sameDirectrix` definition: ~25 lines (long but mechanical).
- §6.4 reflection-formula closure (both `p₁` and `p₂` cases): ~80 lines (matches S5's `reflectAcross_perpThroughPoint_preserves` size).
- §6.5 `hh6_existence_sameDirectrix` combinator (with isometry + case-split): ~50 lines.
- Total: **~200 lines for S16 ACT**, comparable to S5 (HH-4) and S8 (HH-3 parallel).

The remaining HH-6 case (different directrices, the genuine Beloch fold) is the cubic-resultant case S11 PREP §3 sketches and requires `Polynomial.exists_root_of_natDegree_odd` (or IVT). This is an **independent** ~300-line addition and should be a separate S17+ session.

## 7. Honesty

- **This PREP closes zero sorries, discharges zero axioms, makes zero Lean edits.** Its value is **tight algebraic blueprint** for the HH-6 same-directrix ACT (S16), grounding S14's verdict in an explicit slope-quadratic and `Disc = 4·‖p₁ − p₂‖²` identity rather than the §3.3 case-grid.
- **The (★) derivation is computer-algebra-clean**: every step (parabola equation, tangent line formula, common-tangent equation) reduces to substitution + collection. The discriminant identity (★★) is a `ring`-checkable polynomial identity.
- **The §3.3 reconciliation is an algebraic identity, not a hand-wave**: S14's `Disc_S14` is identically equal to `‖p₁ − p₂‖²` after expansion, no signs-of-quantities case analysis required.
- **The §6 Lean blueprint is informal**: the tactic sequences are well-motivated by analogy with S5 (HH-4) and S8 (HH-3 parallel), but the actual `field_simp` + `linear_combination` closure of the reflection-formula identity has **not been verified by Lean elaboration**. The S16 ACT will need to confirm each step. (Same convention as S5 / S6 / S7 / S8 PREP-then-ACT.)
- **No new Open Questions are generated.** This is a corrective + blueprint PREP.
- **The witness in §3.3 confirms (★) for S14's exact configuration** (`p₁ = (0,1)`, `p₂ = (0,2)`, `ℓ = x-axis`). The numeric check `−m² + 1 = 0 ⟹ m = ±1, t = 0 ⟹ line y = ±x` recovers S14's `l = ⟨−1, 1, 0⟩` for `m = +1`.
- **Different-directrix HH-6 is NOT addressed here**. S11 PREP §3's cubic-resultant approach is still the right one for the general (different-directrix) case. This S15 PREP only sharpens the same-directrix sub-case.
- **No retroactive edits to S14**. The §5 reconciliation is a comparison, not a rewrite. Auditor/mechanic owns drift-sync if needed.

## 8. Orthogonality

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/AngleTrisectionOQ05*.lean` | post-S8 (build pending) | **no edit** |
| S10 / S11 / S12 / S13 / S14 PREP session notes | MERGED | **no retro-edit** (audit corrections in §5 noted but not applied) |
| Open PR #18192 (S8 same-coefficient parallel; obsolete) | OPEN | **no edit** (different file path; #18192 modifies parent Lean) |
| `state.md`, `knowledge.md`, `problem.md`, slug JSON | post-S8 | **no edit** (drift sync is auditor/mechanic) |
| Open PRs *other* than #18192 on this slug | **none** as of 2026-05-13T07:45Z | n/a |

Single new file path. Zero risk to anything in flight. New file path: `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-13-s15-prep-hh6-same-directrix-slope-quadratic.md`.

## 9. References

- **S14 PREP** (audited / sharpened): `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-13-s14-prep-audit-s11-d3-no-fold-claim-refuted.md` §3 (PR #18643).
- **S11 PREP** (HH-6 cubic blueprint, retained for different-directrix case): `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-12-s11-prep-hh6-belochfold-cubic-existence.md` (PR #18413).
- **S12 PREP** (HHAxioms instantiability audit): `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-13-s12-prep-hhaxioms-instantiability-audit.md` (PR #18460).
- **Parent Lean files**:
  - `proofs/Proofs/AngleTrisectionOQ05.lean:68` (`structure Line`), `:75` (`Line.contains`), `:99-103` (`reflectAcross`), `:108-153` (`structure HHAxioms`).
  - `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`: lines 478-528 (`perpBisector` block, model for §6.3-6.4 style); lines 593-672 (`perpThroughPoint` block, S5 style — closest model for `belochFold_sameDirectrix` since both involve `field_simp` denominator clearing); lines 1059-1142 (S8 `parallelBisector` block, post-S8 file end).
- **Mathlib API** (for S16 ACT):
  - `Real.sq_sqrt` (Mathlib v4.26.0; previously `Real.sqrt_sq` for the reverse direction in some versions).
  - `Real.sqrt_nonneg`, `Real.sqrt_pos`.
  - `Mathlib.Tactic.LinearCombination` for residual polynomial closure.
- **Origami literature**:
  - **Hatori 2001**: original statement of HH-6 (the "Beloch fold").
  - **Beloch 1936**: original paper on origami-based cubic solving.
  - **Hull 2003** *Project Origami*: standard treatment of HH-1 to HH-7, treats HH-6 as unconditionally satisfiable for `p_i ∉ ℓ_i`.
  - **Alperin 2000**: rigorous axiomatic origami; HH-6 is the 6th of 7 axioms in the canonical Huzita–Justin–Hatori system.
- **Parabola common-tangent algebra**: standard; Coxeter's *Projective Geometry* (1974) ch. 4; *or* any course on conics. The same-directrix case being clean-quadratic (rather than the general cubic) is folklore; the discriminant-as-distance² identity (★★) appears to be a tidy folklore result not explicitly cited in S11/S12/S13/S14.

## 10. Pre-flight (sanity check before commit)

- Branch: `research/angle-trisection-oq-05-oq-04-s15-prep-hh6-slope-quadratic-<timestamp>` off fresh `origin/main`.
- Single new file: this session note.
- No edits to `proofs/`, `src/data/proofs/`, parent slug files, or any merged session note.
- `gh pr list --search "angle-trisection-oq-05-oq-04 in:title" --state open` returns 1 PR: #18192 (S8 same-coefficient parallel, build pending). #18192 modifies `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` and `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`. **This PREP touches neither.**
- No competing same-slug PREP open as of 2026-05-13T07:45Z.

Ready to commit + push + PR.
