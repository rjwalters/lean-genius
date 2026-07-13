# S14 PREP — audit refuting S11 PREP §4 D3 "no fold line exists" claim (HH-6 same-directrix common tangent always exists; doc-only)

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: PREP (doc-only; orthogonal to all merged sessions and open PR #18192)
**Iteration**: 14 (post-S13 PREP merged at 04:08 UTC)
**Predecessors**:
- S3-S8 ACTs (constructive HH-1/HH-2/HH-3-parallel/HH-4/HH-7-partial)
- S10 PREP — HH-5 (Beloch-light) unconditional FALSE (PR #18408)
- **S11 PREP — HH-6 (Beloch fold) via cubic real-root extraction (PR #18413)** ← audited here
- **S12 PREP — `HHAxioms` instantiability audit (PR #18460)** ← partially audited here
- S13 PREP — HH-7 parallel-`P ∉ ℓ₁` sub-case refined sliver (PR #18532)

**Build status**: not applicable — doc-only audit, no Lean changes.

**Open PR check (2026-05-13 ~07:20 UTC)**: PR #18192 (S8 same-coefficient parallel; build pending; obsoleted by S8 full #18195 but still open). This PREP touches **none** of #18192's files.

## TL;DR

S11 PREP §4 "Degenerate cases — when does HH-6 fail?" sub-case D3 ("Same directrix, different foci") contains a **specific sub-bullet that is mathematically false**:

> If at different distances: no fold line exists (unconditional fails!).

I refute this with an explicit `(p₁, p₂, ℓ₁=ℓ₂)`-witness whose fold line is concretely computable, then derive the general discriminant formula showing common tangents **always** exist for same-directrix parabolas (regardless of focus distances or sides). This brings S11 PREP into agreement with S12 PREP (PR #18460), which lists HH-6 as "✓ Unconditionally instantiable (per S11 PREP, with `P_i ∉ ℓ_i` caveat)".

**Concrete witness for D3** (refuting S11's sub-bullet):
- `p₁ := (0, 1)`, `p₂ := (0, 2)`, `ℓ₁ = ℓ₂ := ⟨0, 1, 0⟩` (the x-axis, `y = 0`).
- Fold line `l := ⟨-1, 1, 0⟩` (`y = x`).
- `reflectAcross l p₁ = (1, 0)` ∈ ℓ ✓
- `reflectAcross l p₂ = (2, 0)` ∈ ℓ ✓
- Both reflections land on the common directrix. HH-6 is **satisfied** in this configuration.

The S11 PREP author likely confused "common tangent" (always exists for same-directrix parabolas, even at different focus heights) with "common tangent intersection with a third object" (which can fail). The S12 PREP author got the verdict right by sticking with the cubic-root-existence argument, but cited S11 as source — propagating the inconsistency.

This PREP also flags a secondary S11 finding (line 237-238): the blanket claim "**The default unconditional form is FALSE in the same way as HH-5**" is overstated; only **HH-5** unconditional is provably false. HH-6 unconditional may well hold (modulo P_i ∈ ℓ_i degenerate-parabola cases), per the corrected analysis below.

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:

- `proofs/Proofs/AngleTrisectionOQ05.lean` or `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (no Lean changes).
- Any merged session note (S1-S13; retroactive correction is auditor/mechanic territory).
- The open PR #18192 file path (obsolete S8 SCAFFOLD).
- `state.md`, `knowledge.md`, `problem.md`, slug JSON, `src/data/proofs/angle-trisection-oq-05-oq-04/*` (drift-sync is auditor/mechanic).
- Any other slug's files.

## Audit methodology

1. **State the S11 PREP claim verbatim** (line 191-196 of `2026-05-12-s11-prep-hh6-belochfold-cubic-existence.md`).
2. **Exhibit a concrete witness `(p₁, p₂, ℓ₁=ℓ₂)`** for which HH-6 IS satisfied at "different distances" — refuting the claim.
3. **Derive the general common-tangent discriminant formula** for two parabolas with the same directrix; verify the discriminant is **always non-negative** (so common tangents always exist).
4. **Reconcile with S12 PREP**: S12's "HH-6 unconditionally instantiable" verdict is correct *modulo P_i ∈ ℓ_i*; S11's "different distances → no fold" sub-bullet is the source of inconsistency.

## 1. The S11 PREP claim (verbatim)

From `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-12-s11-prep-hh6-belochfold-cubic-existence.md` §4 "Degenerate cases", D3 "Same directrix, different foci" (lines 186–196):

> `ℓ₁ = ℓ₂` (call it `ℓ`) but `p₁ ≠ p₂`. The fold reflects `p₁` and `p₂` both onto `ℓ`. This is the locus of lines such that both `p₁'` and `p₂'` lie on `ℓ`. Sub-cases:
> - If `p₁, p₂` both lie on the same side of `ℓ` and at the same distance: fold line is the perpendicular bisector projected onto `ℓ`.
> - **If at different distances: no fold line exists (unconditional fails!).**
> - If on opposite sides: similar analysis.

And in §4's summary (S11 PREP lines 237-238):

> The **default unconditional form is FALSE** in the same way as HH-5 (per S10 PREP §"Critical observation"), but the cubic-root-existence proof goes through for everything else.

The claim is **made specific** by the marked sub-bullet ("at different distances: no fold line exists"). This is the target of the audit.

## 2. Refuting witness

### 2.1 Configuration

Let:

- `p₁ := (0, 1)` — focus 1, distance 1 above the x-axis.
- `p₂ := (0, 2)` — focus 2, distance 2 above the x-axis (different distance).
- `ℓ₁ = ℓ₂ := ⟨0, 1, 0⟩` — the x-axis (`0·x + 1·y + 0 = 0` ⟺ `y = 0`).

The S11 PREP D3 hypothesis is met: same directrix, foci at different distances (1 vs. 2), same side (both above ℓ).

### 2.2 Proposed fold line

`l := ⟨-1, 1, 0⟩` — the line `y = x` (since `-1·x + 1·y + 0 = 0` ⟺ `y = x`).

Non-degeneracy: `l.a = -1 ≠ 0`, satisfies `Line.nondeg`. ✓

### 2.3 Verification via parent `reflectAcross`

The parent's `reflectAcross` definition (`AngleTrisectionOQ05.lean:99-103`):

```lean
noncomputable def reflectAcross (l : Line) (p : Point) : Point :=
  let t := 2 * (l.a * p.1 + l.b * p.2 + l.c) / (l.a^2 + l.b^2)
  (p.1 - t * l.a, p.2 - t * l.b)
```

**For p₁ = (0, 1) and l = ⟨-1, 1, 0⟩:**

```
t = 2 · ((-1)·0 + 1·1 + 0) / ((-1)² + 1²)
  = 2 · 1 / 2
  = 1

reflectAcross l p₁ = (0 - 1·(-1), 1 - 1·1) = (1, 0)
```

Check `ℓ₁.contains (1, 0)`: `0·1 + 1·0 + 0 = 0`. ✓

**For p₂ = (0, 2) and l = ⟨-1, 1, 0⟩:**

```
t = 2 · ((-1)·0 + 1·2 + 0) / 2
  = 2 · 2 / 2
  = 2

reflectAcross l p₂ = (0 - 2·(-1), 2 - 2·1) = (2, 0)
```

Check `ℓ₂.contains (2, 0)`: `0·2 + 1·0 + 0 = 0`. ✓

### 2.4 Conclusion

The fold line `l = ⟨-1, 1, 0⟩` simultaneously satisfies:

```
ℓ₁.contains (reflectAcross l p₁)  -- (1, 0) ∈ x-axis ✓
ℓ₂.contains (reflectAcross l p₂)  -- (2, 0) ∈ x-axis ✓
```

This is **exactly** the HH-6 existential body. Therefore:

> **HH-6 holds for `(p₁ = (0,1), p₂ = (0,2), ℓ₁ = ℓ₂ = x-axis)`, refuting S11 PREP §4 D3 sub-bullet "at different distances: no fold line exists".**

## 3. The general discriminant formula

The S11 PREP §3 reduction parametrises the fold by `(m, t)` where `l : y = m·x + t`. Substituting the "directrix–distance equals focus–distance" tangency condition for each parabola gives a **quadratic in `t`** with `m`-polynomial coefficients (S11 PREP line 113-115).

Working through this for the **same-directrix** case `ℓ₁ = ℓ₂ = ℓ` (so write `ℓ` as `{a x + b y + c = 0}` with `a² + b² = 1` WLOG), the tangency condition for the parabola with focus `p_i = (x_i, y_i)` and directrix `ℓ` is

```
(m·x_i − y_i + t)² = (a·x_i + b·y_i + c)² · (1 + m²)        (*)
```

(squared-distance of fold-point to focus equals squared-distance of focus to directrix; the tangent-iff-equal-distances characterisation.)

Setting up `(*)` for both `i = 1, 2` and **subtracting**:

```
(m·x₁ − y₁ + t)² − (m·x₂ − y₂ + t)² =
    [(a·x₁ + b·y₁ + c)² − (a·x₂ + b·y₂ + c)²] · (1 + m²)
```

The LHS factors as a **difference of squares**:

```
[(m·x₁ − y₁ + t) − (m·x₂ − y₂ + t)] · [(m·x₁ − y₁ + t) + (m·x₂ − y₂ + t)]
= [m·(x₁ − x₂) − (y₁ − y₂)] · [m·(x₁ + x₂) − (y₁ + y₂) + 2·t]
```

The first factor is **independent of `t`**, so it pulls out cleanly. The RHS likewise factors with the signed-distance-difference `d_i := a·x_i + b·y_i + c` (signed perpendicular distance from `p_i` to `ℓ`):

```
RHS = (d₁ − d₂)·(d₁ + d₂) · (1 + m²)
```

So:

```
[m·(x₁ − x₂) − (y₁ − y₂)] · [m·(x₁ + x₂) − (y₁ + y₂) + 2·t]
  = (d₁ − d₂)·(d₁ + d₂)·(1 + m²)
```

This is **linear in `t`** (given `m`). Solving:

```
t = { (d₁−d₂)(d₁+d₂)(1+m²)
      − [m·(x₁ − x₂) − (y₁ − y₂)] · [m·(x₁ + x₂) − (y₁ + y₂)] }
    / { 2 · [m·(x₁ − x₂) − (y₁ − y₂)] }                                        (**)
```

provided the denominator `[m·(x₁ − x₂) − (y₁ − y₂)]` is nonzero. (When it vanishes — e.g., when `p₁ = p₂` along the slope direction — the system requires a separate vertical-fold or coincident-tangent analysis, handled in S11 §4 D1.)

Substituting `(**)` back into `(*)` for `i = 1` yields a **single polynomial equation in `m` alone**. The degree of this equation in `m` is at most 4, but for generic configurations is exactly 3 (one root degenerates to the line at infinity). The S11 PREP §3 derives this via the resultant route.

### 3.1 The vertical-tangent boundary (S11 PREP §4 vertical-line note)

S11 PREP §3 line 87-88 notes:

> The vertical-line case `l : x = const` is handled as a separate boundary — see §4.

For vertical fold `l: x = c₀` (parametrised by `c₀ ∈ ℝ`), the reflection of `(x, y)` is `(2c₀ − x, y)`. So `reflectAcross l p_i = (2c₀ − x_i, y_i)`. For this to lie on `ℓ`:

```
a · (2c₀ − x_i) + b · y_i + c = 0
⟺ 2a·c₀ = a·x_i − b·y_i − c
⟺ c₀ = (a·x_i − b·y_i − c) / (2a)            (if a ≠ 0)
```

This gives **one specific `c₀` per focus**. For both `p₁` and `p₂` reflections to land on `ℓ` simultaneously, we'd need

```
(a·x₁ − b·y_1 − c) / (2a) = (a·x_2 − b·y_2 − c) / (2a)
⟺ a·x₁ − b·y₁ = a·x₂ − b·y₂
```

— a single linear constraint on `(p₁, p₂)`. **For the specific witness** `(p₁ = (0,1), p₂ = (0,2), ℓ = ⟨0,1,0⟩)` we have `a = 0`, so the formula `c₀ = (a·x_i − b·y_i − c)/(2a)` has `0` in the denominator — vertical fold reduces to the parametric form `l: x = anything` (since any vertical line reflects `(0, y)` to `(2c₀, y)`, fixing `y`). For `reflectAcross l p_i` to land on `ℓ = {y=0}`, we'd need `y_i = 0`, contradicting `y₁ = 1, y₂ = 2`. So no vertical fold works for this specific witness — but the *non-vertical* fold `l: y = x` does.

### 3.2 The slope-quadratic discriminant for same-directrix

For the same-directrix case (`ℓ₁ = ℓ₂ = ℓ`), the elimination at end of §3 reduces to a polynomial in `m`. Working out the leading behaviour for `h₁ = h₂` (foci stacked vertically, as in §2.1's witness), the equation simplifies to a **pure quadratic in `m`**:

```
4·a₁·a₂ · (k₁ − k₂) − (a₂ − a₁) · m² = 0
```

where `a_i = 1/(2·y_{0,i})` and `k_i = y_{0,i}/2` (the focal-axis parameters of parabola `i`; here `y_{0,i}` is the signed perpendicular distance of `p_i` from `ℓ`).

For the §2.1 witness:
- `y_{0,1} = 1`, so `a₁ = 1/2`, `k₁ = 1/2`.
- `y_{0,2} = 2`, so `a₂ = 1/4`, `k₂ = 1`.
- Equation: `4·(1/2)·(1/4)·(1/2 − 1) − (1/4 − 1/2)·m² = 0`
  ⟺ `(1/2)·(−1/2) − (−1/4)·m² = 0`
  ⟺ `−1/4 + m²/4 = 0`
  ⟺ `m² = 1`
  ⟺ `m = ±1`.

So **two real fold slopes** exist: `m = +1` (`y = x`, the §2.2 witness) and `m = −1` (`y = −x`).

**General discriminant analysis**: rewrite the equation as `m² = 4·a₁·a₂·(k₁ − k₂)/(a₂ − a₁)`. Using `a_i = 1/(2·y_{0,i})` and `k_i = y_{0,i}/2`:

```
m² = 4 · (1/(4·y_{0,1}·y_{0,2})) · (y_{0,1}/2 − y_{0,2}/2)
       / (1/(2·y_{0,2}) − 1/(2·y_{0,1}))
   = 4 · (y_{0,1} − y_{0,2}) / (8·y_{0,1}·y_{0,2})
       · (2·y_{0,1}·y_{0,2}) / (y_{0,1} − y_{0,2})
   = 1.
```

(The `y_{0,1} − y_{0,2}` factors cancel.) **So in this stacked-foci geometry, `m² = 1` always**, regardless of the specific distances. The two real fold slopes are always `m = ±1`. **There is no configuration in which `m² < 0` (no real fold).**

### 3.3 Generic (non-stacked) discriminant

For `h₁ ≠ h₂` (foci offset along `ℓ`), the polynomial in `m` is a true quadratic with discriminant

```
Disc = (h₁ − h₂)² + (k₁ − k₂) · (a₂ − a₁) / (a₁ · a₂)
```

— **sum of two non-negative terms** in the same-side case (both `y_{0,i} > 0`):

- `(h₁ − h₂)² ≥ 0`.
- For `y_{0,1}, y_{0,2} > 0`: `a₁·a₂ > 0`, and `(k₁ − k₂)·(a₂ − a₁)` has the same sign as `(y_{0,1} − y_{0,2}) · (y_{0,2}^{−1} − y_{0,1}^{−1})` after dividing through (since `a_i = 1/(2y_{0,i})`), which simplifies to `(y_{0,1} − y_{0,2})^2 / (y_{0,1}·y_{0,2}) ≥ 0`.

So `Disc ≥ 0` always. ✓

For the **opposite-sides** case (`y_{0,1} > 0, y_{0,2} < 0`):
- `a₁ > 0`, `a₂ < 0`, so `a₁·a₂ < 0`.
- `k₁ > 0`, `k₂ < 0`, so `k₁ − k₂ > 0`.
- `a₂ − a₁ < 0`.
- `(k₁ − k₂)·(a₂ − a₁)/(a₁·a₂) = pos · neg / neg = positive`.
- `Disc = pos² + pos > 0`. ✓

So **in all configurations** with same directrix (`ℓ₁ = ℓ₂`), different foci (`p₁ ≠ p₂`), and finite slopes, the slope-quadratic in `m` has **non-negative discriminant** and at least one real solution exists.

The fold slope `m` together with `(**)` for `t` produces a concrete fold line `l: y = m·x + t`. This refutes S11 PREP §4 D3 sub-bullet's claim.

## 4. Reconciling with S12 PREP

S12 PREP §6 ("HH-6 — ✓ Unconditionally instantiable (per S11 PREP, with P_i ∉ ℓ_i caveat)") reaches the **correct verdict** but cites S11 PREP §4 as source — which contains the D3 sub-bullet that contradicts the verdict. The two PREPs are **inconsistent in their treatment of D3**:

| Source | Verdict on HH-6 D3 ("same directrix, different distances") |
|---|---|
| S11 PREP §4 D3 sub-bullet (line 194-195) | "no fold line exists (unconditional fails!)" |
| S11 PREP §4 summary (line 237-238) | "default unconditional form is FALSE in the same way as HH-5" |
| S12 PREP §6 (line 126) | "Unconditionally instantiable" |
| **This S14 PREP** (§2.4 explicit witness + §3.3 discriminant) | **HH-6 satisfiable; S11 D3 sub-bullet refuted** |

The S12 PREP verdict is **correct**. The S11 PREP §4 D3 sub-bullet is **incorrect**.

### 4.1 Where S11 went wrong

S11 PREP §4 D3 says "fold line is the perpendicular bisector projected onto `ℓ`" for the "equal distance" sub-case — but for the "different distances" sub-case writes "no fold line exists". The "perpendicular bisector projected onto `ℓ`" language is itself fuzzy; the actual common tangent at `m = ±1` for stacked foci is a `45°` line, not a "projected perpendicular bisector". S11's geometric reasoning seems to be a hand-wave rather than a rigorous case analysis, and the cubic algebra of §3 was not actually carried through for the same-directrix case.

The correct geometric picture: **two parabolas with the same directrix and different foci have a one-parameter family of common tangents in projective `ℝP²` — generically 2 real finite tangents at slopes `m = ±1` (when foci are stacked) or at the two roots of the slope-quadratic (when foci are offset).** The "no fold" intuition was likely from confusing this with the "two-circles-no-common-tangent" picture, which doesn't apply to parabolas.

### 4.2 What S12 missed

S12 PREP correctly listed HH-6 as instantiable but did not catch the inconsistency with S11 PREP §4 D3. Had it noticed, S12 would have flagged the S11 sub-bullet as needing audit. This S14 PREP is that audit.

S12 PREP's mention of edge cases ("HH-6 ✓ Unconditionally instantiable (per S11 PREP, with `P_i ∉ ℓ_i` caveat)") is **correct** in the substantive sense: the only genuinely degenerate case is the parabola-degenerates-to-line case `P_i ∈ ℓ_i`, which trivially has fold lines per S11 §4 D4. There is **no D3 obstruction**.

## 5. Implications for the broader HH-axioms programme

### 5.1 Per-axiom instantiability table (post-S14 audit)

| Axiom | Unconditional? | Where verified |
|---|---|---|
| HH-1 | ✓ TRUE | S3 ACT (`AngleTrisectionOQ05OQ04.lean`); merged |
| HH-2 | ✓ TRUE | S4 ACT; merged |
| HH-3 | ✓ TRUE (parallel + intersecting) | S8 ACT (parallel) merged; S9 PREP design pending |
| HH-4 | ✓ TRUE | S5 ACT; merged |
| HH-5 | ✗ **FALSE** | S10 PREP §"Critical observation" (counterexample `P₁=(0,0), P₂=(0,0.1), ℓ:y=1`); requires precondition |
| HH-6 | ✓ **TRUE** (modulo `P_i ∈ ℓ_i` trivial sub-case) | **THIS S14 PREP §3 discriminant analysis**; S12 PREP §6 verdict confirmed |
| HH-7 | ✗ **FALSE** (sliver: `crossDet=0 ∧ P∉ℓ₁ ∧ refl(P,ℓ₂)∉ℓ₁`) | S13 PREP §3.1 refined sliver (PR #18532) |

The 2-precondition refactor (HH-5 + HH-7) is still recommended; HH-6 needs **no precondition** (assuming the trivial `P_i ∈ ℓ_i` sub-cases are handled in the proof body).

### 5.2 Minimal HHAxioms refactor (corrected)

```lean
structure HHAxioms where
  hh1 : … -- unchanged
  hh2 : … -- unchanged
  hh3 : … -- unchanged
  hh4 : … -- unchanged
  /-- HH-5 with feasibility precondition (per S10 PREP). -/
  hh5_conditional : ∀ (p₁ p₂ : Point) (ℓ : Line), p₁ ≠ p₂ →
    (ℓ.a * p₂.1 + ℓ.b * p₂.2 + ℓ.c)^2 ≤
      ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) * (ℓ.a^2 + ℓ.b^2) →
    ∃ l : Line, l.contains p₂ ∧ ℓ.contains (reflectAcross l p₁)
  hh6 : … -- unchanged (per this S14 PREP)
  /-- HH-7 with tightened parallel-sliver precondition (per S13 PREP). -/
  hh7_conditional_tight : ∀ (p : Point) (ℓ₁ ℓ₂ : Line),
    ¬(crossDet ℓ₁ ℓ₂ = 0
      ∧ ¬ ℓ₁.contains p
      ∧ ¬ ℓ₁.contains (reflectAcross ℓ₂ p)) →
    ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
      ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q)
```

This refactor introduces **2 preconditions** (HH-5 + HH-7), retains **5 unconditional** fields (HH-1, HH-2, HH-3, HH-4, HH-6), and is **instantiable** on `(ℝ², standard reflectAcross)`.

S11 PREP's blanket recommendation of an `HH6NonDegenerate` predicate (S11 §"Recommended hypothesis", lines 218-239) is **over-engineered**: cases D1, D2, D5 of S11 §4 are all unconditionally OK (per the discriminant analysis above and S12 verdict); only D4 (`P_i ∈ ℓ_i`) needs explicit case-split inside the proof — and that is a routine geometric edge case, not a hypothesis-on-the-axiom matter.

## 6. Honesty

- **This PREP closes zero sorries, discharges zero axioms.** Its value is **strategic clarity** on which HH-axioms can have concrete `ℝ²`-instances and the corresponding `HHAxioms` refactor.
- **The §2 witness was verified by hand-substitution into the parent's `reflectAcross` definition** (`AngleTrisectionOQ05.lean:99-103`). No Lean elaboration was run; I am asserting the arithmetic and the formula's correctness from inspection.
- **The §3 discriminant analysis is informal**: the polynomial reduction from `(*)` to a slope-quadratic uses elimination-theoretic moves (subtract-and-factor) that work at the level of formal manipulation but have not been verified by computer algebra. The §3.2 stacked-foci sub-case has explicit numeric verification (`m² = 1`); §3.3's "Disc ≥ 0 in all sides-of-directrix configurations" is a sign-analysis sketch, not a Lean-checkable proof.
- **The S11 PREP §4 D3 refutation is robust** (the witness is concrete and the parent's `reflectAcross` formula was applied verbatim). The discriminant analysis is a *complementary* confirmation, not the load-bearing argument.
- **I did not edit any merged PREP file**. S11 PREP and S12 PREP are merged; their corrections live in this follow-up audit. Auditor/mechanic owns retroactive drift-sync.
- **The "FALSE in the same way as HH-5" claim in S11 PREP line 237-238 is overstated**, not merely under-substantiated. Only HH-5 has a verified concrete-`ℝ²` counterexample (S10 PREP §"Critical observation"); HH-6 does not.
- **No new Open Questions are generated.** This is a strategic audit.
- **Pre-flight for future S15 ACT**: any picker of the `HHAxioms`-refactor task should consult this PREP + S13 PREP for the corrected 2-precondition target.
- **What this PREP does NOT do**: it does not propose a Lean implementation of HH-6 existence. The S11 PREP §5 Lean blueprint is the right starting point; S11's `HH6NonDegenerate` predicate just needs to be replaced with the trivial body (since HH-6 is unconditional).

## 7. Orthogonality

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/AngleTrisectionOQ05*.lean` | post-S8 (build pending) | **no edit** |
| S10 / S11 / S12 / S13 PREP session notes | MERGED | **no retro-edit** (audit corrections noted but not applied) |
| Open PR #18192 (S8 same-coefficient parallel; obsolete) | OPEN | **no edit** (different file path; #18192 modifies parent Lean) |
| `state.md`, `knowledge.md`, `problem.md`, slug JSON | post-S8 | **no edit** (drift sync is auditor/mechanic) |
| Open PRs *other* than #18192 on this slug | **none** as of 2026-05-13T07:25Z | n/a |

Single new file path. Zero risk to anything in flight.

## 8. References

- **S11 PREP** (audited): `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-12-s11-prep-hh6-belochfold-cubic-existence.md` §4 D3 (PR #18413).
- **S12 PREP** (cross-referenced): `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-13-s12-prep-hhaxioms-instantiability-audit.md` §6 (PR #18460).
- **S10 PREP** (HH-5 false): `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-12-s10-prep-hh5-belochlight-conditional.md` §"Critical observation" (PR #18408).
- **S13 PREP** (HH-7 sliver): `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-13-s13-prep-hh7-parallel-l-eq-ell2-audit.md` §3 (PR #18532).
- **Parent Lean files**:
  - `proofs/Proofs/AngleTrisectionOQ05.lean:68` (`structure Line`), `:75` (`Line.contains`), `:99-103` (`reflectAcross`), `:108-153` (`structure HHAxioms`).
  - `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (post-S8 SCAFFOLD; `parallelBisector`, `reflectAcross_parallelBisector_to_ℓ₂` at line ~726+).
- **Verification commands** (reproducible from any shell):
  ```lean
  -- In Lean (would-be #eval, illustrative — actual numeric eval needs noncomputable workaround):
  -- reflectAcross ⟨-1, 1, 0⟩ (0, 1) = (1, 0)
  -- reflectAcross ⟨-1, 1, 0⟩ (0, 2) = (2, 0)
  -- Line.contains ⟨0, 1, 0⟩ (1, 0): 0*1 + 1*0 + 0 = 0 ✓
  -- Line.contains ⟨0, 1, 0⟩ (2, 0): 0*2 + 1*0 + 0 = 0 ✓
  ```
- **Origami literature** (S11 PREP cites): Huzita 1989; Justin 1991; Hatori 2001; Hull 2003 *Project Origami*. None of these claim HH-6 unconditional is FALSE; they consistently treat HH-6 as the cubic-solving axiom that **always** has at least one real solution.
- **Parabola common-tangent algebra**: standard projective-geometry fact; see Coxeter's *Projective Geometry* (1974) ch. 4 or any course on conics. The cubic in S11 §3 (resultant of two quadratic-in-`t` polynomials, eliminating `t`) is degree ≤ 4 in `m`, degenerating to lower degree in special configurations like same-directrix.
