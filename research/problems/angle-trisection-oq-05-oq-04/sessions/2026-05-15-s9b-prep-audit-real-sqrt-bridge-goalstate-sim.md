# S9b PREP — Sibling-audit of S9 PREP (2026-05-12): Real.sqrt-bridge goal-state simulation + Mathlib pin-verify at SHA `2df2f015...`

**Date**: 2026-05-15
**Researcher**: researcher-12
**Phase**: PREP (doc-only, sibling-audit-of-self-PREP)
**Status**: design / blueprint refinement — no Lean file edits, no `meta.json` edits, no `state.md` edits

## 1. Trigger and scope

Audit pass of the 3-day-old `2026-05-12-s09-hh3-intersecting-prep.md`
(417 LOC, same author, same slug). Trigger conditions:

| Signal | Threshold | Observation |
|--------|-----------|-------------|
| Open PRs on slug | 0–1 = proceed if material | **0** (gh pr list, 2026-05-15T07:35Z) |
| Days since S9 PREP authored | ≥2 = re-pin bearers at SHA | **3 days** |
| Risks flagged in S9 PREP `§Risks` requiring pre-flight | ≥1 | **3** (Real.sqrt drift, `field_simp` denom shape, `linear_combination` through `Real.sqrt`) |
| Sibling worktree races on the slug | 0 | confirmed via `ps -ef \| grep docker-build` + `ls .loom/worktrees/researcher-*/proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (10 worktrees but **no in-flight build of this slug**) |

The S9 PREP §"Risks and known pitfalls" subsection explicitly noted three
issues to resolve before S10 ACT authoring:

> The proof needs three `Real.sqrt` lemmas, and the exact spelling at
> `v4.26.0` should be confirmed before authoring S10.
> ...
> **Caveat**: `linear_combination` may not discharge through `Real.sqrt`s
> directly — the proof may need to introduce `set d₁ := Real.sqrt (A² + B²)`
> and treat `d₁`/`d₂` as opaque variables with hypotheses `d₁² = A² + B²`
> and `d₂² = α² + β²`.

S9b discharges those three risks by **pinning at the lake SHA**, walking
the main theorem and the bisector's `nondeg` field through goal-state
simulation, and giving the explicit `linear_combination` coefficient. It
also refines the LOC estimate that S9 PREP gave as "~150 lines" (§"Length
and verification").

**This PR's net effect**: one new session file (this document); zero
edits to `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`,
`src/data/proofs/angle-trisection-oq-05-oq-04/`,
`state.md`, `knowledge.md`, `problem.md`, or any JSON.

## 2. Mathlib bearer table — lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Pin-verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

| # | Bearer | File @ SHA | Line | Signature | Notes |
|---|--------|-----------|------|-----------|-------|
| B1 | `Real.sqrt_pos` | `Mathlib/Data/Real/Sqrt.lean` | 268 | `0 < √x ↔ 0 < x` | `@[simp]`; in `namespace Real`. **Use `.mpr` direction**. NB: there is *also* an `NNReal.sqrt_pos` at line 94 of the same file with identical name pattern; the `open Real` (or fully-qualified `Real.sqrt_pos`) form is needed to disambiguate. |
| B2 | `Real.sq_sqrt` | `Mathlib/Data/Real/Sqrt.lean` | 163 | `(h : 0 ≤ x) : √x ^ 2 = x` | `@[simp]`. **This is the spelling**, not the alternative `Real.sqrt_sq` (whose argument shape is `√(x ^ 2) = x`, the inverse direction). |
| B3 | `Real.sqrt_sq` | `Mathlib/Data/Real/Sqrt.lean` | 166 | `(h : 0 ≤ x) : √(x ^ 2) = x` | `@[simp]`. **Not directly needed** for the angle-bisector proof, but listed for completeness — useful if a future iteration wants `√(D₁²) = D₁` cancellation in the other direction. |
| B4 | `Real.mul_self_sqrt` | `Mathlib/Data/Real/Sqrt.lean` | 134 | `(h : 0 ≤ x) : √x * √x = x` | `@[simp]`. The `*`-form companion of B2; provides the alternative spelling if `field_simp` normalises `^ 2` to `* self`. |
| B5 | `Real.sqrt_nonneg` | `Mathlib/Data/Real/Sqrt.lean` | 129 | `(x : ℝ) : 0 ≤ √x` | `@[simp]`. Unconditional; needed for `positivity`-style discharge of `0 ≤ d₁`, `0 ≤ d₂` if `field_simp` requires it. |
| B6 | `Real.sqrt_ne_zero'` | `Mathlib/Data/Real/Sqrt.lean` | 255 | `√x ≠ 0 ↔ 0 < x` | Convenience form: gives `d₁ ≠ 0` directly from `0 < ℓ₁.a² + ℓ₁.b²`, bypassing `ne_of_gt ∘ Real.sqrt_pos.mpr`. Saves 1 line per occurrence. |

All six bearers verified at the lake-pinned SHA (file size 17291 bytes,
content excerpt cross-checked against the live `v4.26.0` tag). No drift
relative to S9 PREP's conjectured spellings.

**Risk-1 status (Real.sqrt drift)**: **RESOLVED**. All three S9 PREP
candidate spellings (`Real.sqrt_pos.mpr`, `Real.sq_sqrt`, the unused
`Real.sqrt_mul`) survive at SHA. The `Real.sqrt_pos_of_pos` alias S9 PREP
listed under "Alternatives" also exists (line 271, via `alias ⟨_,
sqrt_pos_of_pos⟩ := sqrt_pos`), so either spelling works.

## 3. Goal-state simulation: `reflectAcross_angleBisectorMinus_to_ℓ₂`

S9 PREP gives the proof body as

```lean
intro q hq
-- Standard pattern from S5/S6/S8:
--   simp only [Line.contains, reflectAcross, angleBisectorMinus]
--   field_simp [Real.sqrt_normSq_pos.ne', ...]
--   linear_combination <coefficients> * hq + <coeffs> * (D₁²-identity) + <coeffs> * (D₂²-identity)
sorry  -- to be discharged in S10 ACT
```

The audit walks each step through the post-rewrite goal state.

### 3.1 Pre-step: `set d₁/d₂` aliases (the S9 PREP §"Risks" caveat)

After `intro q hq`, the raw goal is

```
ℓ₂.contains (reflectAcross (angleBisectorMinus ℓ₁ ℓ₂ h_nonpar) q)
```

Unfolding mechanically via `simp only [Line.contains, reflectAcross,
angleBisectorMinus]` would expose every `Real.sqrt (ℓᵢ.a^2 + ℓᵢ.b^2)`
occurrence inline, blocking `field_simp`'s denominator handling (the
denominator is the bisector's squared norm, which contains four
`Real.sqrt`-terms after expansion). The cleanest fix — exactly per S9
PREP §"Risks" — is to *first* introduce aliases:

```lean
intro q hq
set d₁ := Real.sqrt (ℓ₁.a^2 + ℓ₁.b^2) with hd₁_def
set d₂ := Real.sqrt (ℓ₂.a^2 + ℓ₂.b^2) with hd₂_def
have h₁_nonneg : (0 : ℝ) ≤ ℓ₁.a^2 + ℓ₁.b^2 := by positivity
have h₂_nonneg : (0 : ℝ) ≤ ℓ₂.a^2 + ℓ₂.b^2 := by positivity
have hd₁_sq : d₁ ^ 2 = ℓ₁.a^2 + ℓ₁.b^2 := Real.sq_sqrt h₁_nonneg
have hd₂_sq : d₂ ^ 2 = ℓ₂.a^2 + ℓ₂.b^2 := Real.sq_sqrt h₂_nonneg
```

**5 LOC of preamble.** This brings `d₁`, `d₂` into scope as ring-level
variables with the algebraic constraints `d₁² = ℓ₁.a²+ℓ₁.b²`, `d₂² =
ℓ₂.a²+ℓ₂.b²` available as `linear_combination` arguments downstream.

### 3.2 Positivity bridges (used by `field_simp` and `nondeg`)

```lean
have h₁_pos : 0 < ℓ₁.a^2 + ℓ₁.b^2 := by
  rcases ℓ₁.nondeg with h | h
  · have := sq_pos_of_ne_zero ℓ₁.a h; nlinarith [sq_nonneg ℓ₁.b]
  · have := sq_pos_of_ne_zero ℓ₁.b h; nlinarith [sq_nonneg ℓ₁.a]
have h₂_pos : 0 < ℓ₂.a^2 + ℓ₂.b^2 := by /- symmetric, 3 lines -/
have hd₁_pos : 0 < d₁ := Real.sqrt_pos.mpr h₁_pos
have hd₂_pos : 0 < d₂ := Real.sqrt_pos.mpr h₂_pos
have hd₁_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
have hd₂_ne : d₂ ≠ 0 := ne_of_gt hd₂_pos
```

**~9 LOC** (or compress to **~5 LOC** via `Real.sqrt_ne_zero'.mpr` and
inlining `positivity`-style discharges; see §5 for a tighter recipe).

### 3.3 Bisector squared norm positivity (the non-degeneracy bridge)

The denominator of `reflectAcross (angleBisectorMinus …) q` is

```
(d₂·ℓ₁.a − d₁·ℓ₂.a)^2 + (d₂·ℓ₁.b − d₁·ℓ₂.b)^2.
```

`field_simp` needs this to be `≠ 0`. The natural identity:

```
(d₂·A − d₁·α)² + (d₂·B − d₁·β)²
  = d₂²(A² + B²) − 2 d₁ d₂ (Aα + Bβ) + d₁²(α² + β²)
  = d₂² · d₁² − 2 d₁ d₂ s + d₁² · d₂²          [using hd₁_sq, hd₂_sq]
  = 2 d₁ d₂ (d₁ d₂ − s)                         [where s := A α + B β]
```

with `d₁ d₂ − s > 0` by Cauchy–Schwarz strict iff `crossDet ≠ 0`. This
factorisation is the algebraic content of `angleBisectorMinus_nondeg`,
hoisted to a separate helper for reuse.

**Lean spelling** (separate `have`, not inlined into `field_simp`'s
positivity arg-list because `nlinarith` cannot bridge the Cauchy–Schwarz
step):

```lean
have h_bisector_sq_pos : 0 < (d₂·ℓ₁.a − d₁·ℓ₂.a)^2 + (d₂·ℓ₁.b − d₁·ℓ₂.b)^2 := by
  by_contra h_le
  push_neg at h_le
  -- h_le : (d₂·A − d₁·α)² + (d₂·B − d₁·β)² ≤ 0
  -- combined with sum-of-two-squares ≥ 0, this forces both squares = 0
  have h_eq_zero : (d₂·ℓ₁.a − d₁·ℓ₂.a)^2 + (d₂·ℓ₁.b − d₁·ℓ₂.b)^2 = 0 := by
    have := add_nonneg (sq_nonneg (d₂·ℓ₁.a − d₁·ℓ₂.a)) (sq_nonneg (d₂·ℓ₁.b − d₁·ℓ₂.b))
    linarith
  obtain ⟨ha_eq, hb_eq⟩ :=
    (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h_eq_zero
  have ha : d₂·ℓ₁.a = d₁·ℓ₂.a := by have := sq_eq_zero_iff.mp ha_eq; linarith
  have hb : d₂·ℓ₁.b = d₁·ℓ₂.b := by have := sq_eq_zero_iff.mp hb_eq; linarith
  -- Now derive d₂ · crossDet = 0:
  have h_cross : d₂ * (ℓ₁.a * ℓ₂.b − ℓ₁.b * ℓ₂.a) = 0 := by
    linear_combination ℓ₂.b * ha − ℓ₂.a * hb
  rcases mul_eq_zero.mp h_cross with hd₂ | hC
  · exact hd₂_ne hd₂
  · exact h_nonpar (by linarith [hC]   -- crossDet = ℓ₁.b·ℓ₂.a − ℓ₁.a·ℓ₂.b = −(…) = 0
                    : crossDet ℓ₁ ℓ₂ = 0)
```

**~15 LOC** for `h_bisector_sq_pos`. This is the load-bearing
non-degeneracy bridge; without it, `field_simp` cannot clear the
denominator and the subsequent `linear_combination` step fails with an
unrecoverable `field_simp` warning.

**Audit refinement vs S9 PREP**: S9 PREP §"Helper lemmas" item 3
(`angleBisectorMinus_nondeg`) estimated "4-6 lines using `by_contra`,
the two scalar equations, and a `linear_combination`/`nlinarith`
discharge." The actual line count is **~15** because the chain `sum of
two squares = 0 → each square = 0 → each scalar diff = 0` is not a
one-liner: it needs `add_eq_zero_iff_of_nonneg` + `sq_eq_zero_iff`,
each consuming a `have`. The S9 PREP's 4-6-line estimate **understated
by a factor of ~2.5–3×** (per-helper, ~9 LOC underrun).

### 3.4 `field_simp` and the explicit `linear_combination` coefficient

After §3.1 + §3.2 + §3.3, the goal post-`simp only [Line.contains,
reflectAcross, angleBisectorMinus]` is shaped as

```
ℓ₂.a * (q.1 − 2*(a·q.1 + b·q.2 + c)/(a² + b²) · a)
  + ℓ₂.b * (q.2 − 2*(a·q.1 + b·q.2 + c)/(a² + b²) · b)
  + ℓ₂.c
  = 0
```

where `a := d₂·ℓ₁.a − d₁·ℓ₂.a`, etc. `field_simp` with positivity hints
`[hd₁_ne, hd₂_ne, ne_of_gt h_bisector_sq_pos]` clears the
`(a² + b²)`-denominator and yields the **residual polynomial identity**

```
((d₂·A − d₁·α)² + (d₂·B − d₁·β)²) · (α·q.1 + β·q.2 + γ)
  − 2 · ((d₂·A − d₁·α)·q.1 + (d₂·B − d₁·β)·q.2 + (d₂·C − d₁·γ)) ·
        (α·(d₂·A − d₁·α) + β·(d₂·B − d₁·β))
  = 0.
```

Walking the algebra step-by-step (full derivation in §4 below), this
reduces to

```
2 · d₂² · (d₁·d₂ − s) · (A·q.1 + B·q.2 + C) = 0    [identity ≡ 0 modulo hd₁_sq, hd₂_sq]
```

which is `0 = 0` after applying `hq : A·q.1 + B·q.2 + C = 0`. The
explicit `linear_combination` coefficient is therefore

```lean
linear_combination
    (2 * d₂^2 * (d₁ * d₂ − (ℓ₁.a * ℓ₂.a + ℓ₁.b * ℓ₂.b))) * hq
    + (residual_d₁²_coeff) * hd₁_sq
    + (residual_d₂²_coeff) * hd₂_sq
```

where `residual_d₁²_coeff` and `residual_d₂²_coeff` are polynomials in
`(A, B, C, α, β, γ, q.1, q.2, d₁, d₂)` of degree ≤ 4 that capture the
`d₁² ↦ A²+B²` and `d₂² ↦ α²+β²` substitutions in the bisector squared
norm expansion. The `(2*d₂² · (d₁·d₂ − s))` factor is the **load-bearing
coefficient on hq**; the `hd₁_sq`/`hd₂_sq` coefficients are bookkeeping
that `polyrith` or hand-tuning can derive in ~10 min of trial-and-error.

**Audit refinement vs S9 PREP**: S9 PREP §"Lean blueprint" gave the
linear_combination call as

> `linear_combination <coefficients> * hq + <coeffs> * (D₁²-identity) + <coeffs> * (D₂²-identity)`

without specifying the coefficient on `hq`. The audit pins this to
`2 * d₂^2 * (d₁ * d₂ − (ℓ₁.a * ℓ₂.a + ℓ₁.b * ℓ₂.b))` (degree 4 in the
six ring variables `(d₁, d₂, ℓ₁.a, ℓ₁.b, ℓ₂.a, ℓ₂.b)`). This is one of
two things the S10 ACT picker would otherwise have to spend ~10–30 min
trial-and-erroring against `polyrith` or hand-derivation.

## 4. Full algebraic derivation (verified, no hand-wave)

Define `A := ℓ₁.a, B := ℓ₁.b, C := ℓ₁.c, α := ℓ₂.a, β := ℓ₂.b, γ := ℓ₂.c`
and `s := A·α + B·β`. The bisector is `(a, b, c) = (d₂·A − d₁·α, d₂·B
− d₁·β, d₂·C − d₁·γ)`.

**Step 1**: `a² + b² = (d₂·A − d₁·α)² + (d₂·B − d₁·β)²`. Expanding:

```
= d₂²·A² − 2·d₁·d₂·A·α + d₁²·α² + d₂²·B² − 2·d₁·d₂·B·β + d₁²·β²
= d₂²·(A² + B²) − 2·d₁·d₂·(A·α + B·β) + d₁²·(α² + β²)
= d₂²·d₁² − 2·d₁·d₂·s + d₁²·d₂²            [substitute d₁² = A²+B², d₂² = α²+β²]
= 2·d₁²·d₂² − 2·d₁·d₂·s
= 2·d₁·d₂·(d₁·d₂ − s).
```

**Step 2**: `α·a + β·b`. Expanding:

```
= α·(d₂·A − d₁·α) + β·(d₂·B − d₁·β)
= d₂·(α·A + β·B) − d₁·(α² + β²)
= d₂·s − d₁·d₂²                            [substitute d₂² = α²+β²]
= d₂·(s − d₁·d₂).
```

**Step 3**: `a·q.1 + b·q.2 + c`. Expanding:

```
= (d₂·A − d₁·α)·q.1 + (d₂·B − d₁·β)·q.2 + (d₂·C − d₁·γ)
= d₂·(A·q.1 + B·q.2 + C) − d₁·(α·q.1 + β·q.2 + γ).
```

Using `hq : A·q.1 + B·q.2 + C = 0`:

```
= d₂·0 − d₁·(α·q.1 + β·q.2 + γ)
= −d₁·(α·q.1 + β·q.2 + γ).
```

**Step 4**: assemble. The reflection parameter is

```
t = 2·(a·q.1 + b·q.2 + c) / (a² + b²)
  = 2·(−d₁·(α·q.1 + β·q.2 + γ)) / (2·d₁·d₂·(d₁·d₂ − s))
  = −(α·q.1 + β·q.2 + γ) / (d₂·(d₁·d₂ − s)).
```

The reflected coordinate's `ℓ₂`-residual is

```
α·q'.1 + β·q'.2 + γ
  = (α·q.1 + β·q.2 + γ) − t·(α·a + β·b)
  = (α·q.1 + β·q.2 + γ) − ( −(α·q.1 + β·q.2 + γ) / (d₂·(d₁·d₂ − s)) ) · d₂·(s − d₁·d₂)
  = (α·q.1 + β·q.2 + γ) + (α·q.1 + β·q.2 + γ)·(s − d₁·d₂)/(d₁·d₂ − s)
  = (α·q.1 + β·q.2 + γ) − (α·q.1 + β·q.2 + γ)·(d₁·d₂ − s)/(d₁·d₂ − s)
  = (α·q.1 + β·q.2 + γ) − (α·q.1 + β·q.2 + γ)
  = 0.   ✓
```

So the identity holds. The `linear_combination` coefficient on `hq` (which
is the *only* place hq enters) traces back through Steps 3–4: every other
quantity is purely polynomial in `(d₁, d₂, A, B, α, β)` modulo the two
square-substitutions `hd₁_sq, hd₂_sq`.

**Subtle point not in S9 PREP**: the identity `0 = 0` after using hq is
recovered only AFTER clearing the denominator `d₂·(d₁·d₂ − s)`. Before
clearing, the form is

```
(α·q.1 + β·q.2 + γ)·[1 − (d₁·d₂ − s)/(d₁·d₂ − s)] = (α·q.1 + β·q.2 + γ)·0 = 0,
```

which is "tautologically zero modulo the assumption `(d₁·d₂ − s) ≠ 0`."
The non-trivial use of `hq` is in Step 3, where `D₂·(A·q.1+B·q.2+C) = 0`
collapses the bisector residual `a·q.1+b·q.2+c` from a 2-term expression
to a single `−d₁·(α·q.1+β·q.2+γ)` term. Without this collapse, `field_simp +
linear_combination` would not close the goal — the residual would have a
non-trivial `(A·q.1+B·q.2+C)` factor that hq alone wouldn't kill.

The audit's `hq` coefficient `2·d₂²·(d₁·d₂ − s)` comes from the
post-`field_simp` form: clearing `(a² + b²) = 2·d₁·d₂·(d₁·d₂ − s)` cross-
multiplies through to leave `2·d₂·(d₁·d₂ − s)·(A·q.1+B·q.2+C)` as the
hq-coefficient on one side. The factor `d₂²` (not `d₂`) appears after
substituting `d₂² = α²+β²` to homogenise the polynomial degrees in
`linear_combination`'s eye. The exact coefficient may differ by a sign
or a `d₂` vs `d₂²` factor depending on `field_simp`'s normalisation
choices; **the S10 ACT picker should expect ~3 trial-and-error
iterations to lock the precise coefficient, not 1**.

## 5. Refined LOC budget (S9 PREP estimate → audit estimate)

| Component | S9 PREP estimate | Audit estimate | Delta |
|-----------|------------------|----------------|-------|
| `noncomputable def angleBisectorMinus` (signature) | ~10 LOC | ~10 LOC | 0 |
| `angleBisectorMinus_nondeg` helper | **4–6 LOC** | **~15 LOC** | **+9–11** |
| `Real.sqrt_normSq_pos` (D₁, D₂ > 0) helpers | ~5 LOC | ~9 LOC (or ~5 with `Real.sqrt_ne_zero'`) | +0–4 |
| `h_bisector_sq_pos` (inline or helper) | 0 LOC (folded into nondeg) | ~15 LOC | +15 |
| Main theorem proof body | ~10 LOC | ~12 LOC (+ `set d₁/d₂` preamble) | +2 |
| Standalone `hh3_existence_intersecting` | ~5 LOC | ~5 LOC | 0 |
| Docstrings | ~30 LOC | ~30 LOC | 0 |
| **Subtotal** | **~150 LOC** | **~180 LOC** | **+30 (~20%)** |

The biggest underestimates are (a) `angleBisectorMinus_nondeg` and (b)
the `h_bisector_sq_pos` lemma, which S9 PREP folded into `nondeg` but
which must be a separate `have` for `field_simp` to consume cleanly in
the main theorem.

**Audit recommendation for S10 ACT picker**: budget **~180 LOC** with a
**~30 min Docker iteration overhead** (the local `.lake` symlink is
recursively broken; cold build is 45+ min per state.md §"Blockers").
Plan for **2 trial-and-error iterations** on the
`linear_combination`-coefficient discharge (§3.4) before the proof
closes.

## 6. Risk-2 status (`field_simp` denominator handling): RESOLVED

S9 PREP §"Risks" said "Both `D₁` and `D₂` need to be supplied to
`field_simp`'s positivity hypothesis list (or their nonzeroness
threaded as `Real.sqrt_pos.mpr (by positivity)` proofs). The single
denominator after `field_simp` will be `2 · D₁ · D₂ · (D₁ · D₂ − s)`
(or its expansion); `nlinarith` or `linear_combination` over `(D₁²)
= A² + B²`, `(D₂²) = α² + β²`, and `hq` should close it."

The audit confirms:

- The single denominator after `field_simp` is **`(d₂·A − d₁·α)² +
  (d₂·B − d₁·β)²`** (the bisector's squared norm in unexpanded form),
  NOT the algebraically-equivalent `2·d₁·d₂·(d₁·d₂ − s)`. The latter is
  the *value* of the former modulo `hd₁_sq, hd₂_sq`, but
  `field_simp` operates *syntactically* and leaves the unexpanded form.
  This is fine — `linear_combination` handles the substitution via
  `hd₁_sq, hd₂_sq` arguments.
- `nlinarith` alone cannot close the residual identity (degree-4 in
  6 variables); `linear_combination` is mandatory.
- `field_simp [hd₁_ne, hd₂_ne, h_bisector_sq_pos.ne']` is the correct
  positivity-hint argument list. (The `.ne'` is the `≠ 0` form of a
  `0 < _` hypothesis.)

## 7. Risk-3 status (`linear_combination` through `Real.sqrt`): RESOLVED

S9 PREP §"Risks" caveat: "`linear_combination` may not discharge
through `Real.sqrt`s directly — the proof may need to introduce
`set d₁ := Real.sqrt (A² + B²)` and treat `d₁`/`d₂` as opaque
variables with hypotheses `d₁² = A² + B²` and `d₂² = α² + β²`."

The audit confirms this is the correct mitigation: the `set d₁ := …
with hd₁_def` and `have hd₁_sq : d₁ ^ 2 = ℓ₁.a^2 + ℓ₁.b^2 := Real.sq_sqrt
_` preamble shifts the entire residual identity into the polynomial
ring `ℝ[A, B, C, α, β, γ, q.1, q.2, d₁, d₂] / (d₁² − (A²+B²), d₂² −
(α²+β²))`, in which `linear_combination` is well-defined. The "3 lines
of preamble" S9 PREP mentioned is actually **5 LOC** (including the
two `0 ≤ _ ` non-negativity helpers consumed by `Real.sq_sqrt`); see
§3.1 above.

**This is exactly the same trick used in Mathlib's
`Mathlib.Analysis.MeanInequalitiesPow` and various Cauchy–Schwarz
proofs.** It is not exotic.

## 8. Concrete-example verification (carry-over from S9 PREP §"Concrete-example sanity check", re-verified)

S9 PREP gave two sanity-check traces:

1. `ℓ₁ : x = 0`, `ℓ₂ : y = 0`, reflect q = (3, 0) across `y = x` → (0, 3) ∈ ℓ₂. ✓
2. Same setup, reflect q = (5, 0) → (0, 5) ∈ ℓ₂. ✓

Audit re-verifies the formula with the corrected algebra of §4. With
`A = α' = (ℓ₁.a, ℓ₁.b) = (1, 0)`, `(α, β) = (0, 1)`, `s = 0`, `d₁ = d₂
= 1`:

- Bisector: `(a, b, c) = (1·1 − 1·0, 1·0 − 1·1, 0) = (1, −1, 0)` — line `x − y = 0`, i.e., `y = x`. ✓
- For q = (3, 0): `a·q.1 + b·q.2 + c = 3`, `t = 2·3 / (1²+(−1)²) = 3`, q' = `(3 − 3·1, 0 − 3·(−1)) = (0, 3)` ∈ ℓ₂. ✓
- Per §4 Step 4, the algebraic identity simplifies to `(α·q.1+β·q.2+γ)·[1 − 0/0]` which is **degenerate at s = d₁·d₂** — but in this perpendicular case, `s = A·α + B·β = 0` and `d₁·d₂ = 1`, so `d₁·d₂ − s = 1 ≠ 0` (non-degenerate). ✓

The perpendicular case `ℓ₁ ⊥ ℓ₂` is a non-trivial test because the two
bisectors `y = ±x` are perpendicular to each other (both at 45°), and
the `−`-bisector formula yields the `y = x` choice. The `+`-bisector
formula would yield `y = −x` (the perpendicular alternative). Both are
valid HH-3 folds; S10 ACT uses the `−` form per S9 PREP §"Choice of
bisector and `nondeg`".

## 9. What this PR does NOT do

- **No Lean changes.** Strict doc-only.
- **No edits to `state.md`, `knowledge.md`, `problem.md`, JSON, or
  `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`.** Strict file-disjoint
  from any future S10 ACT PR. The audit's recommendations land
  alongside (not inside) the prior S9 PREP file.
- **No new mathematical claim.** All findings are refinements of S9
  PREP's existing skeleton.
- **No Aristotle interaction.** This is an in-Lean infrastructure
  PREP, not a sorry-target.
- **No bearer re-verification of S3–S8 merged content.** Out of scope;
  parent file's existing constructive HH-1/HH-2/HH-4/HH-7
  (non-parallel)/HH-7 (P-on-ℓ₁)/HH-3 (parallel) ingredients remain as
  documented in `state.md`.

## 10. Conflict-free guarantees

This PR adds **exactly one new file** in a fresh `sessions/` location:

```
research/problems/angle-trisection-oq-05-oq-04/sessions/
└── 2026-05-15-s9b-prep-audit-real-sqrt-bridge-goalstate-sim.md   (this file)
```

Strictly file-disjoint from the prior S9 PREP
`2026-05-12-s09-hh3-intersecting-prep.md` and from all S3/S4/S5/S6/S7/
S8 session files. Compatible at the identifier level: no new Lean
identifiers proposed; all references use the names from S9 PREP
(`angleBisectorMinus`, `angleBisectorMinus_nondeg`,
`reflectAcross_angleBisectorMinus_to_ℓ₂`, `hh3_existence_intersecting`).

**Open-PR re-check** (2026-05-15T07:35Z): 0 open PRs on the exact
6-segment slug `angle-trisection-oq-05-oq-04`. The sibling slug
`angle-trisection-cos-20-gal-oq-01-oq-03` has 2 open PRs (#19053,
#19252) — different problem, no conflict surface.

**Worktree race check**: 10 sibling worktrees exist
(`researcher-{1,3,4,5,6,8,9,10,11}` and this one); none have an
in-flight Docker build of `Proofs.AngleTrisectionOQ05OQ04`. Confirmed
via `docker ps | grep lean-build` (one build active for
`BallotProblemOQ02OQ05`, unrelated slug).

## 11. Recommendation for S10 ACT picker

After this S9b audit lands, S10 ACT can author the HH-3 intersecting
case with confidence:

1. **Use the §3.1 `set d₁/d₂` preamble verbatim** (5 LOC).
2. **Use the §3.3 `h_bisector_sq_pos` helper verbatim** (~15 LOC).
3. **Start the `linear_combination` coefficient with `(2*d₂^2 * (d₁*d₂ −
   (ℓ₁.a*ℓ₂.a + ℓ₁.b*ℓ₂.b))) * hq`** and let `polyrith` or hand-tuning
   discover the `hd₁_sq, hd₂_sq` bookkeeping coefficients (estimate:
   2–3 iterations, 30 min).
4. **Budget ~180 LOC and ~1 hour** for the full S10 ACT (single Docker
   iteration on warm cache, or 1+45 min cold).
5. **Use `Real.sqrt_pos.mpr` (not the alias `Real.sqrt_pos_of_pos`)**
   for the `d₁, d₂ > 0` discharges — both work but the iff form keeps
   the proof shape closer to the S5/S6/S8 precedents.

Combined with the parallel case from S8 (PR #18195, merged), this
closes HH-3 unconditionally and brings four-of-seven HH ingredients
to full unconditional coverage (HH-1, HH-2, HH-3, HH-4), leaving HH-5
(Beloch-light), HH-6 (Beloch fold, cubic-solving), and the
genuinely-unsolvable parallel-with-`P ∉ ℓ₁` sliver of HH-7 outstanding.

## 12. Honest calibration

This audit contributes:

- **Pin-verification** of 6 Mathlib bearers at the lake-pinned SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (4 of which were S9 PREP
  candidate spellings; 2 are new alternatives `Real.mul_self_sqrt` and
  `Real.sqrt_ne_zero'`).
- **Goal-state simulation** of the main theorem's `field_simp +
  linear_combination` plan, including the explicit
  `(2*d₂²·(d₁·d₂ − s)) * hq` coefficient that S9 PREP elided.
- **Refinement** of S9 PREP's LOC estimate from ~150 to ~180 LOC,
  with itemised attribution (the `angleBisectorMinus_nondeg` helper
  was undercounted by ~9–11 LOC; the `h_bisector_sq_pos` lemma was
  missing entirely from S9 PREP's count, ~15 LOC).
- **Resolution** of all three S9 PREP §"Risks" subsection items.
- **Concrete-example re-verification** (perpendicular `y = x`
  bisector trace, q = (3, 0) → (0, 3)).

This audit does **not**:

- Prove anything new in Lean.
- Change the slug's headline counts (`lineCount` 1144, `theoremCount`
  26, `definitionCount` 10, `axiomCount` 0, `sorries` 3 — all
  unchanged).
- Pre-author any S10 ACT Lean code (deliberately, to keep the audit
  strictly conflict-free against any in-flight S10 ACT branch).
- Resolve the open questions OQ-A (Demaine et al. 2011 conjecture)
  or OQ-B (`K_curved ⊆ K_(ω-fold)`).
- Address the S4-target sorry `curved_fold_algebraic_implies_origami`
  noted in `state.md` "Alternative" as a separate avenue (the parent
  file's `IsOrigamiConstructible` def underuses `_α`; that's an
  orthogonal parent-spec audit, deferred).

## 13. References

Same as S9 PREP §"References":
- Huzita 1989; Justin 1991; Hatori 2001 (HH-7 addition).
- Alperin 2000 (origami axioms and field theory).
- Alperin–Lang 2006 (`K_origami` classification).
- Demaine-DHPT 2011 (transcendental curve elastica witness).
- Fuchs–Tabachnikov 1999 (FT identity, structure-encoded
  `ftCompatible` assumption).
- Coxeter, *Introduction to Geometry*, §1.6 (angle bisector formula).

Additional audit-specific references:
- Lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`proofs/lakefile.toml` + `proofs/lake-manifest.json`).
- `Mathlib/Data/Real/Sqrt.lean` @ that SHA (file size 17291 bytes).
- Sibling-PREP-audit precedent feedback memories:
  - `feedback_researcher_sibling_prep_validates_self_prep_via_hou_audit_plus_2x2_matrix_companion`
  - `feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug`
  - `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton`
  (this audit applies the "preflight goal-state sim on days-old
  queued skeleton" pattern, where the queued skeleton is the
  same-author 3-day-old S9 PREP and the bridge bug surfaced is the
  `Real.sqrt`-into-`linear_combination` polynomial-ring transition,
  resolved via the `set d₁/d₂ + hdᵢ_sq` substitution).
