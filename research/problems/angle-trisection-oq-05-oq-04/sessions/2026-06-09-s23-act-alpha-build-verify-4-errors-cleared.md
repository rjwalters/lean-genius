# Session 23 — S23-α ACT: BUILD-VERIFY clears all 4 OQ04 errors

**Date**: 2026-06-09
**Researcher**: researcher-1 (claim `researcher-74962`)
**Mode**: ACT — full discharge of the residual OQ04 Mathlib-drift errors
**Outcome**: **PROGRESS — Docker BUILD-VERIFY GREEN, 0 errors, parent file 1144 → 1148 LOC (+4 net)**

---

## 0. Baseline at S23 picker

After claiming `angle-trisection-oq-05-oq-04` (researcher-74962, knowledge
score 256 RICH, depth-first), the S22 state.md table claimed the
post-S22 error state was:

| Line | Cat | Status |
|------|-----|---------|
| 499, 502 | A | GREEN (S22 cat-A repair) |
| 596, 597 | A | GREEN (S22 cat-A repair) |
| 642 | B | GREEN (cascade-resolved by cat-A) |
| 772 | B | GREEN (cascade-resolved by cat-A) |
| 782 (body) | C | GREEN (cascade-resolved by cat-A) |
| 1117 | B | **RED** — needs `field_simp [hS_ne, hS_ne']` + linear_combination re-derivation |

S23-α picker confirmed INFRA GREEN at T~18:30Z 2026-06-09:
- Docker 29.5.3 daemon up (`docker info --format '{{.ServerVersion}}'` exits 0)
- `/System/Volumes/Data` 88 Gi avail (well above 5.0 Gi gate)
- Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` stable ~28d
- 7727-olean cache valid

A **first Docker baseline run** at S23-α picker SHIPMENT-1 (before any
edits) revealed the real baseline is **4 errors, not 1**:

```
error: Proofs/AngleTrisectionOQ05OQ04.lean:642:2: ring failed, ring expressions not equal
error: Proofs/AngleTrisectionOQ05OQ04.lean:772:2: ring failed, ring expressions not equal
error: Proofs/AngleTrisectionOQ05OQ04.lean:782:67: unsolved goals
error: Proofs/AngleTrisectionOQ05OQ04.lean:1117:2: ring failed, ring expressions not equal
```

**S22's claim that L642, L772, L782 cascade-resolved by the cat-A repair is
EMPIRICALLY FALSE.** Three additional errors must be addressed. The
likely cause is that the S22 Docker re-verification ran against a stale
`.olean` cache that didn't re-elaborate downstream theorems after the
cat-A `_` removals. The S22 PR shipped its tracker update on this stale
verification.

## 1. The four-fix recipe

### 1.1 L642 — `reflectAcross_perpThroughPoint_preserves`

**Diagnosis**: post-`field_simp` residual is `(1 − D)·hq_expr` where
`D = ℓ.a² + ℓ.b²` and `hq_expr = ℓ.a·q.1 + ℓ.b·q.2 + ℓ.c`. The original
coefficient `((-ℓ.b)^2 + ℓ.a^2) = D` doesn't match — the actual
post-field_simp goal is just `hq_expr = 0` (no D scaling). Mathlib
v4.26.0's `field_simp` cancels denominators differently than the version
S5 ACT was written against.

**Fix** (1 LOC): change `linear_combination ((-ℓ.b)^2 + ℓ.a^2) * hq` →
`linear_combination hq`.

### 1.2 L772 — `reflectAcross_hatoriFold_preserves_ℓ₂`

**Diagnosis**: post-`field_simp` residual is `(crossDet ℓ₁ ℓ₂ − 1) · hq_expr`
where `hq_expr = ℓ₂.a·q.1 + ℓ₂.b·q.2 + ℓ₂.c`. `field_simp` introduced a
`crossDet ℓ₁ ℓ₂` factor (from `hatoriFold.c`'s `/(2·crossDet)`
denominator) but the existing coefficient `((-ℓ₂.b)^2 + ℓ₂.a^2) = D₂`
doesn't account for it.

**Fix** (2 edits): pass `h_nonpar` to `field_simp` and use `crossDet ℓ₁ ℓ₂`
as the linear_combination coefficient:
- `field_simp` → `field_simp [h_nonpar]`
- `linear_combination ((-ℓ₂.b)^2 + ℓ₂.a^2) * hq` → `linear_combination (crossDet ℓ₁ ℓ₂) * hq`

### 1.3 L782 — `reflectAcross_hatoriFold_to_ℓ₁`

**Diagnosis**: two compounding issues.

1. **Inverse-denominator clearing**: residual still contains
   `(ℓ₂.b^2 + ℓ₂.a^2)⁻¹` because `hDpos : ℓ₂.a^2 + ℓ₂.b^2 ≠ 0` has the
   commuted form. Add a commuted variant `hDpos'` and pass to field_simp.

2. **Atom-mismatch on `crossDet ℓ₁ ℓ₂`**: keeping `crossDet` un-unfolded
   in `simp only` (so `h_nonpar` can match the denominator) leaves
   `crossDet ℓ₁ ℓ₂` as an opaque function-call atom in the post-field_simp
   polynomial. The residual factors as
   `crossDet · D₂ · (ℓ₁.a·p.1 + ℓ₁.b·p.2 + ℓ₁.c) − (ℓ₁.b·ℓ₂.a − ℓ₁.a·ℓ₂.b) · D₂ · (...)`
   — these should cancel since `crossDet ℓ₁ ℓ₂ = ℓ₁.b·ℓ₂.a − ℓ₁.a·ℓ₂.b`, but
   `ring` treats the two as distinct atoms. **Unfolding `crossDet` AFTER
   `field_simp`** restores the cancellation.

**Fix** (4 edits):
- Add `have hDpos' : ℓ₂.b^2 + ℓ₂.a^2 ≠ 0 := by rw [add_comm]; exact hDpos`
- Remove `crossDet` from `simp only` (keep it as a function call so
  `h_nonpar : crossDet ℓ₁ ℓ₂ ≠ 0` matches directly)
- Replace `at h_nonpar ⊢` with `at ⊢` (no longer rewriting h_nonpar)
- `field_simp` → `field_simp [h_nonpar, hDpos, hDpos']`
- Insert `simp only [crossDet]` between `field_simp` and `ring` (unfolds
  `crossDet` only in the residual polynomial, where ring needs it to see
  the cancellation)

### 1.4 L1117 — `reflectAcross_parallelBisector_to_ℓ₂` (the original S23-α target)

**Diagnosis**:
1. The S22 PR diagnosed that `field_simp` doesn't recognize the commuted
   form `ℓ₂.a · ℓ₁.a + ℓ₁.b · ℓ₂.b` (= `s'`) as a denominator, leaving
   `s'⁻¹` factors un-cleared. S22's recipe (add `hS_ne'`, pass both to
   `field_simp`) verified that part of the fix.

2. With both `hS_ne` and `hS_ne'` in field_simp, the post-field_simp goal
   is `(2s · D₁) · Goal = 0`, but the existing linear_combination
   coefficients `(-2s) · hq + 2(b₁q.1 − a₁q.2) · h_cross` no longer match.

**Coefficient re-derivation** via `parallelNormal_left_id` /
`parallelNormal_right_id`:

The scaling identities yield (under `h_cross`):
- `D₁ · ℓ₂.a = s · ℓ₁.a + ℓ₁.b · h_cross_expr`
- `D₁ · ℓ₂.b = s · ℓ₁.b − ℓ₁.a · h_cross_expr`

So:
```
D₁ · (ℓ₂.a · q.1 + ℓ₂.b · q.2)
  = s · (ℓ₁.a · q.1 + ℓ₁.b · q.2) + (ℓ₁.b · q.1 − ℓ₁.a · q.2) · h_cross_expr
  = s · (hq_expr − ℓ₁.c) + (ℓ₁.b · q.1 − ℓ₁.a · q.2) · h_cross_expr
```

The full reflection identity reduces to:
**D₁ · Goal = −s · hq_expr + (ℓ₁.b · q.1 − ℓ₁.a · q.2) · h_cross_expr**

`field_simp [hS_ne, hS_ne']` empirically scales by `s · D₁` (not
`2s · D₁` — the factor `2` is treated as a unit and dropped), so the
post-field_simp goal is:
**s · D₁ · Goal = −s² · hq_expr + s · (ℓ₁.b · q.1 − ℓ₁.a · q.2) · h_cross_expr**

So K1 = −s², K2 = s · (b₁ q.1 − a₁ q.2).

**Fix** (5 edits):
- Add `have hS_ne' : ℓ₂.a * ℓ₁.a + ℓ₁.b * ℓ₂.b ≠ 0 := by rw [mul_comm ℓ₂.a ℓ₁.a]; exact hS_ne`
- `field_simp` → `field_simp [hS_ne, hS_ne']`
- Replace linear_combination coefficient `(-2 * s)` → `(-(s)^2)` for hq term
- Replace linear_combination coefficient `(2 * (...))` → `(s * (...))` for h_cross term

## 2. Docker iteration log

| Iter | Edits | Errors after | Diff vs prior |
|------|-------|--------------|---------------|
| Baseline | none | 4 (L642, L772, L782, L1117) | (n/a) |
| 1 | L642 + L772 changed to `linear_combination hq` (coef 1 guess) | 3 (L772 still ring-fail, L782 still inverse, L1117 still ring-fail) | L642 closed |
| 2 | L772 `crossDet * hq` + L782 `[h_nonpar, hDpos]` + L1117 `(2−s)·s` coefficient | 3 (L772 still fail: missing crossDet pass-through, L782 still inverse, L1117 ring-fail) | (regression) |
| 3 | L772 keep `[h_nonpar]` + L1117 `−2s²` coefficient (algebraic 2sD₁ scaling guess) | 2 (L782 still inverse, L1119 ring-fail) | L772 closed |
| 4 | L782 add hDpos' + simp_only crossDet after field_simp + L1117 reduce to `−s²` (residual c₁ analysis showed factor 1 not 2) | **0 errors** | L782 + L1119 closed |

Wall-clock total ≈ 25 min hot-cache (5 iters × ~5 min/iter).

## 3. Empirical insights

### 3.1 S22's cascade-resolution claim was wrong

The S22 PR (`#22526`) shipped with the claim "cat-B at L642/L772 +
cat-C at L782 cascade-resolved by cat-A". S23 cold-cache build proves
this is FALSE — those errors persist independently. Lesson: `_` removal
fixes do not automatically propagate to downstream `ring` / `linear_combination`
sites under Mathlib v4.26.0's `field_simp` behavior change.

The likely mechanism: S22's Docker run used a partially-cached `.olean`
chain where the cat-A theorems re-elaborated but their downstream
dependents (L642, L772, L782) were re-replayed from cache, masking
their failures. S23's first build was on a fresh `.lake/build/` after
the file was edited — full re-elaboration exposed all 4 errors.

### 3.2 Mathlib v4.26.0 `field_simp` behavior

Three distinct manifestations of changed behavior surfaced:

1. **L642/L772**: `field_simp` no longer multiplies through by the
   simp_only-unfolded denominator `(-ℓ.b)^2 + ℓ.a^2`; the residual is
   `(1−D) · hq_expr` not `D · hq_expr`. Symptom: `linear_combination`
   coefficient `D` produces `−D · hq_expr` residual, off by sign.

2. **L772 (separate)**: `field_simp` without args doesn't auto-detect
   `crossDet ℓ₁ ℓ₂ ≠ 0` as a usable hypothesis even though `h_nonpar` is
   in scope. Must explicitly pass `[h_nonpar]`.

3. **L782/L1117**: `field_simp` requires the commuted form of compound
   denominators to be supplied explicitly via auxiliary hypothesis
   (`hDpos'`, `hS_ne'`) — the by-ring rewrite isn't applied at the
   denominator-matching step.

### 3.3 `crossDet` atom-mismatch in `ring`

When `crossDet ℓ₁ ℓ₂` survives field_simp as an opaque function call AND
the same expression also appears expanded as `ℓ₁.b·ℓ₂.a − ℓ₁.a·ℓ₂.b`,
`ring` sees them as distinct atoms and fails to combine them. Fix:
unfold `crossDet` AFTER `field_simp` via `simp only [crossDet]`. This
pattern recurs whenever a definition with a meaningful name is used as
both a hypothesis (in function-call form) and inside the post-field_simp
polynomial residual.

## 4. Empirical pattern for closed-form `linear_combination` derivation

For `reflectAcross_parallelBisector_to_ℓ₂` style theorems where the
post-`field_simp` residual is a degree-N polynomial in the line/point
variables, the systematic recipe is:

1. **Read the c₁ (free-coefficient) term** of the displayed residual.
   This is `(K1_true − provided_K1) · ℓ₁.c`.
2. **Solve for K1_true** from `c₁_observed = (K1_true − provided_K1)`.
3. **Re-derive K2** from a high-degree y term using the known K1_true:
   `residual_y = (K1_true − provided_K1) · b₁ + (K2_true − provided_K2) ·
   (−a₁ · h_cross_expr_in_y)`.

In our case, c₁_observed = `s² · c₁` (with provided K1 = `−2s²` in iter 4),
yielding K1_true = `−s²`. The iter 5 ship coefficient is exactly this.

## 5. Build inventory (post-S23)

```
proofs/Proofs/AngleTrisectionOQ05OQ04.lean
  1148 lines (was 1144; +4 net)
  0 axiom declarations
  26 theorems / lemmas (unchanged)
  10 noncomputable defs + 1 structure (unchanged)
  3 sorries (S3 / S4 / S5 targets — the 3 OQ open conjectures, unchanged)
  Docker build: GREEN (3059 jobs, hot cache ~10s)
```

5 ACT-merged HH ingredients (HH-1, HH-2, HH-4, HH-7 non-parallel,
HH-7 P-on-ℓ₁) and 1 newly-ACT-merged ingredient (**HH-3 parallel**)
move from "build pending / partial" to **build re-verified GREEN at
v4.26.0 Mathlib SHA 2df2f0150c…**. The Path C HH-6 same-directrix
paste (S24+) is now ungated by the L1117 RED blocker.

## 6. S24+ next action

With OQ04 file GREEN, the recommended next action is **S24 ACT — paste
the S16 PREP §5 paste-ready WLOG-frame Lean (~80 LOC + 1 sorry on the
reflection law)** at line 1148 (just before `end AngleTrisectionOQ05OQ04`).
See state.md §"Deferred — S24+: HH-6 same-directrix WLOG in Lean".

## 7. Honest calibration

This S23-α ACT:

- **Edits 1 Lean file** at 4 distinct sites (L642 / L772 / L782 / L1117)
  with surgical changes totaling +12/−8 LOC = +4 net.
- **Reduces OQ04 file errors 4 → 0** under Docker re-verification at
  Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **Promotes HH-3 parallel from RED to GREEN** + reaffirms HH-2 / HH-4 /
  HH-7 non-parallel / HH-7 P-on-ℓ₁ as GREEN at v4.26.0.
- Adds 0 sorries; closes 0 sorries (3 OQ targets at L207/L343/L399
  retained — these are the 3 open mathematical conjectures, not
  shippable Lean work).
- States 0 new theorems; resolves 0 of the 3 open mathematical
  conjectures.
- **Falsifies** S22 state.md's cascade-resolution claim with empirical
  Docker verification.
- Edits `state.md` (next iteration entry) +
  `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json` (lineCount 1144 → 1148) +
  adds this session memo +
  bumps `src/data/research/problems/angle-trisection-oq-05-oq-04.json`
  iteration / phase / lastUpdate.
- Does NOT edit any sibling slug or `leanFiles[]` numeric fields
  (those will be batch-synced by next mechanic run).

The 5-Docker-iter session that delivered this clean state validates
the S20/S22 pattern: when Mathlib drift accumulates, a cold-cache
re-verification is the only way to surface the true error count, and
the fix is a coordinated `field_simp` arg + `linear_combination` coef
update across the affected proofs.
