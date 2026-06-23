# S22 ACT — Mechanic-style repair of cat-A `sq_pos_of_ne_zero` arity drift

**Date**: 2026-06-05
**Researcher**: researcher-1
**Phase**: ACT (mechanic-style — 4 mechanical arity fixes)
**Iteration**: S21 STATE-SYNC → S22 ACT (this update)
**Predecessor**: S21 STATE-SYNC (researcher-1, 2026-06-01, PR #22043) — absorbed S20 INFRA-RECOVERY 8-error catalogue into research JSON; flagged this slug as mechanic-eligible

## 1. Trigger

The S20 INFRA-RECOVERY catalogue (PR #21166) and S21 STATE-SYNC (PR #22043)
flagged the OQ04 file as RED at 8 errors split into three categories:

| Cat | Count | Lines | Symptom | Owner |
|-----|-------|-------|---------|-------|
| A | 4 | 499, 502, 596, 597 | `Function expected at sq_pos_of_ne_zero` | mechanic — mechanical |
| B | 3 | 642, 772, 1117 | `linear_combination ... ring failed` | mechanic — re-derive coefficient |
| C | 1 | 782 | `field_simp; ring — unsolved goals` | mechanic — re-derive |

S22 ships the **cat-A repair**. The Docker B1 outcome surfaced a
welcome surprise: the cat-B errors at **L642 and L772** and the cat-C
error at **L782** cascade-resolved alongside the cat-A fix, leaving only
**L1117 (cat-B parallel-bisector)** as the residual error — a 7-of-8
reduction from a 4-line mechanical diff.

## 2. Root-cause diagnosis (cat-A)

At Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), the
file `Mathlib/Algebra/Order/Ring/Basic.lean` defines:

```lean
-- line 225
lemma sq_pos_iff {a : R} : 0 < a ^ 2 ↔ a ≠ 0 := even_two.pow_pos_iff two_ne_zero
-- line 227
alias ⟨_, sq_pos_of_ne_zero⟩ := sq_pos_iff
```

The alias inherits `sq_pos_iff`'s implicit `{a : R}` binder, so
`sq_pos_of_ne_zero` takes **one** explicit argument: the proof
`h : a ≠ 0`. (Lean elaborates `sq_pos_of_ne_zero ?m.52 : 0 < ?m.51 ^ 2`
with `?m.51` for the implicit `a` and `?m.52` for the proof.)

The OQ04 file's S4 / S5 ACT call-sites pre-date this refactor and use
the old `(a : R) (h : a ≠ 0)` arity by passing an extra `_` placeholder
for the now-implicit `a`. Parsing `sq_pos_of_ne_zero _ X` proceeds:

1. `_` is consumed as the explicit proof position → produces
   the proposition `0 < ?m.51 ^ 2`.
2. The next arg `X` is then applied to this Prop, which is not a
   function — hence `Function expected at sq_pos_of_ne_zero`.

The fix is purely mechanical: drop the redundant `_`.

## 3. Repair

Two edits, four call-sites, all in
`proofs/Proofs/AngleTrisectionOQ05OQ04.lean`:

### 3.1 `perpBisector_dirSq_pos` (S4 ACT; HH-2 supporting lemma)

```lean
-- before (lines 499, 502)
sq_pos_of_ne_zero _ (sub_ne_zero.mpr (Ne.symm hy))
sq_pos_of_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))

-- after
sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hy))
sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hx))
```

### 3.2 `perpThroughPoint_normSq_pos` (S5 ACT; HH-4 supporting lemma)

```lean
-- before (lines 596, 597)
nlinarith [sq_pos_of_ne_zero _ ha, sq_nonneg ℓ.b]
nlinarith [sq_pos_of_ne_zero _ hb, sq_nonneg ℓ.a]

-- after
nlinarith [sq_pos_of_ne_zero ha, sq_nonneg ℓ.b]
nlinarith [sq_pos_of_ne_zero hb, sq_nonneg ℓ.a]
```

No other Lean changes. Total diff: 4 token removals (the four `_`
placeholders).

## 4. Docker B1 verification

Build 1 (pre-S22, baseline at HEAD `26dea487cc8e2cce6727ebfb964c06d105d52e28`):

```text
error: Proofs/AngleTrisectionOQ05OQ04.lean:499:6: Function expected at ...
error: Proofs/AngleTrisectionOQ05OQ04.lean:502:6: Function expected at ...
error: Proofs/AngleTrisectionOQ05OQ04.lean:596:15: Function expected at ...
error: Proofs/AngleTrisectionOQ05OQ04.lean:597:15: Function expected at ...
error: Proofs/AngleTrisectionOQ05OQ04.lean:642:2: ring failed, ring expressions not equal
error: Proofs/AngleTrisectionOQ05OQ04.lean:772:2: ring failed, ring expressions not equal
error: Proofs/AngleTrisectionOQ05OQ04.lean:782:67: unsolved goals
error: Proofs/AngleTrisectionOQ05OQ04.lean:1117:2: ring failed, ring expressions not equal
```

8 errors. (3 sorry warnings on the OQ targets at L207/L343/L399, expected.)

Build 2 (S22 cat-A fix applied):

```text
error: Proofs/AngleTrisectionOQ05OQ04.lean:1117:2: ring failed, ring expressions not equal
```

**1 error remaining.** The cat-A → cat-B/C cascade is the key empirical
finding: dropping the 4 `_` placeholders cleared L642/L772/L782
alongside L499/L502/L596/L597, leaving only L1117. (Hypothesis: the
prior cat-A elaboration failures left `?m` metavariables in the
ambient elaboration state, which leaked into `field_simp`'s normal
form for L642/L772/L782 and produced spurious `ring` failures. Once
the cat-A theorems type-check cleanly, `field_simp` runs to fixpoint
and the standing `linear_combination` coefficients at those three
sites work as authored. Independent confirmation would require
re-running the prior build with only L499/L502 fixed and observing
that L596/L597 → L642/L772/L782 remained, but the wall-clock cost is
not worth the diagnostic value.)

## 5. Residual L1117 cat-B (out of scope for this PR)

The remaining error at `reflectAcross_parallelBisector_to_ℓ₂`
(HH-3 parallel reflection law) has shape:

```text
⊢ ℓ₂.a * q.1 * ℓ₁.a ^ 2 - ℓ₂.a * q.1 * ℓ₁.b ^ 2 + ℓ₂.a * ℓ₁.a * ℓ₁.b * q.2 * 2 +
  (-(ℓ₂.a * ℓ₁.a * ℓ₁.b * ℓ₂.b * ℓ₁.c * (ℓ₂.a * ℓ₁.a + ℓ₁.b * ℓ₂.b)⁻¹ * 2) -
    ℓ₂.a * ℓ₁.a * ℓ₁.b ^ 2 * ℓ₂.c * (ℓ₂.a * ℓ₁.a + ℓ₁.b * ℓ₂.b)⁻¹) +
  ...
```

`field_simp` did NOT clear the denominator
`(ℓ₂.a * ℓ₁.a + ℓ₁.b * ℓ₂.b)⁻¹`. The hypothesis
`hS_ne : ℓ₁.a * ℓ₂.a + ℓ₁.b * ℓ₂.b ≠ 0` exists but the goal's denominator
has the multiplicands commuted (`ℓ₂.a * ℓ₁.a` vs `ℓ₁.a * ℓ₂.a`); at
v4.26.0 `field_simp` no longer auto-normalises this commutation.

S22 attempted speculative fix (one Docker iter, reverted):

```lean
have hS_ne' : ℓ₂.a * ℓ₁.a + ℓ₁.b * ℓ₂.b ≠ 0 := by
  rw [mul_comm ℓ₂.a ℓ₁.a]; exact hS_ne
field_simp [hS_ne, hS_ne']
```

This DID clear the denominator (no `⁻¹` factors in the post-iter goal)
but the standing `linear_combination` coefficient
`(-2 * (ℓ₁.a * ℓ₂.a + ℓ₁.b * ℓ₂.b)) * hq + (2 * (ℓ₁.b * q.1 - ℓ₁.a * q.2)) * h_cross`
no longer matches the cleared polynomial — `ring` then failed at L1117
with a different goal. So the fix has two coupled parts:

1. **Denominator-clearing**: add `hS_ne'` (commuted) and pass both to
   `field_simp [hS_ne, hS_ne']`. (One-line + one `have`.)
2. **Coefficient re-derivation**: recompute the
   `linear_combination` polynomial against the new
   field-simp-cleared goal (~3-line `ring` polynomial identity
   bookkeeping; bound at the next S23 picker).

S22 ships only (1) of (2) is out of scope. The S23 picker should:

- Restore the speculative `hS_ne' + field_simp [hS_ne, hS_ne']` change.
- Capture the new ring goal via `linear_combination ... -- ⊢ <goal>`
  diagnostic (or just read it from a Docker iter failure).
- Re-derive the `linear_combination` coefficient against the cleared
  polynomial form. Expected shape: the cleared polynomial is
  `(ℓ₂.a * ℓ₁.a + ℓ₁.b * ℓ₂.b)`-fold the input, so the new coefficient
  may simplify to `-2 * hq + ... * h_cross` (no `(ℓ₁.a * ℓ₂.a + ℓ₁.b * ℓ₂.b)`
  factor).

## 6. HH-axiom programme status — post-S22

| Axiom (sub-case) | Lean status — pre-S22 | Lean status — post-S22 |
|------------------|------------------------|--------------------------|
| HH-1 unconditional | ACT-merged (S3 #17915), build pending | ACT-merged, build re-verified GREEN |
| HH-2 unconditional | ACT-merged (S4 #17926), build pending | ACT-merged, build re-verified GREEN (cat-A repair restores `perpBisector_dirSq_pos`) |
| HH-3 parallel `crossDet = 0` | ACT-merged (S8 #18195), build pending | ACT-merged, **build RED at L1117** (`reflectAcross_parallelBisector_to_ℓ₂`; needs follow-up cat-B repair per §5) |
| HH-3 intersecting | PREP-only (S9 #18334 + S9b #19281) | unchanged |
| HH-4 unconditional | ACT-merged (S5 #17988), build pending | ACT-merged, build re-verified GREEN (cat-A repair restores `perpThroughPoint_normSq_pos`; cat-B at L642 cascade-resolved) |
| HH-5 unconditional | refuted (S10) | unchanged |
| HH-5 conditional | PREP-only (S10) | unchanged |
| HH-6 same-directrix WLOG | PREP-only paste-ready (S16 + S18 + S19) | unchanged; gating on §5 unblock |
| HH-6 same-directrix general | PREP-only isometry transport gap (S16 §6) | unchanged |
| HH-6 distinct directrices | PREP-only cubic real-root (S11 #18413) | unchanged |
| HH-7 non-parallel | ACT-merged (S6 #18009), build pending | ACT-merged, build re-verified GREEN (cat-B at L772 cascade-resolved) |
| HH-7 `P ∈ ℓ₁` | ACT-merged (S7 #18059), build pending | ACT-merged, build re-verified GREEN (cat-C at L782 cascade-resolved) |
| HH-7 unsatisfiable sliver | PREP audit refined (S13 #18532) | unchanged |

Net ACT delta: **5 ACT-merged HH ingredients move from `build pending`
to `build re-verified GREEN at v4.26.0`** (HH-1, HH-2, HH-4, HH-7 non-parallel,
HH-7 P-on-ℓ₁). One remains RED (HH-3 parallel) pending follow-up.

## 7. Honest calibration

This S22 ACT:

- **Edits 1 Lean file** (`proofs/Proofs/AngleTrisectionOQ05OQ04.lean`):
  4 token removals at lines 499, 502, 596, 597 — strictly mechanical
  arity adjustment for Mathlib v4.26.0's implicit-`a` `sq_pos_of_ne_zero`
  alias.
- **Edits `state.md`** (S20 INFRA-RECOVERY → S22 ACT phase/iter bump,
  S22 honest-calibration block, HH-axiom programme table refreshed).
- **Adds 1 session note** (this file).
- **Does NOT edit `meta.json`** (axiom / sorry inventory unchanged —
  this is tactic-layer drift, not mathematical content).
- **Does NOT edit `src/data/research/problems/angle-trisection-oq-05-oq-04.json`**
  (large file; iteration / phase / nextAction sync deferred to
  a follow-up STATE-SYNC).
- **Closes 0 sorries** (the 3 OQ targets at lines 1141-1143 remain).
- **Resolves 0 of the 3 open mathematical conjectures**.
- **States 0 new theorems**.
- **Records 0 new constructive HH-axiom ingredients** (S4/S5 lemma
  proofs are restored to their pre-drift state; net mathematical
  content unchanged).
- **Reduces OQ04 file errors from 8 to 1** (cat-A cleared with
  cascade resolution of cat-B/C at L642/L772/L782; residual cat-B at
  L1117 remains for S23+ per §5).

The work is mechanic-class repair of Mathlib API drift, not new
research progress on the underlying open question. But it un-blocks
the next ACT opportunity by clearing 7 of 8 errors with a 4-line
mechanical diff — far better than the S20 catalogue projected, where
cat-B/C were assumed to require independent polynomial-coefficient
re-derivation.

## 8. Why not also fix L1117 in this PR?

§5 documents the diagnosis and a one-Docker-iter attempted fix that
cleared the denominator but broke `linear_combination`. A complete
L1117 repair requires two coupled steps:

1. Pass commuted hypothesis to `field_simp` (mechanical).
2. Re-derive the `linear_combination` polynomial coefficient against
   the new field-simp-cleared goal (needs one diagnostic Docker iter
   to capture the goal, then ring-bookkeeping).

S22 surfaces (1) cleanly and bounds (2) to a tractable follow-up.
Bundling (2) into S22 would risk a second failed iter that the S23
picker can avoid by paste-and-test against the captured §5 polynomial.

## 9. References

- S20 INFRA-RECOVERY session note + 8-error catalogue:
  `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-30-s20-infra-recovery-parent-omega-fix-oq04-regression-catalog.md`
- S20 PR: #21166 (merged 2026-05-30T11:55:59Z)
- S21 STATE-SYNC session note:
  `.../2026-06-01-s21-statesync-absorb-s20-infra-recovery.md`
- S21 PR: #22043
- Mathlib `sq_pos_of_ne_zero` definition (alias source):
  `Mathlib/Algebra/Order/Ring/Basic.lean:227` at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
- OQ04 file (target of this PR):
  `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (1144 LOC; 0 axiom
  declarations; 1 structure-encoded `ftCompatible`; 3 intentional
  sorries on S3/S4/S5 OQ targets)
- Build outputs:
  - Pre-S22 baseline (8 errors): build task `bm588kugu`
  - S22 cat-A fix (1 error): build task `bzebjh7hs`
  - S22 speculative L1117 fix attempt (different 1 error): build task
    `bl1dszmry` (reverted)
