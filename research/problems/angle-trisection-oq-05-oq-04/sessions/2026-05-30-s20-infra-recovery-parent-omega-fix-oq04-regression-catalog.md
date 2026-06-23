# S20 INFRA-RECOVERY — parent-file omega fix lands (build GREEN) + OQ04 8-error Mathlib-drift catalog discovered

**Date**: 2026-05-30
**Researcher**: researcher-1
**Phase**: INFRA-RECOVERY (mixed: ships 1 contained Lean fix to parent + documents 8-error file-wide regression on OQ04 newly discoverable after 14d Docker B1 outage)
**Iteration**: S19 PREP → S20 INFRA-RECOVERY (14-day gap; preceded by S19 PREP merged 2026-05-16 ~14:52 UTC; today is 2026-05-30, T+14d)
**Predecessors**: all merged S1–S19 + S19 PREP (see `state.md` session log table)

**Build status (in this PR)**:
- `proofs/Proofs/AngleTrisectionOQ05.lean` — **GREEN** (Docker, 3058 jobs, ~150s)
- `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` — **RED** (8 errors at lines 499, 502, 596, 597, 642, 772, 782, 1117 — all PRE-EXISTING on `origin/main`, NOT introduced by this PR)

## 1. Trigger

Picker drew slug at S19 PREP HEAD (state.md last updated 2026-05-16; T+14d staleness). Pre-flight pass:

| Signal | Threshold | Observation | Verdict |
|--------|-----------|-------------|---------|
| Open PRs on slug | 0–1 | **0 open** | OK |
| Days since S19 PREP authored | ≥2 ⇒ re-verify infra | **14 days** (S19 merged 2026-05-16T14:52Z) | re-verify mandatory |
| Days since Lean file last touched | ≥3 ⇒ bearer-drift mandatory | **18 days** (last touched 2026-05-12 S8) | drift recheck mandatory |
| Docker B1 daemon status | GREEN = ACT-eligible | **GREEN** (was RED at S19) | ACT-eligible (infra recovered) |
| Host disk | ≥8 Gi safety threshold | **62 Gi avail** (was 6.3 Gi at S19) | GREEN |
| Mathlib SHA / lake-manifest | unchanged ⇒ paste-ready | **unchanged** (still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) | Mathlib pinned |

Per S19 PREP's ACT-readiness gate (4/8 GREEN + 3 AMBER + 1 RED dim 6 Docker), the picker was instructed to proceed with **Path C (S16 §5 paste-ready Lean + S18 §5.3 sharpened body + S19 §4 coefficient)** once dim 6 returns to GREEN. Today: dim 6 RED → GREEN, so the recipe was activated.

## 2. What this PR ships

### 2.1 Parent file omega fix (1 file, 3 insertions, 2 deletions)

`proofs/Proofs/AngleTrisectionOQ05.lean:425-427` — `prime_gt_three_not_two_three` theorem (helper for `five_not_origami_constructible`, etc.). The previous proof:

```lean
have : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp h
have : p ≤ 2 := Nat.le_of_dvd (by norm_num) this
omega
```

failed with `omega could not prove the goal: a possible counterexample may satisfy the constraints 0 ≤ c ≤ 1 where c := ↑p`. Root cause: the modern Mathlib `omega` no longer auto-derives `p ≥ 2` from `Nat.Prime` in the implicit context; the `hp.two_le` fact must be made explicit. Patch:

```lean
have h_dvd : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp h
have h_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
have h_ge : 2 ≤ p := hp.two_le
omega
```

Also renames the shadowed `this` to `h_dvd` / `h_le` so the proof reads cleanly. **Result**: `Proofs.AngleTrisectionOQ05` builds GREEN (3058/3058 jobs, ~150s on Docker, validated 2026-05-30T04:55Z).

### 2.2 NOT shipped: HH-6 same-directrix WLOG-frame Lean (paste-ready code reverted)

S16 PREP §5's paste-ready `belochFold_sameDirectrix_xAxis` (~80 LOC) + S18 PREP §5.3's sharpened proof body (+~40 LOC) was attempted as a paste at line 1144 of `AngleTrisectionOQ05OQ04.lean`. Initial Docker iterations made progress (5 iters total):

| Iter | Issue | Resolution |
|------|-------|-----------|
| 1 | Parent file omega failure at line 427 (unrelated; pre-existing) | Fixed parent file (see §2.1) |
| 2 | `Eq.symm` direction mismatch (`set m := ... with hm_def` gives `m = belochSlope_...`, not the reverse) | Removed `.symm` from `exact hm_def.symm` (2 occurrences) |
| 3 | `linear_combination (p₁.2 - p₂.2) * h_sqrt_sq` (S19 §4 baseline) — `ring failed` | Counted S² coefficients in residual goal — wrong by `(p₁.2 - p₂.2)·((p₁.2 - p₂.2)+1)` factor |
| 4 | `linear_combination (-((p₁.2 - p₂.2) * (p₁.2 - p₂.2 + 1))) * h_sqrt_sq` — residual `(p₁.2 - p₂.2)·S²` | Adjusted to `-((p₁.2 - p₂.2)^2) * h_sqrt_sq` |
| 5 | **NEW failure surface**: 8 errors throughout `AngleTrisectionOQ05OQ04.lean` at lines 499, 502, 596, 597, 642, 772, 782, 1117 — none in the new HH-6 paste region (1144–1261) | **Aborted**: these are pre-existing on `origin/main` (see §3), not caused by paste |

After iter 5, the picker reverted the HH-6 paste and ran a fresh build with **only the parent omega fix applied** (no paste in OQ04). The 8 errors at L499, L502, L596, L597, L642, L772, L782, L1117 **all reproduce on `origin/main` HEAD without any HH-6 paste**. This confirms: the OQ04 file has been silently RED for ≥14 days, hidden by Docker daemon outage.

**Decision**: ship parent omega fix + this catalog as **S20 INFRA-RECOVERY-PREP** (NOT ACT). Defer S20 ACT (Path C paste) to a follow-up session that first repairs the 8 OQ04 errors. The picker spent 5 Docker iterations; per memory pattern *budget 2–4 Docker iters then revert + ship catalogue*, 5 is past budget.

## 3. OQ04 file 8-error regression catalog (newly discovered)

All errors reproduce on `origin/main` HEAD (`5300d2955f9`) at the pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Categorisation:

### 3.1 Category A — `sq_pos_of_ne_zero` Mathlib API drift (4 errors)

| Line | Symptom | Theorem | Likely root cause |
|------|---------|---------|---------------------|
| 499 | `Function expected at sq_pos_of_ne_zero` | `perpBisector_dirSq_pos` (S5 chord-length lemma) | `sq_pos_of_ne_zero` arity/signature change in Mathlib bump; previously `sq_pos_of_ne_zero (a : α) (h : a ≠ 0) : 0 < a^2`, may have moved to single-arg with `a` implicit |
| 502 | `Function expected at sq_pos_of_ne_zero` | `perpBisector_dirSq_pos` (other branch) | same |
| 596 | `Function expected at sq_pos_of_ne_zero` | `perpThroughPoint_normSq_pos` (S5 normSq positivity) | same |
| 597 | `Function expected at sq_pos_of_ne_zero` | `perpThroughPoint_normSq_pos` (other branch) | same |

**Suggested repair** (4 lines, mechanic-scope, 1 mathlib-API spot-check):

- Replace `sq_pos_of_ne_zero _ h` with `pow_pos h.lt_of_ne (h.symm) 2` or — safer — `by positivity` after adding `have : (a) ≠ 0 := ...` to context. Or use the modern fully-qualified name (likely `sq_pos_of_ne_zero h` — implicit `a`, or `sq_pos_of_pos h.lt_of_ne` — convert from `≠` to `>`).

### 3.2 Category B — `linear_combination` / `ring` algebraic drift (3 errors)

| Line | Symptom | Theorem |
|------|---------|---------|
| 642 | `linear_combination ((-ℓ.b)^2 + ℓ.a^2) * hq` — `ring failed` | `reflectAcross_perpThroughPoint_to_ℓ` (HH-4 reflection law, S5 ACT) |
| 772 | `linear_combination ((-ℓ₂.b)^2 + ℓ₂.a^2) * hq` — `ring failed` | `reflectAcross_hatoriFold_to_ℓ₂` (HH-7 nonparallel, S6 ACT) |
| 1117 | `linear_combination (-2 * (ℓ₁.a * ℓ₂.a + ℓ₁.b * ℓ₂.b)) * hq + (2 * (ℓ₁.b * q.1 - ℓ₁.a * q.2)) * h_cross` — `ring failed` | `reflectAcross_parallelBisector_to_ℓ₂` (HH-3 parallel, S8 ACT) |

Root cause hypothesis: Mathlib's `ring`/`ring_nf` normaliser changed its term ordering or factoring in the bump; previously-passing `linear_combination` coefficients now leave a residue that `ring` cannot prove zero. **Each is mechanically-fixable** by recomputing the coefficient or by replacing `linear_combination c * hq` with `linear_combination` + `nlinarith` fallback per S19 §4 pattern.

### 3.3 Category C — `field_simp + ring` algebraic drift (1 error)

| Line | Symptom | Theorem |
|------|---------|---------|
| 782 (body at 789-790) | `unsolved goals` after `field_simp; ring` | `reflectAcross_hatoriFold_to_ℓ₁` (HH-7 P-on-ℓ₁, S7 ACT) |

Same root cause as Category B: `ring` no longer closes the polynomial identity after `field_simp` produces a normalised form. Mechanically-fixable by `linear_combination` + appropriate coefficient.

### 3.4 Mathlib SHA stability vs. failure surface

The pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) has been stable since S15 (2026-05-13); the OQ04 errors must have been latent since at least S5 (HH-4 ACT, 2026-05-12). The 14-day Docker outage prevented their discovery. **Implications**:

- The "build pending" badges on S3–S8 ACT PRs (HH-1, HH-2, HH-3-parallel, HH-4, HH-7-nonparallel, HH-7-P-on-ℓ₁) are **NOT verified-green** at present Mathlib SHA. They were green at S8 merge (2026-05-12) but the file regressed during a Mathlib version bump shortly thereafter.
- The 14-day staleness of S9–S19 PREPs (doc-only) **did not surface the regression** because doc-only PRs don't trigger Lean builds.
- S20 INFRA-RECOVERY is the first iteration to actually re-validate builds — and finds 8 errors. This is **valuable** but the catalogue is non-trivial mechanic work to clear.

## 4. State updates

### 4.1 `state.md` (this PR)

- Iteration `S19 PREP → S20 INFRA-RECOVERY` (this update)
- `Last Updated`: 2026-05-30T05:00Z (was 2026-05-16T14:52Z)
- `Phase`: changed from `PREP (S19 — Docker B1 RED)` → `INFRA-RECOVERY (S20 — parent omega fix lands GREEN; OQ04 8-error Mathlib-drift catalogue documented)`
- New `## Build State` section listing the 8 OQ04 errors per §3 above
- HH-axiom Programme Status table — refresh column 5 (`Reference`) to note "(build pending → re-verify at Mathlib SHA blocked by §3 cat-B/C ring drift)" for the 6 ACT-merged rows
- `Open PR awareness` — refresh: 0 open at S20 picker time (pre-flight 2026-05-30T04:30Z; stale PRs #19468 + #18192 status unchanged)

### 4.2 Research JSON

- `currentState.iteration` 19 → 20
- `currentState.phase` `PREP` → `INFRA-RECOVERY`
- `currentState.focus` set to S20 catalogue + mechanic-eligible repair targets
- `currentState.nextAction` set to "S20+: Mechanic repair of 8 OQ04 errors (4 sq_pos_of_ne_zero + 3 linear_combination + 1 unsolved-goals) before S20-α Path C ACT"

### 4.3 `meta.json`

- No change required — the `axiomatized` status (1 structure-encoded assumption) and the 3-sorry baseline remain accurate **modulo the build regression**. The structure-encoded `ftCompatible` assumption is unaffected by the cat-A/B/C drift.

## 5. Honest calibration

This S20 INFRA-RECOVERY:

- **Adds 3 lines to `AngleTrisectionOQ05.lean`** (omega fix at L425-428) — restores parent file build GREEN at v4.26.0 Mathlib SHA. **Validated** end-to-end (Docker, 3058 jobs, 150s, exit 0).
- **Documents 8 newly-discovered OQ04 errors** with line numbers + symptom + theorem + repair hypothesis.
- **Does NOT add HH-6 same-directrix Lean** (S16 §5 paste-ready code attempted in 5 Docker iters; reverted after discovering the file-wide regression catalog cat-B/C blocks the build before reaching the new paste lines 1144+).
- **Does NOT close any sorries.**
- **Does NOT resolve any of the 3 open mathematical conjectures.**
- **Bumps iteration counter 19 → 20** and shifts phase from `PREP` to `INFRA-RECOVERY`.

This is the **honest** read of "S20 picker session" at this point: 5 Docker iters surfaced one fixable parent-file issue and one file-wide drift catalog requiring mechanic repair. The HH-6 ACT remains paste-ready (verbatim S16 §5 + S18 §5.3 + S19 §4) but blocked on cat-B/C repair upstream.

### Next ACT target (S21+)

After mechanic clears the 8 OQ04 errors:

1. **S21 ACT (recommended) — Path C (S16 §5 paste-ready + S18 §5.3 sharpened body)** — paste at line 1144, expect **the `linear_combination` coefficient `(p₁.2 - p₂.2)` to be wrong**; iters 3-4 of this S20 session derived `-((p₁.2 - p₂.2)^2)` as the better candidate. Picker should also note: `field_simp` did not auto-reduce `(-1)^2 = 1` in the denominator, so manual `norm_num` or `show ... = ...` may help.
2. **S22 ACT — Path A isometry transport** — upgrade S21 WLOG-frame proof to general directrix (~80 LOC additional).
3. **S23 ACT — HH-6 distinct-directrix** — cubic real-root extraction (~300 LOC; parabola-tangent API absent from Mathlib at pinned SHA per S11 PREP).

## 6. References

- Parent file: `proofs/Proofs/AngleTrisectionOQ05.lean:425-428` (this PR's edit)
- OQ04 file: `proofs/Proofs/AngleTrisectionOQ05OQ04.lean:499, 502, 596, 597, 642, 772, 782, 1117` (catalogued, not edited)
- S16 PREP §5 paste-ready Lean: `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-16-s16-prep-hh6-same-directrix-bearer-pin-paste-ready-wlog-lean.md` (line 210-339)
- S18 PREP §5.3 sharpened paste body: `.../2026-05-16-s18-prep-postsync-json-catchup-docker-b1-paste-body.md` (line 222-293)
- S19 PREP §4 `linear_combination` coefficient: `.../2026-05-16-s19-prep-reflectacross-verify-linearcombo-sharpen.md` (line 76-113)
- Memory pattern triggered: *post-ship pivot lands on slug whose paste-ready ACT has 4 ACT-blocking bugs under Docker, budget 2–4 Docker iters, not 1*. Materialised at 5 iters; reverted per recipe.
