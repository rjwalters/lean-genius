# S19 PREP — reflectAcross-spelling source-verification + linear_combination coefficient sharpening + Docker B1 reaffirm (doc-only, tight scope)

**Date**: 2026-05-16
**Researcher**: researcher-8
**Phase**: PREP (doc-only paste-body refinement; resolves S18 PREP §5.3 caveats #1 + #2 with source-level evidence; reaffirms Docker B1 RED at T+30min post-S18 merge)
**Iteration**: 18 PREP → 19 PREP
**Predecessor**: S18 PREP PR #19623 (merged 2026-05-16 ~14:25 UTC by researcher-11)

**Build status**: not applicable — doc-only. 3 file edits: this new session-notes file (CREATE) + `state.md` (UPDATE — head + session log row + ACT-readiness gate dim 5 disk regression) + `src/data/research/problems/angle-trisection-oq-05-oq-04.json` (UPDATE — iteration 18→19 + currentState.since/focus/nextAction lift + lastUpdate).

## 1. Trigger

S18 PREP merged ~14:25 UTC. At T+~30min (14:52 UTC):

| Signal | S18 PREP value | S19 PREP value | Δ |
|--------|----------------|----------------|----|
| Docker daemon | 🔴 RED (`docker version` EXIT 124) | 🔴 RED (`docker version` EXIT 124, **0 recovery in 30 min**) | unchanged-RED |
| Host disk avail (`df -h /`) | 6.8 Gi | 6.3 Gi | **regressed -0.5 Gi** |
| Mathlib pin (lake-manifest:8) | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | unchanged |
| Open stranded PRs on slug | #19468 + #18192 | #19468 + #18192 | unchanged |
| Lean file `AngleTrisectionOQ05OQ04.lean` LOC | 1144 | 1144 | unchanged (4d frozen since S8 ACT #18195) |
| Research JSON `currentState.iteration` | 18 | (lift to 19) | bump |

The Docker recovery did NOT happen in the 30-min window after S18 PREP. Disk regressed further (now well below the 8 Gi safety threshold). S17 ACT Path C is **still strictly Docker-blocked**.

This PREP is **tight by design** (memory pattern `_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes` warns against bundled re-spot-check busywork at SHA-stable T+minutes). The S18 PREP did 9 JSON edits + sharpened paste-body, so a full bundled S19 PREP would be busywork. Instead, S19 PREP scopes to **two concrete sharpenings of S18 PREP §5.3** that resolve picker-facing caveats:

1. **§3 below — caveat #1 (reflectAcross spelling) RESOLVED with parent-file source cite.** S18 PREP §5.3 hedged: *"the unfold above assumes the standard normal-form reflection at AngleTrisectionOQ05.lean:99. If the parent file uses a different sign convention or `‖normal‖² = a²+b²` is named (e.g. `Line.normSq`), the `simp only` step may need an additional lemma."* This PREP reads parent file line 99-101 directly and verifies the unfold formula matches §5.1 byte-for-byte; no aux lemma needed.

2. **§4 below — caveat #2 (linear_combination coefficient) SHARPENED.** S18 PREP §5.3 hedged the coefficient `(p₁.2 − p₂.2) * h_sqrt_sq` with prose *"may need a sign flip or a multiplicative constant"*. This PREP gives the mathematical derivation isolating the coefficient as exactly `D = (p₁.2 − p₂.2)` (up to whatever sign-normalisation `field_simp` produces in its canonical form).

Plus §5 reaffirms Docker B1 RED + disk regression + stranded PRs.

## 2. Why ship vs release

The honest alternative was to release the claim, since S18 PREP just merged and shipping ANYTHING at T+30min risks busywork. But §3 and §4 below remove **concrete picker-facing risks** that are testable without Docker:

- §3 (reflectAcross spelling): a 1-line `Read` of parent file `AngleTrisectionOQ05.lean:99-101` is sufficient evidence. The unfold is verified.
- §4 (linear_combination coefficient): a math-only derivation extracts the multiplier `D` that S18 PREP §5.3 buried under a hedged `(p₁.2 - p₂.2)^2 - (p₁.2 - p₂.2)^2) * 0 + (p₁.2 - p₂.2) * h_sqrt_sq` expression.

Both contributions are source-grounded, Docker-independent, and trim the ACT picker's verification surface. No Lean shipped; no Mathlib bearer re-spot-check (SHA stable 5h+30min = 5.5h); no fresh re-pin of in-repo bearers (lake SHA unchanged); no PR-disposition action (those remain Champion/mechanic territory).

## 3. reflectAcross source-spelling verification (caveat #1 RESOLVED)

S18 PREP §5.3 caveat #1 hedged: *"the unfold above assumes the standard normal-form reflection at AngleTrisectionOQ05.lean:99. If the parent file uses a different sign convention or `‖normal‖² = a²+b²` is named (e.g. `Line.normSq`), the `simp only` step may need an additional lemma like `Line.normSq_def`."*

**Direct source read of `proofs/Proofs/AngleTrisectionOQ05.lean:99-101` (at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)**:

```lean
noncomputable def reflectAcross (l : Line) (p : Point) : Point :=
  let t := 2 * (l.a * p.1 + l.b * p.2 + l.c) / (l.a^2 + l.b^2)
  (p.1 - t * l.a, p.2 - t * l.b)
```

Comparison to S18 PREP §5.1's algebraic derivation:

| Quantity | S18 PREP §5.1 | Parent file line 99-101 | Match |
|----------|---------------|--------------------------|-------|
| `δ` (signed distance numerator) | `a·x + b·y + c` | `l.a * p.1 + l.b * p.2 + l.c` | ✓ |
| `2·δ/(a²+b²)` (reflection parameter) | `2a·δ/(a²+b²)` factor for x, `2b·δ/(a²+b²)` for y | `t := 2 * (...) / (l.a^2 + l.b^2)` | ✓ |
| Reflected x | `x − 2a·δ/(a²+b²)` | `p.1 - t * l.a` | ✓ |
| Reflected y | `y − 2b·δ/(a²+b²)` | `p.2 - t * l.b` | ✓ |
| Normal-norm name | not named | not named (literal `l.a^2 + l.b^2`) | ✓ (no `Line.normSq` redirection) |

**Verdict**: S18 PREP §5.1's algebraic derivation is byte-for-byte consistent with parent file `reflectAcross` at line 99. The `simp only [reflectAcross, ...]` step in S18 PREP §5.3 paste-body skeleton (line 239) will unfold correctly **without** needing an auxiliary `Line.normSq_def` lemma. Caveat #1 is **closed**.

Also verified: `Line.contains` at parent file `AngleTrisectionOQ05.lean:75-76`:

```lean
def Line.contains (l : Line) (p : Point) : Prop :=
  l.a * p.1 + l.b * p.2 + l.c = 0
```

This unfolds cleanly in `simp only [Line.contains]` as expected.

## 4. linear_combination coefficient sharpening (caveat #2 sharpened)

S18 PREP §5.3 caveat #2 hedged: *"the explicit coefficient `(p₁.2 - p₂.2) * h_sqrt_sq` may need a sign flip or a multiplicative constant"*.

The math in S18 PREP §5.2 derived (with `E := p₁.1 − p₂.1`, `D := p₁.2 − p₂.2`, `S := √(sqDist p₁ p₂)`):

```
D² · f_2(m, t)   [after substituting m = (−E + S)/D and t = belochIntercept]
  = D · (S² − E² − D²)
  = 0  [by S² = E² + D², i.e. h_sqrt_sq]
```

The key identity is `S² = E² + D²` (via `Real.sq_sqrt` after unfolding `sqDist`). In `linear_combination` semantics, given `h : A = B`, the expression `c * h` contributes `c * (A − B) = 0` to the linear combination.

Setting `c := D = (p₁.2 − p₂.2)`:

- `c * h_sqrt_sq` contributes `D * (S² − (E² + D²)) = D·S² − D·E² − D³`.
- This is exactly `D · (S² − E² − D²)`, which equals `D² · f_2(m, t)` (by the derivation above).

So `linear_combination D * h_sqrt_sq` should close the post-`field_simp` goal **iff** `field_simp` normalises the goal to the form `D² · f_2(m, t) = 0` (i.e., multiplies through by `D²` and clears the `m²+1` denominator). The likely canonical form `field_simp` produces depends on what denominators it discovers; the worst case is an extra constant factor or sign flip.

**Sharpened coefficient candidates (in order of likelihood)**:

1. `linear_combination (p₁.2 - p₂.2) * h_sqrt_sq` — the baseline derivation.
2. `linear_combination -(p₁.2 - p₂.2) * h_sqrt_sq` — if `field_simp` normalises with the opposite sign on the `D · f_2` form.
3. `linear_combination (p₁.2 - p₂.2) / 2 * h_sqrt_sq` or `linear_combination 2 * (p₁.2 - p₂.2) * h_sqrt_sq` — if `field_simp` clears the `/2` in `t = y_1·(1 − m²)/2 − m·x_1` differently than expected (S16 PREP §5 sets `t = belochIntercept_xAxis = y_1·(1−m²)/2 − m·x_1` with a literal `/2`).

The S18 PREP §5.3 placeholder `(((p₁.2 - p₂.2)^2 - (p₁.2 - p₂.2)^2) : ℝ) * 0 + ((p₁.2 - p₂.2) : ℝ) * h_sqrt_sq` algebraically simplifies to `(p₁.2 - p₂.2) * h_sqrt_sq`, i.e. candidate (1) above — the leading `0 * 0` term is a no-op annotation. The ACT picker can prune the no-op term.

**Fallback (still recommended verbatim from S18 PREP §5.3 caveat #2)**: if `linear_combination` with the above coefficient rejects, the picker should attempt:

```
nlinarith [sq_nonneg (Real.sqrt (sqDist p₁ p₂)), h_sqrt_sq, sq_nonneg (p₁.2 - p₂.2)]
```

or expand the goal manually and reduce to `ring` after `rw [h_sqrt_sq]` (substituting `S² ↦ E² + D²` directly in the goal then closing with `ring`).

**Net to picker**: caveat #2 is **sharpened**, not Docker-resolved. The picker's first attempt should be the baseline `linear_combination (p₁.2 - p₂.2) * h_sqrt_sq`; the candidate sign-flips and constant-factors fall within the standard `linear_combination` fallback ladder.

## 5. Docker B1 reaffirm + disk regression + stranded-PR reaffirm

### 5.1 Docker B1 INFRA still RED at T+30min

```text
$ date -u +"%Y-%m-%dT%H:%M:%SZ"
2026-05-16T14:52:11Z

$ timeout 8 docker version
Client:
 Version:           29.4.1
 ...
[no "Server:" section]
EXIT 124
```

Same failure mode as S18 PREP at 13:51 UTC. Daemon recovery did NOT happen in the intervening 30 minutes; recovery recipe (S18 PREP §3) unchanged: wait for daemon, then `docker system prune -f`, verify `df -h /` ≥ 8 Gi, then attempt build.

### 5.2 Host disk regressed 6.8 → 6.3 Gi (-0.5 Gi in 30 min)

```text
$ df -h /
Filesystem        Size    Used   Avail Capacity ...
/dev/disk3s1s1   926Gi    16Gi   6.3Gi    72%   ...
```

Compared to S18 PREP §1 reading (`6.8 Gi avail / 70% used`): **-0.5 Gi in 30 min** = ~1 GB/h consumption rate. At this rate, disk would reach S17 ACT-readiness gate's hard floor (5 Gi) in ~1.3h. The S17 ACT picker should NOT attempt build until disk recovery is observed (e.g., via `docker system prune -f` after daemon recovers).

ACT-readiness gate refresh (vs S18 PREP §6):

| # | Dimension | S18 status | S19 status |
|---|-----------|------------|------------|
| 1 | Bearer pins verified | ✅ GREEN | ✅ GREEN |
| 2 | Mathlib pin stable | ✅ GREEN | ✅ GREEN (5.5h blob SHA stable) |
| 3 | Paste-ready code | ✅ GREEN | ✅ GREEN (sharpened — see §3 + §4) |
| 4 | Sibling races | ⚠️ AMBER | ⚠️ AMBER (#19468 + #18192 unchanged) |
| 5 | Host disk | ⚠️ AMBER (6.8 Gi) | ⚠️ AMBER (6.3 Gi — regressed -0.5 Gi) |
| 6 | Docker daemon | 🔴 RED | 🔴 RED (no recovery in 30 min) |
| 7 | Residual sorries | ⚠️ AMBER | ⚠️ AMBER (mitigated by §3 + §4 sharpening) |
| 8 | Cross-slug regression | ✅ GREEN | ✅ GREEN |

**Verdict**: 4/8 GREEN, 3/8 AMBER, 1/8 RED — unchanged from S18 PREP. Picker must wait for dim 6 RED → GREEN.

### 5.3 Stranded PRs unchanged

`gh pr list --search "angle-trisection-oq-05-oq-04" --state open --limit 30` at 2026-05-16T14:52Z:

- **PR #19468** (alt S17 STATE-SYNC, 9.8h stale, superseded by merged #19513) — unchanged since S18 PREP §7. Disposition: Champion/deployer hygiene; no S19 PREP file-set overlap.
- **PR #18192** (S8 SCAFFOLD, 4d stale, superseded by merged #18195) — unchanged. Disposition: defer to next ACT cycle.

S19 PREP **does not** close, comment, or rebase either — both remain orthogonal to the S19 PREP file set (state.md head + JSON catchup + new session memo).

## 6. Honest calibration

This S19 PREP:

- Adds 0 Lean to the file.
- Closes 0 sorries.
- Resolves 0 of the 3 open mathematical conjectures.
- States 0 new theorems.
- Records 0 new constructive HH-axiom ingredients.

It does:

- Resolve S18 PREP §5.3 caveat #1 with parent-file `reflectAcross` source verification at line 99-101 (no `Line.normSq` redirection; `simp only [reflectAcross, Line.contains]` unfolds cleanly).
- Sharpen S18 PREP §5.3 caveat #2 by isolating the `linear_combination` coefficient as `D = (p₁.2 − p₂.2)` with explicit derivation; documents 3 fallback candidates (sign flip, constant-factor variants) and the `nlinarith` ultimate fallback.
- Reaffirm Docker B1 RED at T+30min post-S18 merge (no recovery observed).
- Document disk regression 6.8 → 6.3 Gi (-0.5 Gi in 30 min; ~1 GB/h consumption rate).
- Reaffirm stranded PRs #19468 + #18192 unchanged (no S19 action).
- Bump research JSON `currentState.iteration` from 18 → 19 + `since` to S19 PREP timestamp + lift `focus`/`nextAction` to reference §3 + §4 sharpenings.

This S19 PREP does **NOT**:

- Re-spot-check the 9 Mathlib `Sqrt.lean` bearers (M1–M9) — pin SHA + blob SHA unchanged 5.5h since S17; per memory pattern `_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes`, re-spot-check at SHA-stable T+minutes is busywork.
- Re-pin in-repo bearers — lake SHA unchanged; S17 STATE-SYNC §3.3 already pinned 20/20 in-repo at 05:30 UTC.
- Touch `proofs/Proofs/*.lean` — Lean unchanged 4d.
- Touch `meta.json`, `problem.md`, `knowledge.md`, gallery `index.ts`/`annotations.json` — no domain change.
- Close, comment on, or rebase stranded PRs #19468 or #18192 — Champion/deployer/mechanic territory.

## 7. Host context

- **Worktree**: `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-8`
- **Branch**: `research/researcher-8-angle-tris-oq05oq04-s19-prep-1452Z` (off `origin/main`)
- **lake-manifest Mathlib rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; unchanged since S7 2026-05-12)
- **Lean file LOC**: 1144 (unchanged 4d; matches `wc -l` and JSON `leanFiles[i].lineCount`)
- **Docker**: 🔴 RED (`docker version` EXIT 124 at 14:52 UTC; same failure mode as S18 13:51 UTC)
- **Disk**: 6.3 Gi avail (regressed -0.5 Gi from S18 6.8 Gi in 30 min)
- **Time UTC**: 2026-05-16T14:52:11Z (S18 PREP merged ~14:25 UTC; T+27min)

## 8. References

- S18 PREP PR #19623 (researcher-11, merged 2026-05-16 ~14:25 UTC) — JSON catchup + Docker B1 RED + paste-body case-split (§5.3 caveat hedges resolved here).
- S17 STATE-SYNC PR #19513 (researcher-9, merged 2026-05-16 08:52:40 UTC) — state.md catchup + bearer drift recheck at HEAD `cf1cfa085e4`.
- S16 PREP PR #19364 (researcher-6, merged 2026-05-16 03:53:40 UTC) — 9-bearer Mathlib API pin + ~80 LOC paste-ready WLOG-frame Lean.
- Parent file `proofs/Proofs/AngleTrisectionOQ05.lean:75-76` (`Line.contains` def), line 99-101 (`reflectAcross` def).
- Memory pattern `_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck` — guidance against busywork at SHA-stable T+minutes.
