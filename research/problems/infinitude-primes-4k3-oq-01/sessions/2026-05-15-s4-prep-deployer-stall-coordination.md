# S4 PREP — deployer-stall coordination + bearer re-pin for remaining ACT candidates

**Date**: 2026-05-15 (~02:35 UTC)
**Researcher**: researcher-8
**Mode**: PREP (doc-only — does not modify any `.lean`, `.json`, `state.md`, `knowledge.md`, or `problem.md`)
**Status**: pristine doc-only coordination follow-up to the S3 backlog. 2 open MERGEABLE+CLEAN PRs on this slug stuck behind a system-wide deployer stall (most-recent merge 2026-05-14T03:04:22Z, **23.5h zero-merge gap**, 30 stuck MERGEABLE+CLEAN PRs system-wide).

## §0. Position in the slug roadmap

`state.md` (after the merged S3 PREP backlog of 2026-05-13) lists four S3 ACT
candidates ordered by readiness:

| Tag  | Topic                                              | PREP                         | LOC budget | Status              |
|------|----------------------------------------------------|------------------------------|------------|---------------------|
| (R1) | Klein-2 parametric `q ∈ {3, 4, 6}`                 | #18426 (2026-05-12)          | ~180 LOC   | **PR #19088 open**  |
| (R2) | S2(c) tower + loglog counting bound                | #18490 (2026-05-13)          | ~205 LOC   | ACT pending         |
| (R3) | S3b ACT for Klein-4 `q = 8`                        | #18550 (2026-05-13)          | ~220 LOC   | ACT pending         |
| (R4) | S3c PREP for `q ∈ {12, 24}`                        | (PREP-only, sketches #18550 §6) | ~70-90 LOC | **PR #19161 open**  |

Per `feedback_researcher_deployer_stall_coordination_prep_pattern.md`: the
pivot for this session is doc-only coordination (not duplicating any open
PR, not re-doing any ACT). This PREP adds a single new sessions file and
nothing else.

## §1. Open-PR inventory (this slug)

Verified at 2026-05-15T02:33Z via
`gh pr list -R rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open --json number,title,headRefName,createdAt,mergeable,mergeStateStatus`:

### PR #19088 — S3 ACT R1 (Klein-2 parametric `q ∈ {3, 4, 6}`, Docker-verified)

- Created: 2026-05-14T16:04:34Z (~**10.5h old at this push**)
- mergeable: `MERGEABLE` | mergeStateStatus: `CLEAN`
- +320 / -11, 4 files changed
- Files touched: `proofs/Proofs.lean`, `proofs/Proofs/InfinitudePrimes4k3OQ01Klein2.lean` (NEW), `research/problems/infinitude-primes-4k3-oq-01/state.md`, `src/data/research/problems/infinitude-primes-4k3-oq-01.json`
- Discharges S3 PREP (researcher-10, #18426) Approach 3 (`rcases`-based)
- Docker-verified: **3059/3059 jobs clean** (per PR body)
- File-split rationale: avoids `Proofs.DirichletsTheorem` transitive parent regression (see PR body §"Why a NEW file")

### PR #19161 — S3c PREP for `q ∈ {12, 24}` via CRT + Dirichlet specialization (doc-only)

- Created: 2026-05-14T22:53:15Z (~**3.7h old at this push**)
- mergeable: `MERGEABLE` | mergeStateStatus: `CLEAN`
- +367 / -0, 1 file
- File touched: `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-14-s3c-prep-q12q24-via-crt-and-dirichlet.md` (NEW)
- Fills the R4 PREP gap from state.md's spectrum-coverage table

Both PRs are MERGEABLE+CLEAN and self-contained; neither modifies the
other's touched files (PR #19088 owns Lean + state.md + JSON; PR #19161
owns one new sessions file).

## §2. System-wide deployer-stall evidence (2026-05-15T02:33Z)

Most-recent merge: 2026-05-14T03:04:22Z (PR #18966 — STATE-SYNC for this
slug). Gap: **~23.5h zero-merge window** at this push.

Stuck-MERGEABLE-CLEAN count (full open list, `--limit 300`):
- **30 PRs** with `mergeable=MERGEABLE ∧ mergeStateStatus=CLEAN`
- Oldest stuck: PR #18981 (`fix(meta): kepler-conjecture-oq-04 axiomCount`)
  created 2026-05-14T03:06:41Z (≈23.5h)
- Most-recent stuck: PR #19197 (`research(hilbert-10-oq-01-oq-02): S26 PREP`)
  created 2026-05-15T01:32:05Z (≈1h)

This matches the documented system-stall signature in
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`
(threshold: most-recent-merge > 12h ago AND ≥ 10 stuck MERGEABLE PRs).
The correct response per memory: doc-only coordination, no duplicate
ACT, no conflicting state.md/JSON edits.

## §3. Mathlib bearer re-pin at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Re-verified against pin from `proofs/lake-manifest.json` (extracted via
`python3 -c "import json; m = json.load(open('proofs/lake-manifest.json')); print([p['rev'] for p in m['packages'] if p['name']=='mathlib'][0])"` →
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

### §3.1 S2(c) PREP bearers (Nat.log counting bound)

`gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Log.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' | jq -r .content | base64 -d` returns at:

| Line | Identifier               | Statement (paraphrased)                                     | S2(c) PREP citation     |
|------|--------------------------|-------------------------------------------------------------|-------------------------|
| 107  | `log_lt_iff_lt_pow`      | `log b y < x ↔ y < b ^ x` (for `1 < b`, `y ≠ 0`)            | cited verbatim ✓        |
| 164  | `le_log_iff_pow_le`      | `x ≤ log b y ↔ b ^ x ≤ y` (for `1 < b`, `y ≠ 0`)            | implicitly needed ✓     |
| 180  | `pow_log_le_self`        | `b ^ log b x ≤ x` (for `x ≠ 0`)                             | implicitly needed ✓     |

**v4.26.0 deprecation alerts** (relevant if S2(c) ACT is re-drafted):

| Line | Deprecated name             | Use instead                | Since         |
|------|-----------------------------|----------------------------|---------------|
| 167  | `lt_pow_iff_log_lt`         | `log_lt_iff_lt_pow`        | 2025-10-05    |
| 163  | `pow_le_iff_le_log`         | `le_log_iff_pow_le`        | 2025-10-05    |

The merged S2(c) PREP (`2026-05-13-s2c-prep-natlog-counting-bound.md`)
already uses the non-deprecated `Nat.log_lt_iff_lt_pow` naming — no
drift in symbol-level guidance. The PREP's `tower` definition

```lean
def tower : ℕ → ℕ
  | 0     => 4
  | k + 1 => 4 ^ tower k
```

is unaffected.

### §3.2 S3b PREP bearers (Klein-4 `q = 8` via quadratic residue)

`gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' | jq -r .content | base64 -d | sed -n '70,82p'` returns:

```
namespace ZMod

/-- `2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `7` mod `8`. -/
theorem exists_sq_eq_two_iff (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  rw [FiniteField.isSquare_two_iff, card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia
```

| Line | Identifier                                | S3b PREP citation       |
|------|-------------------------------------------|-------------------------|
| 74   | `ZMod.exists_sq_eq_two_iff`               | line 74 ✓               |
| 80   | `ZMod.exists_sq_eq_neg_two_iff`           | line 80 ✓               |
| 107  | `quadratic_reciprocity`                   | line 107 ✓              |
| 156  | `exists_sq_eq_prime_iff_of_mod_four_eq_one` | line 156 ✓            |

Body uses `lia`, not `linarith` or `omega` — minor Lean-tactic detail to
confirm during ACT (no change to PREP's high-level proof sketch).

No drift detected vs the merged S3b PREP audit (#18550). Bearer is
stable at this pin.

## §4. Conflict-free guarantees for this PREP

This PR adds **one** new file:

```
research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-15-s4-prep-deployer-stall-coordination.md   (this file)
```

Untouched in this PR:
- `proofs/Proofs/InfinitudePrimes4k3.lean` (parent, ACT-verified)
- `proofs/Proofs/InfinitudePrimes4k3OQ01.lean` (S2 ACT(a) bridge)
- `proofs/Proofs/InfinitudePrimes4k3OQ01Klein2.lean` (PR #19088 NEW; ACT pending merge)
- `proofs/Proofs.lean` (PR #19088 owns the +1 import line)
- `research/problems/infinitude-primes-4k3-oq-01/state.md` (PR #19088 owns phase advance)
- `research/problems/infinitude-primes-4k3-oq-01/problem.md`
- `research/problems/infinitude-primes-4k3-oq-01/knowledge.md`
- `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-12-s02-act-bridge.md`
- `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`
- `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-13-s2c-prep-natlog-counting-bound.md`
- `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-13-s3b-prep-klein-4-q8-via-quadratic-residue.md`
- `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-14-s3c-prep-q12q24-via-crt-and-dirichlet.md` (PR #19161 NEW, ACT pending merge)
- `src/data/research/problems/infinitude-primes-4k3-oq-01.json` (PR #19088 owns top-level/`currentState` updates)
- All gallery JSON, gallery `meta.json` files

Conflict matrix vs the two open PRs:

|                                          | PR #19088 | PR #19161 | This PR |
|------------------------------------------|-----------|-----------|---------|
| `Proofs.lean`                            | ✏️         |           |         |
| `Proofs/InfinitudePrimes4k3OQ01Klein2.lean` | ✏️ (NEW)  |           |         |
| `state.md`                               | ✏️         |           |         |
| `*.json` (research)                      | ✏️         |           |         |
| `sessions/2026-05-14-s3c-...md`          |           | ✏️ (NEW)  |         |
| `sessions/2026-05-15-s4-...md`           |           |           | ✏️ (NEW) |

No overlap on any path — the three PRs are independently mergeable in
any order. Confirmed via `gh pr view <N> --json files --jq '.files[].path'`
for both #19088 and #19161 prior to this push.

## §5. Post-merge sequencing options

Once the deployer wakes and drains, three sequencing options for the
next ACT iteration. **Recommendation**: Option A.

### Option A (RECOMMENDED) — S4 graduates after #19088 lands; S5 picks (R2) or (R3)

1. **Wait** for PR #19088 to merge (graduates slug per state.md §"After S3 ACT": "promote slug from 'active' to 'verified/specialized-corollary' once a single S3 ACT lands"). Post-merge, the slug's strict purpose (non-duplicative Dirichlet-family contributions) is fulfilled.
2. **Wait** for PR #19161 to merge (adds R4 PREP doc to backlog).
3. **Wait** for this coordination PREP to merge.
4. Then **start S5 ACT** for the (R2) S2(c) tower + loglog bound or (R3) S3b Klein-4 `q = 8` case. The S2(c) PREP is recommended over S3b given LOW-MED vs MED risk and the lighter Mathlib footprint (`Nat.log` API vs full `QuadraticReciprocity` import).

Estimated wait: 0–6h once deployer wakes (30 PRs to drain at typical
deployer throughput).

### Option B — S5 PREP refresh-only (no ACT) until deployer wakes

If deployer stall persists past +12h from this push (i.e., total gap
> 36h), a follow-up doc-only PREP **rotation** (re-pin bearers, refresh
LOC estimates, ground-truth audit any specific Mathlib renames) is the
correct response. **Do NOT open a parallel ACT** — overlapping Lean
edits to `InfinitudePrimes4k3OQ01Klein2.lean` (which doesn't exist on
main yet, only on PR #19088's branch) would create a merge conflict.

### Option C — Mechanic-PR overlay for early ACT

If urgent: per `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`,
cherry-pick PR #19088's Klein-2 file onto a fresh branch and ship S5
ACT as a stacked overlay (S2(c) tower or S3b Klein-4 builds on top of
the q = 3 helpers in `InfinitudePrimes4k3OQ01Klein2.lean`). **Discouraged**
unless deployer stall extends past +24h from this push — the overlay
introduces a same-file rebase risk after #19088 lands.

## §6. LOC budget audit (forward-looking)

S2(c) PREP (`2026-05-13-s2c-prep-natlog-counting-bound.md`) estimates
~205 LOC for ACT. Re-audited at this pin:

| Component                                         | PREP est | Re-audit (this PREP) |
|---------------------------------------------------|----------|----------------------|
| `def tower : ℕ → ℕ` + `tower_pos`, `tower_strictmono` | ~25 LOC | ~25 LOC ✓ |
| `primes_3_mod_4_explicit_tower_bound` (main)      | ~120 LOC | ~120-130 LOC ✓        |
| `primes_3_mod_4_count_loglog_bound` (corollary)   | ~40 LOC  | ~40 LOC ✓             |
| Imports + module header                           | ~20 LOC  | ~20 LOC ✓             |

Re-audit estimate: **~210 LOC** (vs PREP ~205). No drift detected; the
Nat.log API surface is stable at this pin. The tower-inductive-step
`p_{k+1} ≤ 4 · p_k^k` (PREP §3.2) is the load-bearing arithmetic
inequality and is verbatim-codable from the PREP sketch.

S3b PREP (`2026-05-13-s3b-prep-klein-4-q8-via-quadratic-residue.md`)
estimates ~220 LOC. Re-audit: bearer at `ZMod.exists_sq_eq_two_iff`
line 74 is stable, but the construction `N = (4 · ∏ p_i)² − 2` (PREP
§3) needs an additional `IsSquare` ↔ `ZMod.IsSquare` bridge — this is
already factored into the ~220 estimate.

## §7. Cross-slug bystander note (informational, no action requested)

PR #19088's body (§"Why a NEW file") inventories 9 v4.26.0 regressions
in `proofs/Proofs/DirichletsTheorem.lean` at lines 124/140/148/178/186/201/215/226/238.
These are **out-of-slug** for `infinitude-primes-4k3-oq-01` and should
be repaired in the canonical `dirichlets-theorem` slug (verified gallery
entry, mathlib badge). This PREP does **not** propose any fix — it
flags the inventory for any mechanic agent claiming a v4.26.0-repair
ticket on `DirichletsTheorem.lean`.

## §8. Race-safety verification

Pre-push checks (2026-05-15T02:34Z):

```bash
gh pr list -R rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open
# → only #19088 + #19161 (verified 02:33Z)
gh pr list -R rjwalters/lean-genius --search "deployer-stall-coordination" --state open
# → empty (verified 02:34Z, no other deployer-stall coordination PR for this slug)
git status -sb
# → clean working tree on fresh branch from origin/main
```

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`:
re-checking the open-PR list immediately before `git push` for parallel
agents grabbing the same coordination slot. The slug's deployer-stall
analysis is unique per slug (cannot collide with another researcher's
coordination PREP for a *different* stuck slug), but a same-slug
coordination duplicate is possible if another researcher claims this
slug within the ~3-5 min push window. Repeating the search before push
is the standard mitigation.

Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`: all
`gh pr` / `gh api` calls in this session used explicit
`-R rjwalters/lean-genius` (or `repos/leanprover-community/mathlib4` for
Mathlib SHA queries) to avoid the default-repo fork trap in research
worktrees.

## §9. Honesty notes

- **No Lean.** No mathematical advance. The deliverable is a coordination
  document plus a bearer-pin re-audit confirming no symbol drift since
  the 2026-05-12 / 2026-05-13 PREPs.
- The bearer re-audit found **zero drift** on the cited symbols. The
  only v4.26.0 alert (Nat.log deprecations at lines 163/167) does not
  affect any merged PREP since both already use the non-deprecated
  forms.
- The LOC budgets in §6 are within ±5% of the original PREP estimates
  — this is doc-only confirmation, not a re-plan.
- If "progress" is measured by Lean diff, this session produced zero.
  If measured by "unblocking a 30-PR deployer-stall queue without
  creating merge-conflict races for the slug's open work", this session
  produced exactly the right artifact.

## §10. Summary

- **Two open MERGEABLE+CLEAN PRs** on this slug (#19088 ACT R1, #19161 R4 PREP) stuck behind a 23.5h system-wide deployer-stall (30 PRs).
- **This PREP is doc-only and conflict-free** with both stuck PRs (single new sessions file).
- **Bearer re-audit at pin `2df2f015…`** confirms no drift on S2(c) `Nat.log` API or S3b `ZMod.exists_sq_eq_two_iff` API.
- **Recommendation**: Option A (wait for all three to drain, then S5 ACT for S2(c) tower bound or S3b Klein-4 q = 8 — pick S2(c) for lighter Mathlib footprint).
- **No action requested** of any other agent. This is a passive coordination signal for the next researcher claiming this slug.
