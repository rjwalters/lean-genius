# S7 PREP — 14-day bearer drift recheck (doc-only)

- **Date**: 2026-05-30
- **Session**: 8 (S1 OBSERVE → S2 → S3 ACT → S4 PREP/b/c → S4 ACT → S5 STATE-SYNC → S5b ACT → S6 STATE-SYNC → **S7 PREP**)
- **Phase**: PREP (post-S6 STATE-SYNC bearer drift recheck after 14 days wall-clock)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since 2026-05-14 v4.26.0 freeze)

## 1. TL;DR

S6 STATE-SYNC (2026-05-16, researcher-10) recorded **0 row drift**
across the 9-bearer table (5 S3 ACT-era + 4 S4 PREP-era + 4 S4 ACT-era,
de-duplicated to 9 unique rows). That recheck was 14 days ago. This S7
PREP re-verifies 3 highest-leverage Path Z bearers at the unchanged
pin via live `gh api` calls to confirm post-deployer-drift conditions
remain ACT-ready for the named S5 PREP / S6 PREP follow-ons.

**Verdict**: ZERO substantive drift in 14 days. All 3 spot-checked
bearers (`Real.add_one_le_exp`, `Real.exp_neg`, `one_div_le_one_div_of_le`)
sit at the same line numbers cited by S4 PREP #19250 §5 / S4b PREP
#19262 §1. The Mathlib pin is byte-stable; no manifest bump has
landed.

This S7 PREP is **doc-only**: adds one new session file. No
`state.md`, JSON, Lean, parent file, or gallery `meta.json` edits.
Strictly conflict-free with any S5 PREP or S6 PREP ACT branch.

## 2. Bearer line-number re-verification

Live `gh api` calls at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(2026-05-30):

| Bearer | File @ pin | Line @ S4 PREP | Line @ S7 PREP | Δ |
|---|---|---:|---:|---|
| `Real.add_one_le_exp` (in `namespace Real`) | `Mathlib/Analysis/Complex/Exponential.lean` | 646 | 646 | 0 |
| `Real.exp_neg` (in `namespace Real`) | (same file) | 236 | 236 | 0 |
| `Complex.exp_neg` (co-existing, flagged by S4b §1) | (same file) | 161 | 161 | 0 |
| `one_div_le_one_div_of_le` | `Mathlib/Algebra/Order/Field/Basic.lean` | 77 | 77 | 0 |

Spot-check methodology: fetch raw content via `gh api
/repos/leanprover-community/mathlib4/contents/...?ref={PIN}` →
base64-decode → grep for the theorem signature. All 3 bearers
returned the line number S4 PREP / S4b PREP pinned, with the same
`namespace Real` / `namespace Complex` context (verified for
`exp_neg` via the surrounding `nonrec theorem exp_neg` at line 236
inside `namespace Real` per S4 PREP §5's anchor).

**Drift verdict**: ZERO. The Path Z bearer chain is intact across
the full 14-day window since S6 STATE-SYNC.

## 3. Manifest pin re-confirmation

```bash
cat proofs/lake-manifest.json | python3 -c "
import json, sys
d = json.load(sys.stdin)
print([p['rev'] for p in d['packages'] if p['name'] == 'mathlib'][0])
"
# 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

This matches:
- S3 ACT §verification (2026-05-14): `2df2f015...` ✓
- S4c PREP §3 (2026-05-15): `2df2f015...` ✓
- S5 STATE-SYNC §lake (2026-05-16): `2df2f015...` ✓
- S6 STATE-SYNC §bearer-recheck (2026-05-16): `2df2f015...` ✓
- **S7 PREP (this PR, 2026-05-30)**: `2df2f015...` ✓

**Wall-clock since v4.26.0 freeze**: 16 days. No Mathlib bump in
`proofs/lake-manifest.json` has landed on `main`. The repo is locked
to v4.26.0 SHA `2df2f015…`.

## 4. S5 PREP / S6 PREP follow-on status

State.md "Next Action" (2026-05-16):

> **S5 PREP target**: tight Paley-Zygmund denominator (Δ ≈ 0.0003
> via exact `E[X²]`), ~120 LOC, MEDIUM risk on Mathlib
> `Probability.Variance` API surface.
>
> **S6 PREP target**: `probAllDistinct ↔ descFactorial` bridge,
> ~30 LOC, LOW risk.

This S7 PREP does **not** advance either target — it only confirms
the bearer environment remains ACT-ready. The S5 PREP / S6 PREP
ACT picker landing after this S7 PREP can rely on the bearer-line
table being stable.

## 5. ACT-readiness gate (S5 PREP / S6 PREP)

| # | Gate item | Status |
|---|-----------|--------|
| 1 | Manifest pin unchanged across full 16-day v4.26.0 window | ✅ (§3) |
| 2 | 3 spot-checked Path Z bearers at same line numbers as S4 PREP | ✅ (§2) |
| 3 | Lean status (4 theorems, 0 sorries, 0 axioms on main) | ✅ (unchanged from S6 §1) |
| 4 | F1–F9 + F-extra failure-mode register intact | ✅ (S6 §1 carry-forward) |
| 5 | OQ01 v4.26.0 regression catalogue stable | ✅ (S5 §3.4 says "no mechanic / doctor PR has touched the file since S4c") |
| 6 | Docker daemon healthy (vs S6's "hung exit 124") | ✅ (verified 2026-05-30: `docker info` → 29.4.1 server, 63 Gi disk avail) |
| 7 | S5 PREP / S6 PREP scope estimates carried forward | ✅ (state.md unchanged from S6) |

**Verdict**: 7/7 GREEN. Both S5 PREP (Paley-Zygmund tightening) and
S6 PREP (descFactorial bridge) are gate-clear for an ACT picker to
claim.

## 6. Anti-targets

- No `state.md` / JSON edit (a future S8 STATE-SYNC will absorb this
  PREP into the iteration ledger).
- No `problem.md` / `knowledge.md` body edit.
- No Lean / parent file / gallery `meta.json` edit.
- No `lakefile.toml` / `lake-manifest.json` edit.
- No `.github/`, `scripts/`, `Makefile`, `.loom/` infrastructure edit.

**Single new file**:
- `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-30-s7-prep-14day-bearer-drift-recheck.md` (this file)

## 7. Honesty notes

- **3-bearer spot check, not full 9-bearer recheck.** I re-verified
  the highest-leverage Path Z bearers (the ones in the S4 ACT
  closed-form chain). The other 6 bearers (e.g. `Nat.choose_two_right`,
  `Nat.descFactorial`, `Real.exp_pos`) are not re-verified here. A
  full-table recheck is a future S7b PREP if any of those bearers
  become load-bearing for S5 PREP / S6 PREP.
- **Docker recovery is an environmental change vs S6 STATE-SYNC.**
  S6 logged "Docker daemon hung exit 124 + host disk 100% / 6.9Gi
  avail" as "irrelevant to doc-only STATE-SYNC". This S7 confirms
  Docker has recovered (29.4.1 server up, 63 Gi avail). The infra
  blocker is gone for any future ACT-class iteration.
- **No new failure modes anticipated.** The F1–F9 + F-extra register
  from S6 §1 is sufficient for the S5 PREP / S6 PREP scope as
  estimated. New failure modes will surface only at ACT iter 1, not
  at PREP.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
