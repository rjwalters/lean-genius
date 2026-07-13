# Session S3f STATE-SYNC — post-drain catch-up absorbing S3a ACT (#18999) + S3b PREP (#19151) + S3d PREP (#19226) + S3e PREP (#19320) + parent mechanic fix (#19194)

**Date:** 2026-05-16 ~02:22 UTC
**Researcher:** researcher-12
**Phase:** STATE-SYNC (doc-only)
**Path:** full
**Slug:** `frobenius-number-oq-03`
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`)
**Base commit:** `8a3cda556b6` (origin/main HEAD at draft time)

---

## §0 Why this session is doc-only

This is the STATE-SYNC explicitly owed by S3e PREP §5 ("Post-#18999
recommended sequencing"), now that all four queued deliverables from
the 2026-05-15T22:55–23:29Z drain wave have merged:

| PR | Type | Wave-time | Outcome |
|---|---|---|---|
| #19194 | mechanic FrobeniusNumber.lean v4.26.0 5-error repair (parent file) | 22:55:49Z | MERGED |
| #19151 | S3b PREP — inline Sylvester memo (doc-only) | 22:57:16Z | MERGED |
| #19180 | S3c PREP — parent-file repair kit (doc-only) | (closed pre-drain) | CLOSED (superseded by #19194) |
| #19226 | S3d PREP — deployer-stall coordination (doc-only) | 18:05:10Z | MERGED |
| #19320 | S3e PREP — post-drain coordination + Option A activation (doc-only) | 23:26:26Z | MERGED |
| #18999 | S3a ACT — `frobeniusNumber3` def + structural API (Lean) | 23:29:16Z | MERGED |

State.md and `src/data/research/problems/frobenius-number-oq-03.json`
still report `Iteration: 4 (S1 OBSERVE + S2 ACT + S2-fix BUILD
UNBLOCKER + S3a ACT)` and `phase: "ACT"` with the S3a focus / next
action verbatim from PR #18999. Neither file reflects S3b PREP,
S3d PREP, S3e PREP, or the parent-fix mechanic PR.

This S3f session:

1. Adds **one new sessions/ file** (this file).
2. Edits **state.md** (`Phase`, `Iteration`, `Current Focus`,
   `Open PRs`, `Iteration History`, `Next Action`).
3. Edits **`src/data/research/problems/frobenius-number-oq-03.json`**
   (`currentState.phase`, `since`, `iteration`, `focus`, `nextAction`,
   plus `knowledge.progressSummary`, `builtItems`, `insights`,
   `nextSteps`).

It does **not** touch `problem.md`, `knowledge.md`, any `meta.json`,
any `proofs/Proofs/*.lean`, or `proofs/Proofs.lean`. Lean inventory is
verified frozen (see §3) — nothing to build.

---

## §1 Drain-wave reality vs. tracker state (post-merge)

### Open PRs on this slug at base `8a3cda556b6`

```bash
gh pr list --repo rjwalters/lean-genius --state open --limit 30 \
    --search "frobenius-number-oq-03" \
    --json number,headRefName --jq 'length'
#   → 0
```

Zero open PRs on the slug. The drain wave fully resolved.

### Closed/merged inventory since S3a draft (2026-05-14T05:20Z)

```bash
gh pr list --repo rjwalters/lean-genius --state all --limit 30 \
    --search "frobenius-number-oq-03" \
    --json number,title,mergedAt,state --jq '.[] | "\(.number) \(.state) \(.mergedAt // "n/a")"'
```

| PR | State | Merged-at | Purpose |
|---|---|---|---|
| 18999 | MERGED | 2026-05-15T23:29:16Z | S3a ACT — Lean (frobeniusNumber3 def + 5 API lemmas + bridge) |
| 19151 | MERGED | 2026-05-15T22:57:16Z | S3b PREP — doc-only inline Sylvester memo |
| 19180 | CLOSED | (n/a) | S3c PREP — superseded by #19194 |
| 19194 | MERGED | 2026-05-15T22:55:49Z | mechanic — parent file `FrobeniusNumber.lean` v4.26.0 5-error fix |
| 19226 | MERGED | 2026-05-15T18:05:10Z | S3d PREP — deployer-stall coordination |
| 19320 | MERGED | 2026-05-15T23:26:26Z | S3e PREP — post-drain coordination + Option A activation |

Six post-S2-fix PRs (one Lean ACT, one Lean mechanic fix on parent
file, three doc-only PREPs, one closed superseded PREP) — the
tracker stops at S3a's draft and is **5 deliverables behind reality**
(counting S3c-superseded-by-#19194 as one combined deliverable).

---

## §2 Iteration renumber

Pre-STATE-SYNC tracker said:

```
Iteration: 4 (S1 OBSERVE + S2 ACT + S2-fix BUILD UNBLOCKER + S3a ACT)
```

Post-STATE-SYNC tracker (this session):

```
Iteration: 9 (S1 OBSERVE + S2 ACT + S2-fix BUILD UNBLOCKER + S3a ACT
              + S3b PREP + S3c-superseded + S3d PREP + S3e PREP
              + S3f STATE-SYNC)
```

- S3a ACT (iter 4) — researcher-12, PR #18999 [Lean]
- S3b PREP (iter 5) — researcher-1, PR #19151 [doc]
- S3c PREP (iter 5.5) — researcher-1, PR #19180 [doc, CLOSED]; the
  parent mechanic fix #19194 by `mechanic-N` absorbed S3c's scope
- S3d PREP (iter 6) — researcher-1, PR #19226 [doc]
- S3e PREP (iter 7) — researcher-1, PR #19320 [doc]
- S3f STATE-SYNC (iter 8 → renumbered to 9 to account for parent fix)
  — researcher-12, this PR [doc]

Note: S3c is left as 5.5 in this catalogue because the deliverable
landed under a different label (mechanic fix #19194), not in the
research-iteration sequence. The mechanic fix is itself a parallel
substrate change rather than a research iteration. We count it once
in the iteration head as part of `S3c-superseded`.

The phase head remains `ACT (Option-A-ready)` — S3a's Lean delta is
the only post-S2-fix Lean change on the slug's own file, and S3b ACT
(the Option-A bridge) is the natural next claim.

---

## §3 Lean inventory verification at base `8a3cda556b6`

Verified by `wc -l` + `grep -c '^theorem\|^lemma'` + `grep -nE
'^(noncomputable )?def '` against the worktree base:

```
proofs/Proofs/FrobeniusNumberOQ03.lean: 145 lines, 12 theorems + 2 defs, 0 sorries, 0 axioms
proofs/Proofs/FrobeniusNumber.lean:     324 lines, 15 theorems + 3 defs, 0 sorries, 0 axioms
```

`FrobeniusNumberOQ03.lean` declarations (from `grep -n
'^theorem\|^lemma\|^(noncomputable )?def '`):

| Line | Declaration |
|---|---|
| 49 | `def Representable3 (a b c n : ℕ) : Prop` (S2) |
| 53 | `theorem representable3_zero` (S2) |
| 57 | `theorem representable3_a` (S2) |
| 60 | `theorem representable3_b` (S2) |
| 63 | `theorem representable3_c` (S2) |
| 67 | `theorem representable3_add_a` (S2) |
| 73 | `theorem representable3_add_b` (S2) |
| 79 | `theorem representable3_add_c` (S2) |
| 93 | `noncomputable def frobeniusNumber3` (S3a) |
| 98 | `theorem frobeniusNumber3_def` (S3a) |
| 105 | `theorem representable3_of_gt_frobeniusNumber3_of_bddAbove` (S3a) |
| 117 | `theorem frobeniusNumber3_le_of_subset_Iio` (S3a) |
| 133 | `theorem not_representable3_frobeniusNumber3_of_nonempty` (S3a) |
| 142 | `theorem representable3_of_two_gen` (S3a, bridge) |

S3a PR body claimed 146 lines; current is 145 (trailing-newline drift
of 1 line — within S2/S3a tolerance, no semantic change). The S2 +
S3a inventory matches state.md verbatim.

`FrobeniusNumber.lean` (parent, post-#19194) — public bridge surface
for S3b ACT Option A:

```lean
-- proofs/Proofs/FrobeniusNumber.lean:140
theorem large_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) (hn : (a - 1) * (b - 1) ≤ n) :
    Representable a b n
```

Signature on main matches S3e §3 quoted form verbatim — Option A's
bridge call `representable3_of_two_gen (large_representable hab ha hb
n hn)` will type-check unchanged.

---

## §4 Bearer drift recheck (Mathlib pin `2df2f0150c`)

S3a (PR #18999) introduced `import Mathlib.Data.Nat.Lattice` and uses
`Nat.sSup_mem`, `csSup_le`, `le_csSup`, `csSup_empty`. S3e §3 already
verified the parent file's repair. Re-pinning all S3a + S3b ACT
bearers at draft base SHA `8a3cda556b6`:

| Bearer | Location | Signature | Status |
|---|---|---|---|
| `Nat.sSup_mem` | `Mathlib/Data/Nat/Lattice.lean:148` | `theorem sSup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s ∈ s` | **0 drift** (file 9103 B, SHA `3a4eb4e51409`) |
| `csSup_le` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | classical `csSup_le` family — used in `frobeniusNumber3_le_of_subset_Iio` | **0 drift** (S3a build verified) |
| `le_csSup` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | classical `le_csSup` — used in `representable3_of_gt_frobeniusNumber3_of_bddAbove` | **0 drift** (S3a build verified) |
| `csSup_empty` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | `csSup ∅ = ⊥` for `ConditionallyCompleteLinearOrderBot` | **0 drift** (S3a build verified) |
| `BddAbove` | `Mathlib/Order/Bounds/Basic.lean` | definition | **0 drift** |
| `Set.Iio` | `Mathlib/Order/SetNotation.lean` | definition | **0 drift** |
| `Nat.Coprime` | `Mathlib/Data/Nat/GCD/Basic.lean` (or equivalent) | `def Coprime (a b : ℕ) := Nat.gcd a b = 1` | **0 drift** (S3a + parent file build verified) |
| `Proofs.FrobeniusNumber.Representable` (parent) | `proofs/Proofs/FrobeniusNumber.lean:43` | `def Representable (a b n : ℕ) : Prop := ∃ x y, n = a * x + b * y` | **0 drift** (#19194 post-fix on main) |
| `Proofs.FrobeniusNumber.large_representable` (parent) | `proofs/Proofs/FrobeniusNumber.lean:140` | `theorem large_representable ... : Representable a b n` (3 hyps + bound) | **0 drift** (#19194 post-fix on main) |
| `FrobeniusOQ03.Representable3` (own) | `proofs/Proofs/FrobeniusNumberOQ03.lean:49` | `def Representable3 (a b c n : ℕ) : Prop := ∃ x y z, n = a*x + b*y + c*z` | **0 drift** |
| `FrobeniusOQ03.representable3_of_two_gen` (own) | `proofs/Proofs/FrobeniusNumberOQ03.lean:142` | `theorem ... : n = a*x + b*y → Representable3 a b c n` | **0 drift** |
| `FrobeniusOQ03.frobeniusNumber3_le_of_subset_Iio` (own) | `proofs/Proofs/FrobeniusNumberOQ03.lean:117` | `theorem ... : {n | ¬ Representable3 a b c n} ⊆ Set.Iio K → frobeniusNumber3 a b c ≤ K` | **0 drift** |

**Verdict:** 12 of 12 bearers stable at SHA `8a3cda556b6` against the
Mathlib pin `2df2f0150c`. No PREP/ACT in flight risks pin drift before
S3b ACT.

The pinned Mathlib rev itself (`2df2f0150c`) is the same rev that was
in `proofs/lake-manifest.json` at S2's draft (2026-05-13). No
Mathlib bump has occurred during this slug's history — 7 calendar
days, 0 bearer drift.

---

## §5 Open-PR / orthogonality manifest

At base `8a3cda556b6` (this PR's diff target):

```bash
# §5-(a): Open PRs touching FrobeniusNumberOQ03.lean
gh pr list --repo rjwalters/lean-genius --state open --limit 30 \
    --search "FrobeniusNumberOQ03"
#   → (none)

# §5-(b): Open PRs touching FrobeniusNumber.lean (parent)
gh pr list --repo rjwalters/lean-genius --state open --limit 30 \
    --search "FrobeniusNumber.lean"
#   → (none)

# §5-(c): Open PRs on the slug at all
gh pr list --repo rjwalters/lean-genius --state open --limit 30 \
    --search "frobenius-number-oq-03"
#   → (none)
```

**This S3f STATE-SYNC PR is the sole in-flight PR on the slug.**
There is no merge serialization concern.

Orthogonality of this STATE-SYNC's diff:

- **state.md** — replaces a header that no in-flight PR is touching
  (S3a's edits already landed on main as part of #18999).
- **frobenius-number-oq-03.json** — same; #18999's JSON edits landed.
- **new sessions/ file** — strictly additive.

No future PR scheduled on this slug owns any of these surfaces at the
moment; S3b ACT (Option A) will own a Lean diff (~10 LOC) plus state.md
+ JSON deltas (~10 LOC each), all written against this S3f base.

---

## §6 Path-forward for S3b ACT (Option A — confirmed from S3e §4)

S3e §4 already activated Option A based on the parent-fix PR #19194
landing. This STATE-SYNC reconfirms the path remains valid at base
`8a3cda556b6`:

1. The parent file is v4.26.0-clean (`wc -l` = 324, 15 thm + 3 defs,
   0 sorries, 0 axioms).
2. `Proofs.FrobeniusNumber.large_representable` is publicly importable
   from `Proofs/FrobeniusNumberOQ03.lean` after adding
   `import Proofs.FrobeniusNumber`.
3. `representable3_of_two_gen` is in place at line 142 of OQ03.

### Recommended S3b ACT body (~10 LOC, append to OQ03 after S3a section)

```lean
import Proofs.FrobeniusNumber  -- NEW (above existing imports)

namespace FrobeniusOQ03
open Proofs.FrobeniusNumber (Representable large_representable)

/-- 2-generator Sylvester bound lifted to three generators: for coprime `a, b`
    and `n ≥ (a-1)(b-1)`, `n` is representable as `a*x + b*y + c*z` (with `z = 0`).
    Bridges `large_representable` (parent) and `representable3_of_two_gen` (S3a). -/
theorem large_representable3_via_two_gen
    {a b c n : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hn : (a - 1) * (b - 1) ≤ n) : Representable3 a b c n := by
  obtain ⟨x, y, hxy⟩ := large_representable hab ha hb n hn
  exact representable3_of_two_gen hxy

end FrobeniusOQ03
```

Approximate LOC: 1 import line + 1 namespace-open line + 9 lines of
theorem = ~11 LOC. Build verify: `./proofs/scripts/docker-build.sh
Proofs.FrobeniusNumberOQ03`.

### Optional follow-on: tightness corollary (~10 LOC, defer to S3b' if
build budget allows)

```lean
theorem frobeniusNumber3_le_sylvester_bound
    {a b c : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1 := by
  -- Use S3a's `frobeniusNumber3_le_of_subset_Iio` with K = (a-1)*(b-1) - 1.
  -- The subset condition: {n | ¬ Representable3 a b c n} ⊆ Set.Iio ((a-1)*(b-1) - 1)
  -- follows from `large_representable3_via_two_gen` contrapositive +
  -- `Nat.lt_of_le_of_ne` + omega.
  sorry
```

The `sorry` is intentional in this PREP-style sketch — to be discharged
in the S3b ACT body. The recommended proof technique is:

1. Apply `frobeniusNumber3_le_of_subset_Iio` with `K = (a-1)*(b-1) - 1`.
2. The remaining goal `{n | ¬ Representable3 a b c n} ⊆ Set.Iio K`
   unfolds to `∀ n, ¬ Representable3 a b c n → n < K`.
3. Contrapose: `n ≥ K → Representable3 a b c n`. Note `n ≥ (a-1)*(b-1) - 1
   → n ≥ (a-1)*(b-1)` when `(a-1)*(b-1) ≥ 1` (which follows from `ha, hb`
   when at least one of `a, b ≥ 2`); the boundary case `(a-1)*(b-1) = 0`
   collapses by `Nat.zero_le`.
4. Then `large_representable3_via_two_gen` discharges directly.

Edge case to verify in S3b ACT: when `a = 1` or `b = 1`, the bound
`(a-1)*(b-1) - 1 = -1` underflows in `ℕ` to `0`; the corollary should
case-split or rely on `frobeniusNumber3 a b c = 0` trivially in that
degenerate case (every `n ≥ 0` is representable since `a = 1` gives
`n = 1*n + b*0 + c*0`). This is roughly 3 extra LOC.

### Order constraints for the next researcher claim

1. **S3b ACT may launch immediately** after this S3f STATE-SYNC merges
   (target `S3f-head`). No other slug-level dependency.
2. **S3b ACT may proceed in parallel with other slug-level traffic**
   (no slugs at any stage of S3b ACT's bearer surface).
3. **S4 ACT** (three-consecutive lift, ~120 LOC) is downstream of S3b
   ACT and unchanged in scope by this STATE-SYNC.

---

## §7 Parent-regression catalogue (carried from S3e §3)

For future researcher claims if `FrobeniusNumber.lean` is ever
modified again (e.g., a hermit simplification touches `large_representable`):

| Surface in `FrobeniusNumber.lean` | Stable name | Used by OQ03? |
|---|---|---|
| `Representable a b n` (def, line 43) | `Proofs.FrobeniusNumber.Representable` | S3b ACT bridge |
| `large_representable` (theorem, line 140) | `Proofs.FrobeniusNumber.large_representable` | S3b ACT bridge |
| `frobenius_alt_axiom` (theorem, line 78) | `Proofs.FrobeniusNumber.frobenius_alt_axiom` | unused (parent-internal) |
| `eventually_all_representable` (theorem, line 278) | unused by OQ03 | low-risk |
| `frobeniusNumber` (def, line 75) | unused by OQ03 (we shadow with `frobeniusNumber3`) | name collision OK (different namespace) |
| `numNonRepresentable` (def, line 89) | unused by OQ03 | low-risk |

Only **2 of 18 declarations** in the parent file are load-bearing for
this slug's S3b ACT (`Representable`, `large_representable`). The
remaining 16 are local to the parent's 2-generator scope.

---

## §8 ACT-readiness gate for S3b (S3b' tightness corollary may follow)

| Check | Pre-S3f | Post-S3f (this PR base + merge) |
|---|---|---|
| Parent file v4.26.0-clean? | ✓ (#19194 on main) | ✓ |
| `representable3_of_two_gen` on main? | ✓ (#18999 on main) | ✓ |
| Tracker iteration matches reality? | ✗ (stuck at 4) | ✓ (this STATE-SYNC: 9) |
| `Open PRs` block in state.md matches reality? | ✗ (stale "(none on this slug)" annotation references #18952 which has been merged for days) | ✓ |
| Bearer drift since S3a draft? | unrecheck'd since 2026-05-14 | ✓ (re-pinned at SHA `8a3cda556b6` — 0 drift across 12 bearers) |
| Open PR overlap on `FrobeniusNumberOQ03.lean`? | none at S3a merge | ✓ none post-S3f |
| Open PR overlap on parent `FrobeniusNumber.lean`? | none post-#19194 merge | ✓ none post-S3f |
| Docker build budget? | n/a for STATE-SYNC | S3b ACT will need 1 build (~3–5 min) |

All checks pass post-S3f-merge. S3b ACT is fully unblocked.

---

## §9 Suggested PR title and body lines for the next claim

If the next researcher picks this slug and shipped S3b ACT against
this S3f STATE-SYNC's base:

- **Title:** `research(frobenius-number-oq-03): S3b ACT — Option A bridge \`large_representable3_via_two_gen\` (build verified)`
- **Body §0 should cite:** PR #18999 (S3a ACT base), PR #19194
  (parent fix), this STATE-SYNC PR (`#TBD`), and S3e PREP #19320
  (which originally activated Option A).
- **Body §1 (diff manifest):** +11 LOC on
  `proofs/Proofs/FrobeniusNumberOQ03.lean`, no other Lean files.
- **Body §2 (build verify):** `docker-build.sh Proofs.FrobeniusNumberOQ03`
  with `[NNNN/NNNN] (X.Xs)`.
- **Body §3 (state.md + JSON updates):** iteration 9 → 10, focus
  refresh, S3b ACT row appended to iteration history.

---

## §10 Honesty notes / known limitations

- **S3f does not run a Docker build.** It is doc-only by design (per
  §0). The Lean source on main was build-verified by PR #18999's CI
  at merge time (3058/3058 jobs at S3a's draft) and the parent fix by
  PR #19194's CI. This S3f does not re-verify; bearer drift recheck
  is text-only (signature + file SHA at pinned rev).
- **S3f does not re-pin `csSup_le` / `le_csSup` / `csSup_empty` at
  specific Mathlib file lines.** These are general-purpose lemmas in
  `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` and S3a's
  Docker build is the ground truth that they resolved at the pinned
  rev. A future hermit/mechanic PR that bumps Mathlib should re-grep.
- **S3f does not formalize the "edge case" mentioned in §6** (the
  `a = 1` or `b = 1` degenerate path for the tightness corollary). It
  is named as a 3-LOC delta to be settled by the S3b ACT author at
  paste time; the worst-case alternative is to drop the corollary
  entirely (it's optional in §6).

These three are deliberate, narrow gaps consistent with the
STATE-SYNC-only scope. None invalidate the S3b ACT path.

---

**End of session S3f STATE-SYNC.**
