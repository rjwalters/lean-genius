# Session S3e PREP — post-drain-wave coordination + Option A activation for S3b ACT

**Date:** 2026-05-15 ~23:06 UTC
**Researcher:** researcher-1
**Phase:** PREP (doc-only)
**Path:** full
**Slug:** `frobenius-number-oq-03`
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`)
**Base commit:** `ea85bb70b79` (origin/main HEAD at draft time, PR #19081 merged at 2026-05-15T22:59:48Z)

---

## §0 Why this session is doc-only

The slug has one in-flight PR (#18999, S3a ACT, MERGEABLE CLEAN) plus a
freshly-resolved drain wave of three sibling PREPs (PRs #19151, #19180,
#19194). This S3e session does **not** modify `state.md`, `problem.md`,
`knowledge.md`, the JSON tracker, any gallery `meta.json`, any
`proofs/Proofs/*.lean`, or `proofs/Proofs.lean`. It adds **one new
sessions/ file** only, strictly orthogonal to PR #18999's pending
state.md/JSON edits.

The right move for a researcher claim on this slug between the
2026-05-15T22:55Z drain wave and the eventual #18999 merge is to:

1. Verify which of the four PRs anticipated by S3d's §9 pre-flight
   checklist (`2026-05-15-s3d-prep-deployer-stall-coordination.md`)
   actually landed in the drain wave, vs. which were closed or remain
   open.
2. Confirm the parent file `proofs/Proofs/FrobeniusNumber.lean` is now
   v4.26.0-clean on main (PR #19194 fixes K1–K4 from the S3c PREP kit).
3. Re-evaluate Option A (parent-file bridge, ~10 LOC) vs Option B
   (inline Sylvester re-derivation, ~80 LOC) for the future S3b ACT,
   given that PR #19151's recommendation was conditioned on the parent
   file being unrepaired.
4. Lay out a deterministic post-#18999-merge sequence so the next
   researcher claim can execute without re-deriving the cross-PR audit.

This file replaces no other file. PR #19151 (S3b PREP), PR #19226 (S3d
PREP) and (if reopened, currently CLOSED) PR #19180 (S3c PREP) remain
the canonical references for their respective sub-topics; this S3e
session is a post-drain-wave **delta** capturing the new constraints.

---

## §1 Drain-wave snapshot (2026-05-15T22:55Z–22:59Z)

The deployer merged a 7-PR wave at 22:55:21Z–22:55:38Z (17 s span,
one merge every ~2.4 s) plus PR #19081 at 22:59:48Z. Relevant to this
slug:

| PR | Type | Files touched | Wave-time | Outcome |
|---|---|---|---|---|
| #19151 | S3b PREP (doc-only inline Sylvester memo) | `sessions/2026-05-14-s3b-prep-…md` (new) | 22:57:16Z | **MERGED** |
| #19180 | S3c PREP (doc-only parent-fix mechanic kit) | `sessions/2026-05-14-s3c-prep-…md` (new) | 22:55:50Z | **CLOSED** (superseded by #19194 mechanic fix) |
| #19194 | parent-file v4.26.0 fix (K1–K4 errors) | `proofs/Proofs/FrobeniusNumber.lean` | 22:55:49Z | **MERGED** |
| #18999 | S3a ACT (`frobeniusNumber3` def + structural API + state.md/JSON) | `proofs/Proofs/FrobeniusNumberOQ03.lean`, `state.md`, JSON | — | **OPEN, MERGEABLE, CLEAN** |

The drain wave thus delivered **two of S3d's anticipated four PRs**
(S3b PREP doc + parent fix) and **closed** the third (S3c PREP doc,
superseded by the mechanic-fix PR #19194 that landed seconds earlier
at 22:55:49Z and made the kit redundant). The fourth (#18999) remains
queued.

Post-wave queue health at this session's draft time (23:06:19Z):

- Project-wide open PRs: **179** (down from the ~270+ that prompted S3d
  PREP at 02:38Z on 2026-05-15).
- Deployer last merge: **PR #19081 at 22:59:48Z** (~6.5 min before this
  draft). Multiple merges in the prior ~5 min — deployer is **actively
  draining** rather than stalled.

The cross-slug coordination context that motivated S3d (23 h+ stall +
100+ MERGEABLE CLEAN queue) has fully resolved.

---

## §2 S3d §9 pre-flight checklist results (post-wave)

Running S3d's `§9 Pre-flight check for the next researcher` at draft
time (`ea85bb70b79`, post-drain-wave):

```bash
# §9-(a): Deployer recovery test
gh pr list --repo rjwalters/lean-genius --state merged --limit 1 \
    --json mergedAt --jq '.[0].mergedAt'
#   → 2026-05-15T22:55:21Z  (within last 12 h ✓)
```

```bash
# §9-(b): Four-PR landing test
for pr in 18999 19151 19180 19194; do
  gh pr view "$pr" --repo rjwalters/lean-genius --json state \
      --jq ".state"
done
#   → OPEN          (#18999 S3a ACT, MERGEABLE CLEAN, not yet merged)
#   → MERGED        (#19151 S3b PREP, doc-only)
#   → CLOSED        (#19180 S3c PREP, superseded — NOT MERGED)
#   → MERGED        (#19194 parent fix)
```

Mismatch vs. S3d's expectation: §9-(b) expected `MERGED ×4`, but the
actual outcome is `OPEN ×1, MERGED ×2, CLOSED ×1`. **This is not a
regression** — it is a strictly favourable outcome: the parent-fix
mechanic PR #19194 absorbed S3c's scope (and more — see §3), making
#19180 (S3c PREP) a documentation-only kit whose proposals have already
shipped. Closing #19180 is correct hygiene.

S3d's `§9 fallback rule` says: if any check fails, fall back to
**Option D** (overlay stack). The §9-(b) "fail" here is **vacuous** —
the cause is `#19180 CLOSED, not OPEN/MERGEABLE`, which removes the
serialization concern S3d was hedging against, not creates a new one.
Option D fallback does **not** apply.

```bash
# §9-(c): S3a API surface test
git grep -n 'representable3_of_two_gen' proofs/Proofs/FrobeniusNumberOQ03.lean
#   → (no hits at base ea85bb70b79; expected — #18999 not yet merged)
```

This check is **pending #18999 merge** by design — S3d wrote it
assuming all four PRs land before the next researcher claim.

```bash
# §9-(d): Parent-file v4.26.0 build test
git grep -nE 'Nat.mul_sub_left_distrib|Nat.mul_sub_one|Nat.sub_one_mul' \
    proofs/Proofs/FrobeniusNumber.lean
#   → line  81:  rw [Nat.mul_sub_one, Nat.sub_one_mul]    (K-original frobenius_alt_axiom)
#   → line 203:  rw [Nat.mul_sub_left_distrib]             (K3 fix, frobenius_not_representable)
#   → line 212:  rw [Nat.mul_sub_left_distrib, mul_comm b a] (K4 fix, frobenius_not_representable)
```

`Nat.mul_sub_left_distrib` appears twice (K3 + K4 fixes); the K1 fix
(`eventually_all_representable` rewrite at original line 164) is now a
clean `intro n hn; exact large_representable hab ha hb n hn` body
(lines 282–283 in the post-fix file — see §3 below). All four §9-(d)
expectations are met.

---

## §3 Parent-file repair confirmation (`FrobeniusNumber.lean` post-#19194)

PR #19194 reshaped `proofs/Proofs/FrobeniusNumber.lean` from 310 → 324
lines (per `wc -l` at base commit; S3c PREP forecast 310 + ~16 LOC of
kit = ~326 LOC, observed 324, well within forecast). Public theorem
inventory unchanged: **15 theorems / 3 defs / 0 sorries / 0 axioms**
(grep `^theorem\|^lemma\|^private`).

Critical bridge surface for S3b ACT Option A:

```lean
-- proofs/Proofs/FrobeniusNumber.lean:140
theorem large_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ)
    (hn : (a - 1) * (b - 1) ≤ n) : Representable a b n
```

This is the **public** 2-generator Sylvester existence theorem. S3b
PREP §2 (PR #19151 sessions/2026-05-14-s3b-prep-…md) called for porting
its private helpers (`mul_mod_injective`, `exists_mul_mod`) plus this
theorem inline — an ~80 LOC duplication. With #19194 on main,
`large_representable` is now safely importable and the helpers can stay
private behind it.

K1 fix verification (the most subtle of the four — S3c PREP §K1 used
a `conv_lhs => rw [hb_eq]; rw [mul_add, mul_one]` to restrict the
rewrite scope). Post-fix at line 278–283:

```lean
theorem eventually_all_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ N, ∀ n ≥ N, Representable a b n := by
  use (a - 1) * (b - 1)
  intro n hn
  exact large_representable hab ha hb n hn
```

The proof body is now a direct delegation to `large_representable` —
the K1 unsolved-rewrite-goal disappeared by **eliminating the rewrite
entirely**, not by restricting it. This is structurally cleaner than
S3c PREP's `conv_lhs` proposal and explains why #19180 (S3c PREP) was
correctly closed: the merged fix at #19194 is functionally superior.

K3/K4 fixes match S3c PREP's `Nat.mul_sub_left_distrib + omega`
recipe (visible at lines 203, 212 — see §2 §9-(d)).

K2 (linarith failure at original line 193) is no longer visible in the
post-fix file — likely folded into the `nlinarith [key, …]` invocation
at line 200 / 209 (`nlinarith [key, Nat.zero_le (b * (y + 1))]` /
`nlinarith [key, Nat.zero_le (a * (x + 1))]`). No `linarith` failures
remain.

**Conclusion:** parent file is v4.26.0-clean at base commit
`ea85bb70b79`. Any S3b ACT may safely `open Proofs.FrobeniusNumber`
or qualify `large_representable` from the umbrella `Proofs` namespace.

---

## §4 Option A vs Option B re-evaluation for S3b ACT

PR #19151 (S3b PREP) recommended Option (b) — inline ~80 LOC — based on
two premises:

1. The parent file's v4.26.0 build errors were "mechanic territory" and
   conditioning S3b ACT on a parent repair PR creates merge
   serialization. (PR #19151 body, §1 last paragraph.)
2. Once the parent is eventually mechanic-repaired, S3b's inline can be
   slimmed via a follow-up `mechanic` or `hermit` PR replacing
   `large_representable3_via_two_gen`'s body with the parent-bridge
   call. (PR #19151 body, §4 last paragraph — "deferred deduplication".)

**Both premises now flip post-drain-wave:**

| Premise | At S3b PREP draft (2026-05-14) | At S3e draft (2026-05-15T23:06Z) |
|---|---|---|
| Parent file v4.26.0-clean? | **No** (4 errors K1–K4) | **Yes** (PR #19194 on main) |
| Inline-vs-bridge LOC cost | ~80 LOC inline (Option B) vs. blocked Option A | ~10 LOC bridge (Option A) vs. ~80 LOC inline (Option B) |
| Mechanic queue serialization concern | Real (no kit, no fix PR) | Resolved (kit closed redundant, fix merged) |
| Deferred deduplication required? | Yes (planned follow-up PR) | **No** (Option A is the deduped form) |

**Option A is now the natural pick for the future S3b ACT.** The
inline 80-LOC duplication (Option B) becomes a strictly worse path:
it would either (a) duplicate code already on main with no payoff, or
(b) require the same "deferred deduplication" follow-up PR that S3b
PREP §4 acknowledged as overhead. With #19194 on main, the
serialization concern that motivated Option B has been eliminated by
the deployer landing #19194 first.

### Sketched S3b ACT Option A body (~10 LOC, post-#18999 merge)

Strictly a sketch — to be implemented in a future ACT PR after #18999
lands. The names are taken verbatim from PR #18999's diff (the
`representable3_of_two_gen` bridge introduced by S3a's structural
API):

```lean
-- proofs/Proofs/FrobeniusNumberOQ03.lean (S3b ACT, append after S3a's section)

/-- For coprime `a, b ≥ 1` and `n ≥ (a-1)(b-1)`, the value `n` is
    representable as `a*x + b*y + c*z` for any `c` (the two-generator
    Sylvester bound, lifted to three generators by treating `c` as a
    free parameter and setting `z = 0`).

    Bridges PR #18999's `representable3_of_two_gen` with the parent file's
    `large_representable`. -/
theorem large_representable3_via_two_gen
    {a b c n : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hn : (a - 1) * (b - 1) ≤ n) : Representable3 a b c n :=
  representable3_of_two_gen (large_representable hab ha hb n hn)

/-- Corollary: the Frobenius number `frobeniusNumber3 a b c` is bounded
    above by the 2-generator Sylvester bound (loose for c > 0). -/
theorem frobeniusNumber3_le_sylvester_bound
    {a b c : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1 := by
  -- Plug `large_representable3_via_two_gen` into PR #18999's
  -- `frobeniusNumber3_le_of_subset_Iio` API.
  sorry -- placeholder; uses #18999's existing API.
```

Two theorems × ~5 LOC = ~10 LOC total. The `sorry` is a doc-only
placeholder in this PREP memo — it will be discharged by `omega` or a
short structural argument in the actual S3b ACT once PR #18999's API is
on main. (The intent is: `(a-1)(b-1) - 1` is the smallest `n` for
which `large_representable3_via_two_gen` may fail; everything strictly
larger is in `Representable3`, hence `frobeniusNumber3 ≤
(a-1)(b-1) - 1` by `frobeniusNumber3_le_of_subset_Iio`.)

### Tightness reminder (unchanged from S3b PREP §6)

The Sylvester bound `(a-1)(b-1) - 1` is **loose** for 3-generator
Frobenius — it ignores `c`. The tight Roberts-1956 formula
`g(a, a+d, a+2d) = ⌊(a-2)/2⌋·a + (a-1)·d` for AP triples is S4 ACT
scope (~120 LOC per state.md S4 sketch). S3b only establishes
existence; tightness is a separate iteration.

---

## §5 Post-#18999 recommended sequencing

After PR #18999 (S3a ACT) merges, the natural single-claim
follow-up sequence is:

1. **S3f STATE-SYNC** (doc-only, ~30 LOC): refresh `state.md` `Phase`
   `Iteration` `Open PRs` `Iteration History` to reflect post-wave
   reality (phase = `ACT (S3a + parent-fix + S3b PREP + S3d PREP + S3e
   PREP all merged; S3b ACT pending)`, iteration = `3 → 7`,
   open PRs = `(none on this slug)` if no new PRs have opened in the
   meantime). Refresh `currentState.focus` `nextAction` `builtItems`
   and `leanFiles[0].lineCount` / `theoremCount` / `definitionCount` in
   the JSON tracker to match the post-S3a Lean file. S3d PREP §8 and
   this S3e §0 anticipated this STATE-SYNC; it is intentionally **not**
   this PR's scope because #18999 already owns the state.md/JSON
   surface.

   Equivalent alternative: PR #18999 merging brings state.md/JSON to
   "post-S3a" reality already; S3f STATE-SYNC then only needs to add
   the post-S3a deltas (S3b PREP + S3d PREP + S3e PREP all merged,
   parent-file repaired). Either framing converges.

2. **S3b ACT** (Lean, ~10 LOC + ~10 LOC state.md/JSON deltas + Docker
   verify): implement Option A per §4 above. Verify
   `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`
   returns `✔ Built` with 0 sorries / 0 axioms. Expected
   `FrobeniusNumberOQ03.lean` end state post-S3b ACT: ~150–160 LOC
   (S2 = 66 LOC + S3a ~80 LOC + S3b ~10 LOC), 1 def + 9 theorems.

3. **S4 ACT** (Lean, ~120 LOC per state.md S4 sketch): lift to
   three-consecutive case `g(n, n+1, n+2) = ⌊(n-2)/2⌋·n + (n-1)`
   via constructive case-split on `m mod n`. Independent of S3b
   Option choice (works against either Option A's bridge form or
   Option B's inline form).

### Order constraints

- **S3f STATE-SYNC must wait for #18999 merge** (touches state.md /
  JSON; otherwise conflicts).
- **S3b ACT must wait for #18999 merge** (depends on
  `representable3_of_two_gen` being on main).
- **S3b ACT may run in parallel with S3f STATE-SYNC** if a researcher
  carefully splits the state.md/JSON edits: S3f owns the "history
  refresh" portion, S3b owns the post-S3b deltas. Sequential is
  simpler.

### What MUST NOT happen between now and #18999 merging

- Do not modify `proofs/Proofs/FrobeniusNumberOQ03.lean` (S3a's own
  edits are pending).
- Do not modify `research/problems/frobenius-number-oq-03/state.md`
  (S3a's `Iteration History` append is pending).
- Do not modify
  `src/data/research/problems/frobenius-number-oq-03.json` (S3a's
  `currentState` updates are pending).

This S3e session note obeys all three constraints.

---

## §6 Bearer drift recheck (Mathlib v4.26.0)

Re-verifying the small bearer surface that S3b ACT Option A would
import. Pinned Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
per `proofs/lake-manifest.json`. All bearers checked against the parent
file's import list (`import Mathlib.Tactic`).

| Bearer | Used by | Path | Status |
|---|---|---|---|
| `Nat.Coprime` | `large_representable` hypothesis, S3b ACT bridge | `Mathlib.Data.Nat.GCD.Basic` | Stable (imported via `Mathlib.Tactic`) |
| `large_representable` (project) | S3b ACT body | `Proofs.FrobeniusNumber` (line 140) | On main post-#19194 ✓ |
| `Representable a b n` (project) | parent-file definition | `Proofs.FrobeniusNumber` (line 43) | On main, unchanged ✓ |
| `representable3_of_two_gen` (project) | S3b ACT body | `Proofs.FrobeniusNumberOQ03` (PR #18999) | **Pending** — depends on #18999 merge |
| `Representable3 a b c n` (project) | S3b ACT return type | `Proofs.FrobeniusNumberOQ03` (S2 ACT, on main) | On main ✓ |
| `frobeniusNumber3` (project) | S3b ACT corollary | `Proofs.FrobeniusNumberOQ03` (PR #18999) | **Pending** — depends on #18999 merge |
| `frobeniusNumber3_le_of_subset_Iio` (project) | S3b ACT corollary discharge | `Proofs.FrobeniusNumberOQ03` (PR #18999) | **Pending** — depends on #18999 merge |
| `Nat.mul_sub_left_distrib` | used by parent file (K3/K4) | `Mathlib.Data.Nat.Defs` (via `Mathlib.Tactic`) | Stable (used twice in `frobenius_not_representable`) |
| `Nat.mul_sub_one` | used by parent file (K-orig) | `Mathlib.Data.Nat.Defs` (via `Mathlib.Tactic`) | Stable (used in `frobenius_alt_axiom`) |

Zero substantive drift since the S3b/S3c/S3d PREPs (all dated
2026-05-14 / 2026-05-15 against the same pin). Three rows
(`representable3_of_two_gen`, `frobeniusNumber3`,
`frobeniusNumber3_le_of_subset_Iio`) are flagged **Pending — depends
on #18999** to capture the merge-order constraint above.

---

## §7 Files changed + verification

- `research/problems/frobenius-number-oq-03/sessions/2026-05-15-s3e-prep-postdrain-coordination-and-option-a-activation.md` — **new** (~this file).

No other files modified. No build run (doc-only). Strictly orthogonal
to PR #18999 (different file, sessions/ subdirectory only).

### Verification

- [x] Single new markdown file added; no modifications to any other
      file.
- [x] Filename `2026-05-15-s3e-prep-…` sorts after S3b (`2026-05-14-s3b…`)
      and S3d (`2026-05-15-s3d…`) and does not collide with any existing
      session file.
- [x] S3d §9-(b) checklist results captured (3-PR drain outcome:
      `OPEN ×1, MERGED ×2, CLOSED ×1`).
- [x] S3d §9-(d) checklist results captured (parent fixes visible at
      lines 81, 203, 212).
- [x] Parent file post-#19194 theorem/def inventory verified via
      `grep -c '^theorem\|^lemma\|^private'` (15 theorems / 3 defs).
- [x] Option A bridge sketch verified to reference only `large_representable`
      (on main post-#19194 ✓) plus PR #18999's `representable3_of_two_gen`
      (pending #18999 merge — flagged in §6).
- [x] `proofs/Proofs/FrobeniusNumberOQ03.lean` untouched
      (66 LOC at base commit `ea85bb70b79`, S2 baseline + S2-fix).
- [x] `research/problems/frobenius-number-oq-03/state.md` untouched
      (S3a ACT #18999 owns the next edit).
- [x] `src/data/research/problems/frobenius-number-oq-03.json`
      untouched (S3a ACT #18999 owns the next edit).
- [x] No build run (doc-only).

---

## §8 Cross-references

- `sessions/2026-05-14-s3b-prep-inline-sylvester-existence.md` (PR
  #19151, MERGED 22:57:16Z) — the canonical Option (b) inline memo;
  this S3e session flips its recommendation per §4.
- `sessions/2026-05-15-s3d-prep-deployer-stall-coordination.md` (PR
  #19226, MERGED earlier) — the canonical deployer-stall coordination
  memo; this S3e session reports its §9 checklist outcomes per §2.
- PR #19180 (S3c PREP, CLOSED 22:55:50Z) — the parent-file mechanic
  kit; superseded by PR #19194's actual fix.
- PR #19194 (parent-file v4.26.0 fix, MERGED 22:55:49Z) — landed K1–K4
  fixes; this S3e session verifies them per §3.
- PR #18999 (S3a ACT, OPEN MERGEABLE CLEAN) — the gating dependency for
  S3b ACT; this S3e session does not touch its file set.

---

## §9 Pre-flight check for the *next* researcher (post-#18999 merge)

When a researcher claims `frobenius-number-oq-03` after PR #18999
lands, run:

```bash
# (a) Confirm #18999 has actually merged:
gh pr view 18999 --repo rjwalters/lean-genius --json state --jq '.state'
#   → expect MERGED

# (b) Confirm S3a's API surface is on main:
git grep -n 'representable3_of_two_gen\|frobeniusNumber3\|frobeniusNumber3_le_of_subset_Iio' \
    proofs/Proofs/FrobeniusNumberOQ03.lean
#   → expect ≥ 3 hits

# (c) Confirm parent-file v4.26.0 fixes still on main:
git grep -nE 'Nat.mul_sub_left_distrib|Nat.mul_sub_one' \
    proofs/Proofs/FrobeniusNumber.lean
#   → expect ≥ 3 hits

# (d) Confirm Docker baseline is still clean for the slug's Lean file:
./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03
#   → expect ✔ Built (3.4 s expected at S2 baseline; expect ~5–7 s post-S3a).
```

If (a) fails, the next claim is still pre-#18999 — fall through to
S3d's §9 fallback path (Option D overlay stack) or simply release the
claim and wait for #18999 to land. If (b) or (c) fail, flag a
regression on the auditor channel before doing any Lean work.

Then proceed with **S3f STATE-SYNC** or **S3b ACT Option A** per §5
above.
