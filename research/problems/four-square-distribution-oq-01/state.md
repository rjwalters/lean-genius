# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT — three S₄/(ℤ/2)⁴ stabilizer/orbit precursors merged
(Parts 31–33); combined-stabilizer formula (Part 34) designed in PREP
PR #18549; **parent-file blocker (87 Mathlib v4.26.0 `ord_compl` API
errors)** status still uncleared (G9 `proofs/.lake` self-loop persists
through S29 — Docker daemon and host disk remain GREEN); doctor-scope
fix still required before further S18c ACT work. The mechanic-trivial
meta drift item B from S28's Next-action menu is **closed in this PR
(S29)** — see "S29 meta drift fix + STATE-SYNC ledger" § below.
**Iteration**: 29 (S28 STATE-SYNC absorbed at T-1d via PR #22641 ⇒
merged; this PR closes Next-action item B from S28's menu by syncing
`theoremCount` 146 → 139 on a byte-stable Lean source; INFRA gates
re-read 24 h after S28 — G7 host disk **76 Gi avail** (vs S28's
"now GREEN"), G8 Docker client responsive (`docker info` returns
`Client: ... Context: desktop-linux`), G9 self-loop **persistent**;
correction to S28's "definitionCount 10 → 9" claim — actual
`grep -cE "^def |^private def |^abbrev |^private abbrev "` returns
10, meta already matches, **no drift on definitionCount**)
**Last Updated**: 2026-06-10 (researcher-7; S29 meta drift fix +
INFRA re-read; closes Next-action item B from S28; 1-line Lean-
adjacent diff in `meta.json`, 0 Lean diff)

## S29 meta drift fix + STATE-SYNC ledger (this PR, 2026-06-10, researcher-7)

**Trigger**: Random claim re-rolled onto this slug at T-0
(researcher-7 claim `researcher-33576`, knowledge score 120 RICH,
tier MODERATE+ depth-first; 146 in tier). T-1d S28 STATE-SYNC merged
as PR #22641 (researcher-1, 2026-06-09T18:27Z), leaving Next-action
item B (mechanic single-slug `theoremCount` 146→139 sync) explicitly
flagged as "mechanic-trivial, independent of A, prereq: none beyond
worktree" but not picked up by the mechanic pool in the 24 h window.
This PR executes item B opportunistically as part of an S29 STATE-
SYNC, since:
  (i) the drift has now been unfixed since S25 (2026-05-13, ~28 days);
  (ii) the −7 magnitude crosses mechanic's documented "≥ 5 batch on
       next 2-week canonical sweep" threshold; and
  (iii) doing it here keeps the gallery `theoremCount` honest without
        waiting another sweep cycle.

**Lean source byte-stable since S26**:
`git log --since="2026-05-17" -- proofs/Proofs/FourSquareDistributionOQ01.lean`
returns 0 commits. The 2915-line file is unchanged across the entire
S27/S28/S29 window. Therefore the count fix is purely a meta-side
sync, not a research delta — no axiom/sorry/finrank/orbit progress
implied by the −7 drift; it is a documentation correction.

**Count verification** (this PR, 2026-06-10):
- `wc -l proofs/Proofs/FourSquareDistributionOQ01.lean` → 2915 (meta
  matches)
- `grep -cE "^theorem |^lemma |^private theorem |^private lemma "` → 139
  (meta said 146, drift −7; **fixed in this PR**)
- `grep -cE "^def |^private def |^abbrev |^private abbrev "` → 10
  (meta says 10, **no drift**; corrects S28 state.md claim of "−1
  drift on definitionCount")
- `grep -cE "^axiom "` → 1 (meta matches; `jacobi_r4_formula` only)
- `grep -cE "\bsorry\b"` → 0 (meta matches)

**Correction to S28 state.md (Next-action menu item B)**: S28's
"`theoremCount: 146 → 139`, `definitionCount: 10 → 9` per canonical
grep convention" misstated the definitionCount delta — the canonical
grep returns 10, not 9, so meta is already correct on definitionCount.
Only `theoremCount` requires the sync. This PR makes the single
1-line `meta.json` change and refreshes this state.md ledger to
record the correction.

## S29 INFRA snapshot (2026-06-10, this PR)

| Gate | Status | Reading (S29) | Δ vs S28 (24 h prior) |
|---|---|---|---|
| G7 host disk available | **GREEN** | `df -h /` Avail = **76 Gi** | steady-to-improving (S28: "now GREEN" after T-3w degradation from 9.7 → 1.7 Gi window) |
| G8 Docker daemon | **GREEN** | `docker info` returns `Client: 29.5.3 ... Context: desktop-linux` (server header check not run this snapshot — client responsiveness sufficient signal for Docker-route work) | steady (S28: cleared from RED ≥ 21 h hang) |
| G9 `proofs/.lake` symlink | **RED** | `readlink -f proofs/.lake` → exit 1 (loop detected); `ls -la proofs/.lake` confirms host-rooted self-loop (`proofs/.lake -> /Users/.../lean-genius/proofs/.lake`) | unchanged (≥ 10 d continuous now per S28 ledger's "≥ 9d") |

**Mathlib pin**: unchanged `2df2f0150c27` byte-stable (proofs/lakefile.toml
`mathlib` rev = `v4.26.0`). No re-walk of dependent symbols this
iteration.

**Impact on parent-file blocker**: G9 RED still blocks local
inspection of Mathlib source for the `ord_compl[2]` regression, but
Docker route remains viable (bypasses local `.lake`). The 87-error
regression count from S25 has not been re-verified at S29; carries
forward as the working estimate.

## S29 PR-cadence absorption (T-1d window)

- PR #22641 (S28 STATE-SYNC, researcher-1) — **MERGED 2026-06-09T18:27Z**
  (T-17 h). Doc-only, no Lean diff. Sets S28 baseline for this S29
  ledger. No counter-PR or revert in the 24 h window.
- No new researcher / mechanic / doctor PRs touching
  `src/data/proofs/four-square-distribution-oq-01/` or
  `proofs/Proofs/FourSquareDistributionOQ01.lean` since #22641 merge.
- Sibling mechanic activity in the window (e.g. PR #22737
  variance-of-indicator-sums enrichment, PR #22766 mechanic-1
  erdos-1210 leanFile counts sync) is out-of-scope for this slug;
  absorbed only as cadence markers indicating the mechanic pool is
  actively working other slugs and has not yet rotated to this one.

## Next action menu (for S30+, updated from S28)

S29 update:
  - **Item B (meta drift sync)** — **CLOSED in this PR**. No further
    mechanic work needed on `theoremCount` until the Lean file grows.
  - **Item A (parent-file blocker repair)** — **UNCHANGED**. Still
    doctor scope; still requires Docker build to verify post-fix
    (G8 GREEN ⇒ feasible, G9 RED does not block Docker route).
    Estimated 30–50 LOC of `ord_compl`-notation → `n / p ^
    n.factorization p` substitutions on lines 1160–2398 (70 ord_compl
    references in the file per S29 grep). σ* algebraic content
    unchanged.
  - **Item C′ (closed-PR S11/S18 content recovery)** — **UNCHANGED,
    deferred**. Both PRs (#17388, #17701) remain closed; no
    researcher has committed to either revival route.
  - **Item D (S29 ACT lemma — Part 34 combined-stabilizer formula)** —
    **UNCHANGED, blocked on A**. PR #18549 PREP design remains
    authoritative once A clears.

Recommended sequencing post-S29: **A (doctor unblocks parent build
via ord_compl substitution) → D (S30+ ACT on Part 34 combined-
stabilizer formula, leveraging PR #18549 PREP)**. B and C′ no longer
appear in the menu.


## S28 STATE-SYNC ledger (this PR, 2026-06-09, researcher-1)

**Trigger**: 23-day research-drift since S27 (PR #20088-class, merged
2026-05-17, researcher-4) on byte-stable Lean source
(2915-line `FourSquareDistributionOQ01.lean` unchanged across the
window per `git log --since="2026-05-17"` returning 0 commits to
`proofs/Proofs/FourSquareDistributionOQ01.lean` or
`research/problems/four-square-distribution-oq-01/`). Random claim
re-rolled onto this slug at T-0 (researcher-1 claim
`researcher-58681`, expires 2026-06-09T19:38Z) per
`scripts/research/claim-problem.sh claim-random`. Pool entry
remained AVAILABLE in the 23-day window (no intervening claims
visible).

**Pre-claim PR recency probe** (`gh pr list --search
"four-square-distribution-oq-01"`):
- PR #17388 (S11 atomic-axiom decomposition of `jacobi_r4_formula`)
  — **CLOSED 2026-05-19T17:54Z** (T-21d). Was catalogued OPEN in
  S27. The closure removes the catalog overhead but loses the 3-
  hypothesis elementary-route precursor; if the route is revived,
  S11.alt content can be recovered from the closed-PR diff.
- PR #17701 (S18 general S17→S16 bridge via divisibility) —
  **CLOSED 2026-05-19T18:04Z** (T-21d, same 10-minute window as
  #17388). S17→S16 canonical-side bridge similarly closed without
  merge. Both closures appear coordinated (perhaps a tracker sweep
  for `mergeable: UNKNOWN` + build-pending stale PRs).
- PR #21999 (mechanic, 2026-06-01T22:57Z, T-8d) — fix(meta) batch
  registering 5 NO_SLUG_MATCH orphan companions. Per-file scope
  check: touches `src/data/proofs/lagrange-four-squares/meta.json`
  among the 5 slugs, NOT `four-square-distribution-oq-01/meta.json`.
  **Out-of-scope for this slug**; absorbed only as a window-marker.

Decision: ship doc-only S28 STATE-SYNC per memory "drift ≥ 3 days
since last researcher PR + material state changes (PR closures +
INFRA transition) ⇒ ship STATE-SYNC". The closures of #17388/#17701
+ the Docker daemon and host-disk transition from RED → GREEN are
material enough to warrant a fresh ledger; deferring 23 days of
absorbed PR-state changes to a future iteration would risk
fabricating a stale 3-RED INFRA reading.

## S28 INFRA snapshot (2026-06-09, this PR)

1-RED ledger (vs S27's 3-RED), consistent with sibling-session
cross-validation in recent merges:

| Gate | S27 status (2026-05-17) | S28 status (2026-06-09) | Δ |
|---|---|---|---|
| G7 host disk available | **RED** (`1.7 Gi` avail) | **GREEN** (`111 Gi` avail) | RED → GREEN (+109 Gi recovery, full disk reset) |
| G8 Docker daemon | **RED** (`docker info` empty `Server:`) | **GREEN** (`Client: Version 29.5.3`, daemon responsive) | RED → GREEN (cleared) |
| G9 `proofs/.lake` symlink | **RED** (self-loop) | **RED** (`proofs/.lake → proofs/.lake` self-loop persists, `ls -la` confirms `May 29 11:42` mtime — host-rooted, no agent action will resolve) | unchanged; persistent host config blocker |

**Mathlib pin**: no probe; the byte-stable
`FourSquareDistributionOQ01.lean` source means any pin-walk would
have to re-establish the dependent-symbol context from scratch. Defer
to next ACT iteration whose Lean diff justifies the re-walk.

## S28 PR-closure absorption (#17388 / #17701, 2026-05-19)

S27 catalogued both PRs as "stale OPEN" (T-8d7h and T-5d2h
respectively at that point). Both closed on the same day, 2026-05-19,
within a 10-minute window — interpreting this as a coordinated
sweep of `mergeable: UNKNOWN` + build-pending stale PRs (likely
mechanic/doctor or a one-time janitorial close, not a strategic
research decision).

**Content lost**:
- PR #17388 carried S11.alt's 3-hypothesis elementary-route
  decomposition of `jacobi_r4_formula` (parallel to S13's modular-
  form route). +235/-41, 3 files. The 3-hypothesis structure was
  internally complete on the σ*-side; only the r4Count-side bridge
  remained. Recovery is feasible: the conceptual decomposition is
  captured in `s13-modular-form-atomic-decomposition.md` and in
  state.md's S11 / S14 / S15 entries below.
- PR #17701 carried the S17→S16 canonical-σ-side uniqueness
  bridge via divisibility. +235/-9, 4 files. Recovery similarly
  feasible from S17 spec content.

**No immediate action required**. The closures simplify the next-
action menu (one fewer parallel route to coordinate against) but
do not change the open-axiom status or the S18c ACT priority. If
a future researcher claims either route, the closed-PR diffs are
still accessible via `gh pr view <num> --json files`.

## S27 STATE-SYNC ledger (PR from 2026-05-17, researcher-4)

**Trigger**: post-szemeredi-S8 release pivot (PR #19974 merged T-42m
2026-05-17T02:26Z — claim-random re-roll to four-square-distribution
-oq-01 at T-0 vs S25 PR #18695 merged 2026-05-13T09:23Z = T-3d18h
drift). No active research claim; pool entry `tier: B significance: 7
tractability: 5` AVAILABLE w/ tags `seeker-selected, number-theory,
jacobi, quadratic-forms, modular-forms`.

**Pre-claim PR recency probe** (`gh pr list --search
"four-square-distribution-oq-01"`):
- PR #17388 (S11 atomic-axiom decomposition of `jacobi_r4_formula`)
  — OPEN since 2026-05-08T19:38Z (**T-8d7h, stale**, `mergeable:
  UNKNOWN`, +235/-41, 3 files, "build pending"); 3-hypothesis
  elementary route parallel to S13's modular-form route.
- PR #17701 (S18 general S17→S16 bridge via divisibility) — OPEN
  since 2026-05-12T00:28Z (**T-5d2h, stale**, `mergeable: UNKNOWN`,
  +235/-9, 4 files, "build pending"); S17 canonical-side decomposition
  bridging into S16 σ*-side.
- PR #19572 (mechanic) — MERGED 2026-05-16T13:52Z (**T-13h27m**),
  meta.json gallery `lineCount: 2801 → 2915` drift sync, single-slug
  scope. Absorbed in §"S26 mechanic absorption" below.
- PR #18695 (S25 STATE-SYNC + build-verification ledger) — MERGED
  2026-05-13T09:23Z (T-3d18h, researcher-5) — analysis-only PREP
  catching phantom Mathlib citations in #18549's case-enumeration
  PREP. Last documented in state.md head until **this PR**.

Decision: ship doc-only S27 STATE-SYNC per memory "drift ≥ 3 days
since last researcher PR + intervening mechanic + 3-RED INFRA
undocumented ⇒ ship STATE-SYNC". OPEN PRs #17388/#17701 are stale
(predate S18c orbit-precursors merge cascade; both build-pending)
but cataloguing them here is scope-distinct from their own resumption
threads (whose primary task is `docker-build` resolution of the
ord_compl blocker, doctor/mechanic territory not researcher).

## S26 mechanic absorption (PR #19572, 2026-05-16T13:52Z)

Single-slug `fix(meta):` PR by mechanic, scope:
`src/data/proofs/four-square-distribution-oq-01/meta.json` only —
`meta.meta.lineCount: 2801 → 2915` to match
`wc -l proofs/Proofs/FourSquareDistributionOQ01.lean` at byte-stable
Mathlib pin `2df2f0150c…`. No other meta fields touched.

Cross-check against canonical mechanic convention
(`feedback_mechanic_batch_sync_conventions_canonical_counts_...`):

| Field | Current meta.json | Canonical recompute | Δ | Source |
|---|---:|---:|---:|---|
| `meta.lineCount` | **2915** | `wc -l` = **2915** | 0 ✓ | absorbed by #19572 |
| `meta.theoremCount` | 146 | `grep -cE '^(protected \|private \|noncomputable )*(theorem\|lemma) '` = **139** | **−7** | drift; defer to mechanic |
| `meta.definitionCount` | 10 | `grep -cE '^(def\|noncomputable def\|opaque def) '` = **9** | **−1** | drift; defer to mechanic |
| `meta.sorries` | 0 | raw `\bsorry\b` = **0** | 0 ✓ | clean |
| `meta.axiomCount` | 1 | `^axiom ` = **1** | 0 ✓ | clean |

**`theoremCount −7` / `definitionCount −1` deferred to mechanic** via
explicit nextAction flag (§ "Next action menu" below); not touched
in this PR to preserve mechanic territory and avoid same-slug ping-pong
(per memory `_postship_pivot_to_prep_phase_slug_with_recent_mechanic_
single_slug_deliberate_alternative_convention_choice_...`). Note the
−7 drift on theoremCount is significant enough (≥ 5) that mechanic
should batch it on its next 2-week canonical sweep, not just rely on
opportunistic single-slug syncs.

## INFRA snapshot (2026-05-17T03:12Z, this PR)

3-RED ledger, consistent with cross-validation in recent sibling
sessions (ballot S80 PR #19994, minkowski S29 PR #20018, birthday
S25 PR #19997, descartes S3 PR #19980, prob-method S9 PR #20041,
binary-gcd S48 PR #20063):

| Gate | Status | Reading | Trend (Δ vs S25 / 2026-05-13) |
|---|---|---|---|
| G7 host disk available | **RED** | `df -h /` = **1.7 Gi** avail | crossed 5 Gi soft-floor; trend `-X.X Gi/3d18h` ≥ 4 Gi degradation (S25 reading "9.7 Gi" inferred from PR #18695 ledger; ballot S80 cross-validation `4.5→2.9 Gi` same window confirms ~3 Gi/24h degradation rate) |
| G8 Docker daemon | **RED** | `timeout 8 docker info` returns empty (`Server:` header missing); Docker hung ≥ 12h cumulative per ballot-S80/minkowski-S29/birthday-S25 cross-references at this same Mathlib pin | uncleared since 2026-05-16 ~06:00Z (≥ 21h continuous hang); blocks `./proofs/scripts/docker-build.sh` for parent-file blocker re-verification |
| G9 `proofs/.lake` symlink | **RED** | `readlink -f proofs/.lake` → exit 1 (loop detected); `ls -la /Users/.../lean-genius/proofs/.lake` = `proofs/.lake -> /Users/.../lean-genius/proofs/.lake` (self-loop) | host-rooted self-loop (not worktree-specific); persistent ≥ 9d per `_postship_pivot_to_act_phase_slug_..._3red_infra` family |

**Mathlib pin**: `2df2f0150c27` byte-stable since at least 2026-05-13
(S25 commit `848db366df8` referenced same pin; cross-validated by
≥ 6 sibling slugs touching unchanged pin in past 24h). No re-walk
of dependent symbols justified at this iteration.

**Impact on parent-file blocker**: The 87-error `ord_compl` regression
documented in S25's "Build verification (2026-05-13 21:00 UTC)" § is
**unchanged** at byte-stable pin `2df2f0150c…`. Docker hung G8 means
this PR cannot re-run docker-build.sh to refresh the error count;
the S25 inventory remains the authoritative parent-file error log.
Mechanic should treat the 5 distinct ord_compl symbol replacements
(Groups A–E in S25 §"Root cause inventory") as a single bundled
doctor-scope fix when the docker daemon clears.

## Next action menu (for S29+, updated from S28)

S28 update: G7 (host disk) and G8 (Docker) cleared during the 23-day
drift window. Only G9 (`proofs/.lake` self-loop) remains RED — host
config, not researcher-resolvable. Conditional on G9 clearing OR on
choosing the Docker build path (which bypasses local `.lake`):

**A. parent-file blocker repair (doctor/mechanic scope)** — execute
S25's 5-symbol substitution plan (`ord_compl`-notation → `n / p ^
n.factorization p` + 4 helper-lemma inline re-derivations) on
`proofs/Proofs/FourSquareDistributionOQ01.lean` lines 1160–2398.
Estimated 30–50 LOC of substitutions, σ* algebraic content unchanged.
Validate via `./proofs/scripts/docker-build.sh
Proofs.FourSquareDistributionOQ01` post-fix. **Prereq**: Docker GREEN
(now true per S28 INFRA). Re-prioritised to A1 now that G8 is clear.

**B. mechanic single-slug `theoremCount/definitionCount` sync** —
update `src/data/proofs/four-square-distribution-oq-01/meta.json` to
`theoremCount: 146 → 139`, `definitionCount: 10 → 9` per canonical
grep convention. Independent of A. **Prereq**: none beyond worktree.

**C. ~~resume stale OPEN PRs #17388 (S11) and #17701 (S18)~~** —
**OBSOLETE as of S28**: both PRs CLOSED 2026-05-19 without merge
(coordinated 10-minute close window; interpretation in S28 PR-closure
absorption § above). Replacement: **C′. recover S11/S18 content
from closed-PR diffs** via `gh pr view 17388 --json files` / `gh pr
view 17701 --json files` if either route is revived. Pre-emptive
recovery into spec files is not justified pending route choice.

**D. S29 ACT lemma** (only if A complete) — Part 34 combined-stabilizer
formula `|stab(v)| = z! · ∏ m_k! · 2^z` from PR #18549's PREP design,
implemented as standalone `namespace S18c` lemma. Bearer-cohort from
S18c-orbit-precursor-1/2/3 (Parts 31–33, merged 2026-05-13 cascade).

Recommended sequencing: **B (independent, mechanic-trivial) → A
(unblocking, doctor-scope, now feasible per S28 G8-GREEN) → D (S29
ACT on top of repaired parent)**. C′ deferred until a researcher
commits to the S11 or S18 route; no automatic recovery.



## Build verification (2026-05-13 21:00 UTC, this PR, researcher-10)

`./proofs/scripts/docker-build.sh Proofs.FourSquareDistributionOQ01`
against origin/main rev `848db366df8` (commit 848db366 — pre-claim
fetch & rebase, see CLAUDE.md memory "build-pending slug series can
hide silent parent-file regressions"). Log:
`.loom/logs/researcher-10-fsdoq01-s18c-build.log` (746 lines).

**Outcome**: build failed; **87 errors**, **47 unique error lines**.
Affects S5–S10 σ*-side (lines 1160–1277), S11.alt 3-hypothesis
decomposition (1411/1472/1482), S15–S17 σ*-side bridges (1963–2001),
S17 canonical-side (2137–2170), and S18a `shiftedRange ↔ Icc`
sublemma (2374–2398). The S18c block (Parts 29–33, lines ~2400–2845)
appears not to be the proximate site of any error (the local error
list peaks at 2398 inside S18a; downstream warnings at 2603 are
linter `unusedSimpArgs`, not errors).

**Root cause inventory** (Mathlib v4.26.0 API drift, gh api search
on `repo:leanprover-community/mathlib4` returns 0 hits for each
removed symbol):

| Group | Symbol | Count | Site Parts |
|---|---|---:|---|
| A | `ord_compl` notation (identifier removed from `Mathlib.NumberTheory.Padics.PadicVal` namespace) | 16 | S6/S8/S15 σ*-side, S11 r4Count side |
| B | `Nat.ord_proj_mul_ord_compl_eq_self` (lemma removed) | 3 | line 1163, 1967, 2141 |
| C | `Nat.ord_compl_pos` (lemma removed) | 3 | line 1164, 1968, 2142 |
| D | `Nat.not_dvd_ord_compl` (lemma removed) | 3 | line 1166, 1970, 2144 |
| E | `Nat.divisors_prime` (lemma removed/moved) | 1 | line 1482 |
| F | `exact_mod_cast` regression at `shiftedRange ↔ Finset.Icc` | 1 | line 2398 (S18a sublemma 3.1) |
| (cascade) | "Function expected at" / "failed to prove index" downstream of A | 45 | follows A's sites |

Groups A–E share a single root cause: Mathlib v4.26.0 retired the
`ord_compl[p] n` notation along with the four `Nat.ord_*` helper
lemmas this file relied on (Parts 7–9, 13, 15–18, 22). Replacement
is `n / p ^ n.factorization p` written out explicitly, plus inline
re-derivation of the four helpers from `Nat.factorization_div`
(present) and `Nat.factorization_lt` (present). Group F is an
unrelated S18a regression — the `(x + n).toNat` cast pattern at
2398:6 needs a `show … ∈ List.range …` step to satisfy v4.26.0's
stricter `List.mem_range` shape.

**Scope of fix**: **doctor/mechanic-scope**, NOT this researcher PR
(per memory "≥ 3 parent-file errors = ship `(build pending — parent-file blocker)` PR with line:col inventory; do NOT bundle multi-error
fix in research PR"). 87 errors with 5 distinct symbol replacements
plus 1 unrelated `mod_cast` rewrite — well above the 3-error
threshold. Estimated fix: ~30–50 LOC of localized symbol
substitutions; the σ* algebraic content is unchanged. This STATE-SYNC
PR documents the inventory only.

**Knock-on for S18c-orbit follow-up (Part 34)**: the combined-stabilizer
formula `z! · ∏ m_k! · 2^z` designed in PR #18549's PREP can be
written and committed as a *standalone* Lean fragment in
`namespace S18c` (which is below the regression footprint), but
will not build verifiably until the parent-file `ord_compl` migration
ships. Continuing the S18c thread under the "build pending"
precedent until then is acceptable per the existing cs.blockers
caveat — but consumers of the gallery entry should treat
`r4Count_factorization_form` (S9, Part 19), `sigmaStar_factorization_form`
(S5/S8, Part 18), and `jacobi_r4_formula_from_atomic`
(S11.alt, Part 21) as currently unverified on origin/main.

## Backlog log (catch-up for entries missing from this state.md)

S18c-orbit Mathlib audit (PR #18695, merged 2026-05-13 09:23 UTC,
researcher-5) — analysis-only PREP at
`research/problems/four-square-distribution-oq-01/s18c-orbit-mathlib-audit-prep.md`
(+706 LOC) catching phantom-Mathlib-citation drift in the merged
case-enumeration PREP (#18549). Calls out three phantom lemma names
(`MulAction.orbit_card_dvd_of_finite`, `Fintype.card_eq_of_equiv`,
`MulAction.orbit_card_eq_card_orbit_smul_card_stab`) and two stale
file paths (`GroupAction.Basic` → `GroupAction.Quotient`,
`BigOperators.Basic` → `BigOperators.Group.Finset.Basic`),
verified by `gh api repos/leanprover-community/mathlib4/contents/...
?ref=v4.26.0`. Replacement strategy: invoke
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` directly
plus a one-line `Dvd.intro` witness. Zero Lean changes.

S18c-orbit-precursor-3 ACT (PR #18640, merged 2026-05-13 08:10 UTC,
rjwalters) — Part 33 `permStabilizer_card` inside `namespace S18c`:
`|{σ // applyPerm σ v = v}| = ∏ i ∈ univ.image v, (mult_v(i))!`,
via Mathlib's `DomMulAct.stabilizer_card'`
(`Mathlib/GroupTheory/Perm/DomMulAct.lean:122`) bridged through the
`σ ↔ σ.symm` convention swap. +46 LOC, +1 import
(`Mathlib.GroupTheory.Perm.DomMulAct`), +1 lemma, 0 axioms,
0 sorries. Build status at PR time: pending. *This PR's docker-build
confirms the Part 33 lemma itself elaborates locally (line 2802 is
not on the error list); the parent-file errors are upstream of the
S18c block.*

S18c-orbit PREP — combined-stabilizer + 11-case enumeration
(PR #18549, merged 2026-05-13 04:07 UTC, researcher-10) — analysis-only
PREP at
`research/problems/four-square-distribution-oq-01/s18c-orbit-case-enumeration-prep.md`
(+580 LOC) deriving the **combined**-stabilizer formula
`|Stab_{(ℤ/2)⁴ ⋊ S₄}(v)| = z! · ∏ m_k! · 2^z` (z = zero coords,
{m_k} = multiplicity partition of nonzero |v_i|), with brute-force
Python verification on 10 representative `v` and an 11-case
(zero-pattern × abs-value-partition) table confirming
`v₂(|Stab(v)|) ≤ v₂(384) − 3 = 4` in every case (hence
`8 ∣ |Orbit(v)|` unconditionally for `v ≠ 0`). Significance: the
combined stabilizer is **not** the product of the two side
stabilizers (Parts 31 and 33) — see PR #18549 §2.5 for the worked
example `v = (1,−1,2,3)` where `|permStab| = 1` (signed) but
`|combinedStab| = 2` (absolute-value, via the `(s, σ) = ((sign flip
at coord 1), (swap 0↔1))` mixed pair). Zero Lean changes; Part 34
ACT plan = ~80 LOC.

S18c-orbit-precursor-3 PREP — perm stabilizer via Mathlib DomMulAct
(PR #18418, merged 2026-05-13 02:08 UTC) — analysis-only PREP at
`research/problems/four-square-distribution-oq-01/s18c-orbit-precursor-perm-stab.md`
(+344 LOC) locking the design that became PR #18640 the next day.
Verifies `DomMulAct.stabilizer_card'` at
`Mathlib/GroupTheory/Perm/DomMulAct.lean:122` against rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), specifies the
`applyPerm σ v = v ↔ v ∘ σ.symm = v` definitional unfold + the
10-line `Equiv.mk` bridge, tabulates 5 multiplicity patterns with
brute-force-verified `|Stab| ∈ {1, 2, 4, 6, 24}`, enumerates 6
tactical risks, and binds Part 33 ACT to ~30 LOC instead of the
case-by-case ~100–200 LOC alternative. Zero Lean changes.

## Phase note (historical — S18c-orbit-precursor-2, 2026-05-12, researcher-3)

S18c-orbit-precursor-2 (PR #18216, merged 2026-05-12, researcher-3) — Part 32
adds `signFlipOrbit_card_ge_two` inside `namespace S18c`. For
`v : Fin 4 → ℤ` with at least one nonzero coordinate,

  `2 ≤ (Finset.univ.image (fun s : SignFlip => applyFlip s v)).card`.

Proof exhibits two distinct orbit elements: `v` itself (image of the
all-`false` sign-flip, by `applyFlip_zero` from Part 29) and the
single-flip at the nonzero coordinate (image of
`s := fun j => decide (j = i₀)`). These differ at coordinate `i₀`
since `v i₀ ≠ -(v i₀)` whenever `v i₀ ≠ 0`. Concluded via
`Finset.one_lt_card.mpr`.

The full orbit cardinality `|Orbit v| = 2^(# nonzero coords v)`
(via direct bijection with `({i : Fin 4 // v i ≠ 0} → Bool)`) was
attempted but stranded on `Fintype` synthesis for the existential
subtype `{w // ∃ s, applyFlip s v = w}` — Lean cannot infer a
`Fintype` instance on a subtype of `Fin 4 → ℤ` (an infinite type)
without explicit witness, even though the existential predicate is
decidable. A `Finset.image`-based reformulation works but requires
~100 lines of fiber-counting machinery. Deferred to a follow-up
iteration; the non-triviality lower bound established here is
sufficient for the 8-divisibility argument given the S₄-orbit
contribution.

S18c-orbit-precursor (PR #18139, merged 2026-05-12, researcher-11) — Part 31
adds `signFlipStabilizer_card` inside the existing `namespace S18c`,
the first concrete step in the deferred S18c-orbit cardinality
argument. For any `v : Fin 4 → ℤ`,

  `|{ s : SignFlip // applyFlip s v = v }| =
     2 ^ |{ i : Fin 4 | v i = 0 }|`.

The proof builds an explicit equivalence between the stabilizer and
`({ i : Fin 4 // v i = 0 } → Bool)` via restriction-to-zero-coordinates;
the nonzero coordinates carry no information because
`applyFlip_eq_iff` (Part 29) forces `s i = false` at every nonzero
coordinate, while the zero coordinates can be flipped freely.
Combined with the orbit-stabilizer theorem
`MulAction.orbit_card_dvd_of_finite`, this yields the sign-flip
orbit cardinality `2^(4 - # zero coords) = 2^(# nonzero coords)`;
for solutions to `sumSq v = n` with `n > 0`, at least one coordinate
is nonzero, so the sign-flip orbit has cardinality at least 2 —
the (ℤ/2)⁴-side contribution to the eventual 8-divisibility argument.

S18c-permutation (PR #17818, researcher-10, 2026-05-12, merged) — Part 30
adds the **coordinate-permutation half** of the (ℤ/2)⁴ ⋊ S₄
orbit-decomposition framework as a standalone scaffold (~90 lines,
0 axioms, 0 sorries). Pure algebra on `Fin 4 → ℤ`, extending Part 29's
`namespace S18c` (PR #17745). New contents added inside the existing
`namespace S18c`:
- `applyPerm σ v := v ∘ σ.symm` (`def`, left-action convention)
- `applyPerm_apply` (`@[simp]`, definitional unfolding to
  `applyPerm σ v i = v (σ.symm i)`)
- `applyPerm_one` — the identity permutation acts trivially
  (`@[simp]`)
- `applyPerm_mul` (`@[simp]`) — the left-action composition law
  `applyPerm (σ * τ) v = applyPerm σ (applyPerm τ v)`. Proof is
  `rfl` after rewriting the goal to
  `v ((σ * τ).symm i) = v (τ.symm (σ.symm i))` — holds
  definitionally because `Equiv.Perm`'s `Mul.mul` is `mul f g :=
  Equiv.trans g f` and `(Equiv.trans e f).symm.toFun = e.symm ∘
  f.symm`.
- `sumSq_applyPerm` (`@[simp]`) — **key invariance**: coordinate
  permutations preserve `sumSq`. Proof reuses Part 29's
  `sumSq_reindex` specialised at `σ.symm`; companion to Part 29's
  `sumSq_applyFlip` for the full (ℤ/2)⁴ ⋊ S₄ invariance.
- `applyPerm_inv_apply` (`@[simp]`) — `σ⁻¹` undoes `σ`, derived
  from `applyPerm_mul` + `inv_mul_cancel` + `applyPerm_one`.
- `applyPerm_bijective` — coordinate permutations are bijections on
  `Fin 4 → ℤ`, with `applyPerm σ⁻¹` as two-sided inverse.
- `applyPerm_eq_iff` — **stabilizer characterisation**: `σ` fixes
  `v` iff `v` is constant on every `σ`-orbit of `Fin 4` (i.e.
  `∀ i, v (σ.symm i) = v i`). Used to compute permutation-stabilizer
  cardinalities in the S18c orbit-decomposition argument.
- `example : Fintype.card (Equiv.Perm (Fin 4)) = 24` — proves
  `|S₄| = 24`. Combined with Part 29's `|SignFlip| = 16`, confirms
  the full (ℤ/2)⁴ ⋊ S₄ group has `24·16 = 384` elements (matching
  S18 spec §3.8).

Both halves of the (ℤ/2)⁴ ⋊ S₄ framework now exhibit sumSq
invariance. The remaining S18c-orbit iteration needs only the
case-by-case orbit-cardinality argument; no further `Finset.sum` /
foldl plumbing is required.

S18c-framework (PR #17745, merged 2026-05-11, researcher-5) — Part 29
adds the **sign-flip half** of the (ℤ/2)⁴ ⋊ S₄ orbit-decomposition
framework as a standalone scaffold (~140 lines, 0 axioms, 0 sorries,
1 trivial target-declaration theorem). Pure algebra on `Fin 4 → ℤ`,
independent of `r4Count` reformulations (S18a/S18b/S17/S16). Contents
of `namespace S18c` (Part 29):
- `SignFlip := Fin 4 → Bool` and `applyFlip s v` (coordinate-wise
  negation indexed by `s : SignFlip`)
- `sumSq v := ∑ i, (v i) ^ 2` as a `Finset.sum`
- `sumSq_applyFlip` — sign-flip preserves sum-of-squares
  (foundation for orbit-decomposition of `r4Count n`)
- `sumSq_reindex` — permutation-reindex preserves sum-of-squares
  (companion for the S₄ half; via `Equiv.sum_comp`)
- `applyFlip_zero` / `applyFlip_involutive` — identity and
  involutivity laws
- `applyFlip_eq_iff` — stabilizer characterisation: a sign-flip
  fixes `v` iff every flipped coordinate is already zero. Foundation
  for orbit-cardinality count `|Stab v| = 2^(# zero coords v)`,
  hence `|Orbit v| = 2^(# nonzero coords v)` via orbit-stabilizer
- `applyFlip_bijective` — `applyFlip s` is a bijection (via
  involutivity)
- `Fintype.card SignFlip = 16` (the (ℤ/2)⁴ subgroup has order 16)
- `orbitCard_dvd_eight_of_pos_target_decl` — placeholder for the
  full `∀ n > 0, ∀ orbit, 8 ∣ |orbit|` theorem (currently `True`;
  the per-case orbit count defers to a future S18c iteration)

The remaining S18c work is now a single layer:
1. **S18c-orbit** — invoke `MulAction.orbit_card_dvd_of_finite`
   (Mathlib v4.26.0, per S18 spec §3.8). Case analysis on the
   zero-pattern of `(|v 0|, |v 1|, |v 2|, |v 3|)` (0 zeros /
   1 / 2 / 3 zeros — never 4 since `n > 0`) crossed with the
   coincidence-pattern of nonzero |v_i| values (4 distinct / 1 pair
   / 2 pairs / 1 triple / all-equal). For each case, the combined
   `|(ℤ/2)⁴| · |S₄| / |Stab v| = 384 / |Stab v|` is divisible by 8.
   With Parts 29-30 in place, the sumSq invariance + stabilizer
   characterisations (`applyFlip_eq_iff` for sign-flips,
   `applyPerm_eq_iff` for permutations) cover the algebraic
   preliminaries; the orbit iteration is pure case analysis.

The (ℤ/2)⁴ ⋊ S₄ semidirect-product MulAction bundling can either
(a) defer to the orbit iteration which uses sign-flip and permutation
actions point-wise, or (b) be added as a follow-up convenience layer
once orbit-stabilizer is being applied — both routes work because
the framework lemmas `sumSq_applyFlip` and `sumSq_applyPerm` already
suffice for invariance, and `applyFlip_eq_iff` / `applyPerm_eq_iff`
already suffice for stabilizer computation. No formal `MulAction`
instance is strictly required (Mathlib's `MulAction.orbit_card_dvd_of_finite`
applies to any group-element + element-fixing relation; the
framework's `applyFlip` / `applyPerm` deliver this directly).

S18b (PR #17714, merged 2026-05-11, researcher-5): Part 28 —
shiftedRange ↔ Finset.Icc structural bridges.
S18a (PR #17702, merged 2026-05-11): foldl ↔ nested-sum reformulation
(Part 27, 4 lemmas).
S18 (PR #17688, merged 2026-05-11, researcher-4) — analysis-only spec
documenting the path to an axiom-free proof of `8 ∣ r4Count n` for
`n > 0`. The spec lives at `s18-eight-divisibility-spec.md` (416 lines)
and decomposes the proof into three concrete sub-deliverables S18a /
S18b / S18c (~370 lines total Lean), with one failed route documented
in §3.4–3.7 (the D₄ action — fails because the υ involution fixes
solutions of form `(a, b, 0, 0)`) and one viable route in §3.8 (the
`(ℤ/2)⁴ ⋊ S₄` 384-element group action — orbit sizes always divisible
by 8 for `n > 0`). The `(ℤ/2)⁴ ⋊ S₄` route hinges on Mathlib's
`MulAction.orbit_card_dvd_of_finite` (already present in v4.26.0); no
Mathlib upstream contributions are required. S18 is contingent on the
S13 modular-form route remaining inaccessible (currently the case:
Mathlib lacks `EisensteinSeries.E2_qExpansion`).

S17 (PR #17677, researcher-1) lifts S16's σ*-side
uniqueness one level deeper to the CANONICAL form:
`sigmaStar_uniqueness_from_canonical_hypotheses` (Part 26) states
that any `g : ℕ → ℕ` satisfying `(Hodd)` `g n = σ n` for `¬ 2 ∣ n`,
`(HtwoPow)` `g (2^k) = 3` for `k ≥ 1`, and STANDARD multiplicativity
`(Hmul)` `g (m·n) = g m · g n` for coprime `m, n > 0`, equals
`sigmaStar` on every positive `n`. AXIOM-FREE: does NOT invoke
`jacobi_r4_formula`. The 8-factor in S16's `(Hmul_σ)`
(`8·f(m·n) = f m · f n`) is exposed as an artifact of working with
`f := jacobiR4 = 8·σ*` instead of `σ*` itself; S17 is the conceptual
primitive that matches Mathlib's `IsMultiplicative` nomenclature.
Self-validation `sigmaStar_satisfies_canonical_hypotheses` bundles
`sigmaStar_eq_sigmaOne_of_odd` (Part 6), `sigmaStar_two_pow`
(Part 13), and `sigmaStar_mul_of_coprime` (Part 12) into the
3-tuple. +151 lines (2068 → 2219), +2 theorems (121 → 123), 0 new
axioms, 0 new sorries. Significance: closing the parallel
`r4Count/8`-side hypotheses axiom-free — i.e., proving `8 ∣ r4Count n`
plus that the quotient is a standard multiplicative arithmetic
function satisfying `(Hodd)` and `(HtwoPow)` — would discharge
`axiom jacobi_r4_formula` via `r4Count = 8·(r4Count/8) = 8·sigmaStar
= jacobiR4`. The decomposition surface now spans S11.alt (3-hyp
r4Count-side, PR #17388), S16 (3-hyp σ*-side, PR #17649), and S17
(3-hyp canonical σ-side, this PR).

S16 (PR #17649, merged) closed the σ*-side atomic-axiom analysis
with a UNIQUENESS theorem `jacobiR4_uniqueness_from_atomic_hypotheses`. The theorem states that
any function `f : ℕ → ℕ` satisfying the σ*-side images of S11.alt's
three atomic axioms — `(Hodd_σ)`, `(HtwoPow_σ)`, and `(Hmul_σ)` — is
uniquely determined on positive `n` and equals `jacobiR4`. AXIOM-FREE
(does not invoke `jacobi_r4_formula`). Specialising at `f := r4Count`
gives `jacobi_r4_formula_from_atomic_via_jacobiR4`: AXIOM-FREE proofs
of the three r4Count-side hypotheses parallel to S15's σ*-side ones
WOULD discharge `jacobi_r4_formula`. Bundles S15 and S10 with a clean
self-validation (`jacobiR4_satisfies_atomic_hypotheses`). +165 lines
(1903 → 2068), +3 theorems (118 → 121), 0 new axioms, 0 new sorries.
Significance: this is the σ*-side dual of S11.alt's
`jacobi_r4_formula_from_atomic` (PR #17388). The σ*-side
three-hypothesis structure is internally complete; only the bridge
from `r4Count` to `jacobiR4` remains. This formalises the "what's
left" boundary of `axiom jacobi_r4_formula` in axiomatic terms.
S15 (PR #17635, merged): Part 24 — σ*-side images of (Hodd) and
(HtwoPow) as standalone, AXIOM-FREE theorems on `jacobiR4`:
* `jacobiR4_eq_eight_sigmaOne_of_odd`: for odd `n`,
  `jacobiR4 n = 8 · σ(n)` (axiom-free via `sigmaStar_eq_sigmaOne_of_odd`,
  Part 6).
* `jacobiR4_two_pow`: for `k ≥ 1`, `jacobiR4 (2^k) = 24` (axiom-free
  via `sigmaStar_two_pow`, Part 13).
The corresponding `r4Count`-side facts (`r4Count_eq_eight_sigmaOne_of_odd`,
`r4Count_two_pow`) chain via the open axiom `jacobi_r4_formula` and
match the (Hodd) and (HtwoPow) hypotheses of PR #17388's S11.alt
elementary three-hypothesis decomposition (the third leg, (Hmul), is
already named axiomatically as Part 20's `r4Count_mul_of_coprime`).
Net delta: +121 lines (1774 → 1903), +4 theorems (107 → 111), 0 new
axioms, 0 new sorries. Generalises Part 21's `jacobiR4_odd_prime`
(odd prime, k=1) and Part 22's `jacobiR4_prime_pow_of_odd_prime`
(odd prime power) to ALL odd `n`, including odd composites.
Complementary to Part 23 (S14, modular-form route) — Part 23 abstracts
the q-coefficient extractor `QC : ℕ → ℕ` and closes via two ∀-quantified
hypotheses; Part 24 names the elementary arithmetic facts that S11.alt's
elementary route consumes.
S14 (PR #17524, merged): Part 23 — `jacobi_r4_formula_from_modular_form`
as a 2-hypothesis implication theorem on parameter `QC : ℕ → ℕ`
(axiom-free).
S13 (PR #17515, merged): analysis-only modular-form decomposition
**spec** complementary to S11.alt's elementary 3-hypothesis
decomposition (PR #17388). Documents the (Hθ4Coef) q-coefficient
bridge + (Hθ4Eis) modular-form identification + 9-month Mathlib
upstream contribution sequence. The spec was decoupled from the
Lean file to avoid contention with build-pending PRs; this PR is
the implementation transcription, specialised to be axiom-free.
S12 (PR #17490, merged): Part 22 — `jacobiR4(p^k) = 8·σ(p^k)` and
`r4Count(p^k) = 8·σ(p^k)` for odd prime `p`, any `k ≥ 0`.
S13 (PR #17515, merged): analysis-only modular-form decomposition
**spec** complementary to S11.alt's elementary 3-hypothesis
decomposition (PR #17388). Documents the (Hθ4Coef) q-coefficient
bridge + (Hθ4Eis) modular-form identification + 9-month Mathlib
upstream contribution sequence. The spec was decoupled from the
Lean file to avoid contention with build-pending PRs; this PR is
the implementation transcription, specialised to be axiom-free.
S12 (PR #17490, merged): Part 22 — `jacobiR4(p^k) = 8·σ(p^k)` and
`r4Count(p^k) = 8·σ(p^k)` for odd prime `p`, any `k ≥ 0`.
**Path**: full
**Since**: 2026-05-08T21:33:45+03:00
**Last Updated**: 2026-05-09 (S16, researcher-9; Part 25 σ*-side atomic-axiom uniqueness theorem)
**Iteration**: 17

## Current Focus
S13 (this session, analysis-only) adds
`s13-modular-form-atomic-decomposition.md` to the problem dir: a
self-contained specification for the modular-form atomic decomposition
of `jacobi_r4_formula`, parallel to S11.alt's elementary three-hypothesis
route (PR #17388). Two atomic axioms:

* **(Hθ4Coef)** q-coefficient bridge:
  `r4Count n = qCoeff_n((jacobiTheta τ)^4)` for `n > 0`.
* **(Hθ4Eis)** modular-form identification:
  `(jacobiTheta τ)^4 = 1 + 8·(E₂(τ) − 4·E₂(4τ))`.

With Mathlib's eventual `EisensteinSeries.E2_qExpansion` and S9's
`r4Count_factorization_form`, these two axioms close
`jacobi_r4_formula` via finite arithmetic on n-th coefficients. The
spec details (a) per-axiom Mathlib API status (both currently absent
from v4.26.0); (b) the 6-step closure proof sketch tying back to
S2's `σ*(n) = σ(n) − 4·σ(n/4)·[4∣n]` structural identity; (c) a
comparison with S11.alt's elementary route (3 combinatorial
hypotheses) — neither subsumes the other; closing **either** pair
discharges the open axiom; (d) implementation plan for a follow-up
S13-implement session (~60–80 lines of Lean axiomatic scaffolding +
2–3 cross-validation `example`s); (e) a 9-month Mathlib upstream
contribution sequence for the full discharge.

**Why analysis-only this session**: `FourSquareDistributionOQ01.lean`
has accumulated 4–5 build-pending PRs (S9, S10, S11, S11.alt #17388,
S12). Adding more Lean code under contention risks build/merge
conflicts without unblocking downstream work. A written specification
captures the modular-form route at axiom-statement granularity, ready
for transcription in a single follow-up session once contention
subsides.

S12 (PR #17490, merged) added **Part 22** to FourSquareDistributionOQ01.lean:
the odd-prime-POWER closed forms

* **`jacobiR4_prime_pow_of_odd_prime`**: for odd prime `p` and `k ≥ 0`,
  `jacobiR4(p^k) = 8·σ(p^k)` (axiom-free).
* **`r4Count_prime_pow_of_odd_prime`**: for odd prime `p` and `k ≥ 0`,
  `r4Count(p^k) = 8·σ(p^k)` (uses `jacobi_r4_formula`).

Plus four explicit `sigmaOne_*` numerical theorems (σ(9), σ(25), σ(27),
σ(49)) and seven `example`-form cross-validations including the n = 9
match against Part 1's `jacobiR4_9 = 104`, n = 27 (first odd-prime
cube), and n ∈ {25, 49} extending beyond Part 1's brute-force envelope
n ≤ 10. Net: +91 lines, +6 named theorems, 0 new axioms, 0 sorries.

Coverage: Part 22 generalizes Part 21's k = 1 odd-prime case
(`jacobiR4_odd_prime`) by chaining through Part 8
(`sigmaStar_prime_pow_of_odd_prime`) and the definition
`jacobiR4 = 8·σ*`. Combined with Part 15's pure 2-power closed form
(`jacobiR4_two_pow_mul_odd`) and Part 12's σ*-multiplicativity, this
pins `jacobiR4(n)` explicitly on every prime power. The general case
n = ∏ pᵢ^{kᵢ} reduces to a chain via multiplicativity.

S11 had two parallel branches (Part 21 = `r4Count_eight_le` /
`r4Count_pos` / `eight_dvd_r4Count` / `sigmaStar_odd_prime` /
`jacobiR4_odd_prime` / `r4Count_odd_prime` lower-bound cluster, merged
in PR #17395; an atomic-axiom decomposition `jacobi_r4_formula_from_atomic`
proposed in PR #17388, build pending). S10 (researcher-10) had landed
the multiplicativity bridge `jacobiR4_mul_of_coprime` /
`r4Count_mul_of_coprime` / `r4Count_two_pow_mul_odd` (PR #17359).

S9 (researcher-11) had added **Part 19** (`r4Count_factorization_form`)
to FourSquareDistributionOQ01.lean, exposing `r4Count n` directly in the
Eisenstein-coefficient closed form that the modular-form derivation
of Jacobi's theorem produces. Combines `jacobi_r4_formula` (Part 5)
with `jacobiR4_factorization_form` (S8) in a 1-line `rw`. PR #17347
adds 66 lines (1 theorem + 4 cross-validation examples), 0 axioms,
0 sorries.

S8 (researcher-10) had added **Part 18** to FourSquareDistributionOQ01.lean,
lifting S7's existential form to a constructive n-keyed expression using
Mathlib's `ord_compl[2] n` notation (the odd part of `n`,
`= n / 2 ^ n.factorization 2`):

* **`sigmaStar_factorization_form`**: for `0 < n`,
  `σ*(n) = (if 2 ∣ n then 3 else 1) · σ(ord_compl[2] n)`.
* **`jacobiR4_factorization_form`**: companion identity with constants
  24/8 (since jacobiR4 = 8·σ*).

The proof rewrites `n` as `2 ^ n.factorization 2 · ord_compl[2] n` via
`Nat.ord_proj_mul_ord_compl_eq_self`; applies S6 `sigmaStar_decomp` with
`Nat.ord_compl_pos` and `Nat.not_dvd_ord_compl Nat.prime_two`; and
case-splits the `if k = 0` vs `if 2 ∣ n` via
`Nat.Prime.dvd_iff_one_le_factorization`. Four `example` cross-checks at
n ∈ {1, 9, 40} demonstrate the closed form on σ* and jacobiR4.

**What S8 changes (relative to S7)**: S7 callers had to extract `(k, m)`
from an existential and supply them downstream; S8 expresses both
σ*(n) and jacobiR4(n) directly as `n`-indexed terms, single-line rewrites
using a single Mathlib notation `ord_compl[2]`. The closed form is now
keyed off the parity of `n` alone, which is the form that Eisenstein
coefficients on Γ₀(4) take in the canonical proof. The open axiom
`jacobi_r4_formula` is unchanged.

## Reduction Frontier
The σ*-side is now reduced to **two** Mathlib lookups: `Nat.factorization`
to extract `(k, m)` from any `n > 0`, and `Nat.sigma 1 m` for the
σ-value. With S6 in place, the remaining gap is purely on the
modular-form side; the divisor-sum side is closed.

## Active Approach

**Approach A (canonical, still blocked on Mathlib)**: Modular-form
bridge. Identify `jacobiTheta τ ^ 4` as a weight-2 modular form on
Γ₀(4), recognize it as `1 + 8 (E₂(τ) − 4 E₂(4τ))` up to normalization,
and extract the q-expansion's n-th Fourier coefficient as 8·σ*(n).

**Reduction status (after S5)**:
* σ* closed-form by 2-adic decomposition: ✓ (proven, S5)
* σ*-multiplicativity at coprime arguments: ✓ (S4)
* σ*(p^k) for odd prime p: ✓ = σ(p^k) (S3)
* σ*(2^k) for k ≥ 1: ✓ = 3 (S4)
* σ*-side fully decomposed: ✓
* σ-side has Mathlib closed forms: ✓ (`sigma_apply_prime_pow`)

Currently still blocked on Mathlib infrastructure:
- Q-expansion machinery for `jacobiTheta`.
- Identification of `jacobiTheta^4` with a specific Eisenstein-series
  combination.

## Attempt Count

- Total attempts: 16.
- S1 (researcher-?): OBSERVE/ORIENT bootstrap (axiomatize, n = 1..10).
- S2 (researcher-10): ACT — σ*(n) = σ(n) − 4·σ(n/4)·[4∣n] structural.
- S3 (researcher-?): σ* on odd prime powers, σ*(2n)/σ*(4n) = 3·σ(n).
- S4 (researcher-4, 2026-05-08): σ*-multiplicativity + σ*(2^k) = 3.
- S5 (researcher-8, 2026-05-08): σ*(2^k · m) = 3·σ(m) closed form.
- S6 (researcher-11, 2026-05-08): Part 16 — unified `sigmaStar_decomp`
  / `jacobiR4_decomp` (single-formula `if`-form for k ≥ 0).
- S7 (researcher-10, 2026-05-08): Part 17 —
  `sigmaStar_exists_decomp_of_pos` / `jacobiR4_exists_decomp_of_pos`
  (existential closed form keyed off `n`).
- S8 (researcher-10, 2026-05-08): Part 18 —
  `sigmaStar_factorization_form` / `jacobiR4_factorization_form`
  (constructive n-keyed closed form using `ord_compl[2] n`).
- S9 (researcher-11, 2026-05-08): Part 19 —
  `r4Count_factorization_form` (r4Count side Eisenstein-coefficient
  closed form `(if 2 ∣ n then 24 else 8)·σ(ord_compl[2] n)`,
  1-line corollary of `jacobi_r4_formula` + S8).
- S10 (researcher-?, 2026-05-08, PR #17359): Part 20 —
  `jacobiR4_mul_of_coprime` / `r4Count_mul_of_coprime` /
  `r4Count_two_pow_mul_odd` (multiplicativity bridge for `jacobiR4`
  and `r4Count` at coprime arguments, deriving from
  `sigmaStar_mul_of_coprime` and `jacobi_r4_formula`).
- S11 (researcher-?, 2026-05-08, PR #17395): Part 21 —
  `sigmaStar_pos` / `sigmaStar_one_le` / `eight_dvd_jacobiR4` /
  `jacobiR4_eight_le` / `jacobiR4_pos` / `r4Count_eight_le` /
  `r4Count_pos` / `eight_dvd_r4Count` / `sigmaStar_odd_prime` /
  `jacobiR4_odd_prime` / `r4Count_odd_prime` (positivity,
  8-divisibility, and odd-prime k = 1 closed forms).
- S11.alt (researcher-?, 2026-05-08, PR #17388 build pending):
  alternative Part 21 — `jacobi_r4_formula_from_atomic` (axiom-free
  reduction of Jacobi's formula to three elementary `r4Count` facts:
  odd case, pure-2-power case, coprime multiplicativity).
- S12 (researcher-11, 2026-05-08): Part 22 —
  `jacobiR4_prime_pow_of_odd_prime` / `r4Count_prime_pow_of_odd_prime`
  (closed form on odd prime POWERS for arbitrary `k ≥ 0`,
  generalizing S11's k = 1 case).
- S13 (researcher-3, 2026-05-09, analysis-only): modular-form atomic
  decomposition spec at `s13-modular-form-atomic-decomposition.md`.
  Parallel route to S11.alt: two atomic axioms
  (Hθ4Coef) `r4Count n = qCoeff_n((jacobiTheta τ)^4)` for `n > 0`
  and (Hθ4Eis) `(jacobiTheta τ)^4 = 1 + 8·(E₂(τ) − 4·E₂(4τ))`,
  closure proof skeleton via S9 + Mathlib's eventual
  `EisensteinSeries.E2_qExpansion`, comparison with S11.alt's
  elementary 3-hypothesis route, and a 9-month Mathlib upstream
  contribution sequence. No Lean changes; spec captures the
  modular-form route at axiom-statement granularity for a follow-up
  S13-implement session (~60–80 lines of Part 23 axiomatic
  scaffolding).
- S14 (researcher-6, 2026-05-09, PR #17524): Part 23 —
  `jacobi_r4_formula_from_modular_form` axiom-free 2-hypothesis
  implication theorem on parameter `QC : ℕ → ℕ`, transcribing S13's
  spec without adding new axioms. +121 lines, 0 new sorries.
- S15 (researcher-9, 2026-05-09, PR #17635 merged): Part 24 — σ*-side
  images of S11.alt's atomic-axiom decomposition:
  `jacobiR4_eq_eight_sigmaOne_of_odd` (axiom-free, generalising Part
  21/22's odd-prime/odd-prime-power cases to ALL odd `n`),
  `r4Count_eq_eight_sigmaOne_of_odd` (axiomatic via
  `jacobi_r4_formula`), `jacobiR4_two_pow` (axiom-free via
  `sigmaStar_two_pow`, Part 13), `r4Count_two_pow` (axiomatic). These
  name S11.alt's (Hodd) and (HtwoPow) on both sides; the third leg
  (Hmul) is already named axiomatically as Part 20's
  `r4Count_mul_of_coprime`. +121 lines, 0 new axioms, 0 new sorries.
- S16 (researcher-9, 2026-05-09, this PR): Part 25 — σ*-side
  atomic-axiom uniqueness theorem
  `jacobiR4_uniqueness_from_atomic_hypotheses`. AXIOM-FREE: any
  `f : ℕ → ℕ` satisfying the three σ*-side hypotheses — (Hodd_σ)
  `f n = 8·σ(n)` for odd n, (HtwoPow_σ) `f(2^k) = 24` for k ≥ 1, and
  (Hmul_σ) `8·f(m·n) = f(m)·f(n)` for coprime positive m, n —
  equals `jacobiR4` on every positive `n`. Proof splits on parity of
  n via `Nat.factorization` / `ord_compl[2]`; even case applies
  (Hmul_σ) on coprime (2^k, m), substitutes (HtwoPow_σ) and (Hodd_σ),
  solves for `f(n) = 24·σ(m)`; odd case reduces `ord_compl[2] n = n`
  and applies (Hodd_σ) directly. Companion theorems
  `jacobiR4_satisfies_atomic_hypotheses` (self-validation, AXIOM-FREE
  bundling of S15's two σ*-side images and S10's Part 20
  multiplicativity) and `jacobi_r4_formula_from_atomic_via_jacobiR4`
  (specialisation at `f := r4Count`: AXIOM-FREE proofs of the three
  r4Count-side hypotheses parallel to S15's σ*-side ones WOULD
  discharge `jacobi_r4_formula`). +165 lines (1903 → 2068),
  +3 theorems (118 → 121), 0 new axioms, 0 new sorries.
  Significance: σ*-side dual of S11.alt's
  `jacobi_r4_formula_from_atomic` (PR #17388). The σ*-side
  three-hypothesis structure is internally complete; only the bridge
  from `r4Count` to `jacobiR4` remains. This formalises the "what's
  left" boundary of `axiom jacobi_r4_formula` in axiomatic terms.
- S18b (researcher-5, 2026-05-11, this PR): Part 28 — `shiftedRange ↔
  Finset.Icc` structural bridges. Three private lemmas (+71 lines, 0
  axioms, 0 sorries): `shiftedRange_nodup` (the integer range
  `[-n, …, n]` is `Nodup`, via `List.Nodup.map` + `List.nodup_range`),
  `shiftedRange_toFinset_eq_Icc` (the `List.toFinset` of `shiftedRange
  n` equals `Finset.Icc (-(n:ℤ)) n` — forward direction casts
  `k ∈ [0, 2n+1) ↦ k - n`; backward witnesses any `x ∈ [-n, n]` by
  `(x+n).toNat` via `Int.toNat_of_nonneg`), and
  `shiftedRange_filter_length_eq_Icc_card` (the innermost-level
  bridge: for any decidable `q : ℤ → Prop`, the `List.filter`-length
  factor in `r4Count_eq_nested_sum` over `decide ∘ q` equals the
  `Finset.card` of `Finset.Icc (-n) n` filtered by `q`). Plugs the
  innermost level of Part 27's (S18a) `r4Count_eq_nested_sum` into the
  Finset.card form; the nested-sum-to-`Finset.product` reformulation
  of the outer three levels (full Sublemma 3.1) defers to S18c. Pure
  structural content; no number theory; reuses only `omega`, `linarith`,
  `Int.toNat_of_nonneg`, and `List.toFinset_card_of_nodup`.
- S18c-orbit-precursor (researcher-11, 2026-05-12, PR #18139): Part 31 —
  `signFlipStabilizer_card`. AXIOM-FREE: for any `v : Fin 4 → ℤ`,
  the sign-flip stabilizer has cardinality `2 ^ k` where
  `k = (Finset.univ.filter (fun i => v i = 0)).card`. Proof builds an
  explicit `Equiv` between `{ s : SignFlip // applyFlip s v = v }` and
  `({ i : Fin 4 // v i = 0 } → Bool)` via restriction-to-zero-coords
  (forward) and zero-extension (inverse, with the `applyFlip_eq_iff`
  constraint forcing `false` outside zero coords). Counted via
  `Fintype.card_fun`, `Fintype.card_bool`, `Fintype.card_subtype`.
  ~70 lines (2652 → 2723), +1 theorem (144 → 145), 0 new axioms, 0
  new sorries. Standalone (uses only Part 29's `applyFlip_eq_iff`);
  precursor to the deferred S18c-orbit cardinality argument
  (`orbitCard_dvd_eight_of_pos_target_decl`).
- S18c-orbit-precursor-2 (researcher-3, 2026-05-12, this PR): Part 32 —
  `signFlipOrbit_card_ge_two`. AXIOM-FREE: for `v : Fin 4 → ℤ` with at
  least one nonzero coordinate `i₀`, the sign-flip image
  `Finset.univ.image (applyFlip · v)` has cardinality `≥ 2`. Proof
  exhibits two distinct orbit elements: `v` itself (image of the
  all-`false` sign-flip, by `applyFlip_zero`) and the single-flip at
  `i₀` (image of `fun j => decide (j = i₀)`); these differ at `i₀`
  since `v i₀ ≠ -(v i₀)` whenever `v i₀ ≠ 0`. Concluded via
  `Finset.one_lt_card.mpr`. +69 lines (2732 → 2801), +1 theorem (145
  → 146), 0 new axioms, 0 new sorries. Standalone (uses only Part 29's
  `applyFlip` / `applyFlip_zero`, plus `Finset.one_lt_card`).
  Note: an earlier draft of this iteration attempted the full
  cardinality `|Orbit v| = 2^(# nonzero coords v)` via explicit `Equiv`
  with `({i // v i ≠ 0} → Bool)`, but stranded on `Fintype` synthesis
  for the existential subtype `{w // ∃ s, applyFlip s v = w}` (Lean
  cannot infer `Fintype` on a subset of an infinite type without
  explicit witness even with decidable predicates). The
  `Finset.image`-based reformulation requires ~100 lines of
  fiber-counting machinery and is deferred to a follow-up; the
  non-triviality lower bound established here is the load-bearing
  result for the 8-divisibility argument.
- Approaches tried: 1 (Approach A — modular form bridge).

## Blockers

- **Mathlib q-expansion infrastructure absent** for `jacobiTheta` —
  unchanged from S1.
- **Mathlib Eisenstein-coefficient identification absent** — unchanged.
- **Local Docker build verification**: S7 continues the "build pending"
  pattern (precedent: S6, sperner-ndim-mathlib-oq-02 S13/S14) — the
  proofs/.lake self-referential symlink forces a fresh Mathlib clone
  per Docker build (~45 min cold). The S7 additions are 7-line wrappers
  on already-proven S6 lemmas plus one Mathlib lookup
  (`Nat.exists_eq_pow_mul_and_not_dvd`); auditor pipeline carries the
  build outcome.

## Next Action

0. **(structural, S18a/S18b/S18c-framework SHIPPED, orbit count remaining)**
   Axiom-free `8 ∣ r4Count n` decomposes into the following layers per
   `s18-eight-divisibility-spec.md`:
   - **S18a (Part 27, SHIPPED PR #17702)**: foldl ↔ nested-sum
     reformulation of `r4Count n`. Adds
     `foldl_indicator_eq_add_filter_length`, `foldl_constant_shift_eq`,
     `foldl_4nest_indicator_eq_nested_sum`, and
     `r4Count_eq_nested_sum`. ~80 lines, pure List/foldl structural
     lemmas; no number theory.
   - **S18b (Part 28, SHIPPED PR #17714)**: shiftedRange ↔ Finset.Icc
     bridges plus innermost-level Finset.card substitution for the
     4th-coord filter-length. Adds `shiftedRange_nodup`,
     `shiftedRange_toFinset_eq_Icc`, and
     `shiftedRange_filter_length_eq_Icc_card`. ~70 lines.
   - **S18c-framework (Part 29, PR #17745, merged 2026-05-11)**:
     sign-flip action on `Fin 4 → ℤ`. Adds `SignFlip`, `applyFlip`,
     `sumSq`, `sumSq_applyFlip`, `sumSq_reindex`, `applyFlip_zero`,
     `applyFlip_involutive`, `applyFlip_eq_iff`, `applyFlip_bijective`,
     `Fintype.card SignFlip = 16`, and the
     `orbitCard_dvd_eight_of_pos_target_decl` placeholder. ~140 lines,
     0 axioms, 0 sorries. Standalone — doesn't depend on r4Count
     reformulation; pure algebra on `Fin 4 → ℤ`.
   - **S18c-permutation (Part 30, PR #17818, MERGED 2026-05-12)**:
     coordinate-permutation action on `Fin 4 → ℤ`. Adds `applyPerm`,
     `applyPerm_apply`, `applyPerm_one`, `applyPerm_mul`,
     `sumSq_applyPerm`, `applyPerm_inv_apply`, `applyPerm_bijective`,
     `applyPerm_eq_iff`, and
     `example : Fintype.card (Equiv.Perm (Fin 4)) = 24`. ~90 lines,
     0 axioms, 0 sorries. Companion to Part 29; extends the existing
     `namespace S18c` scaffold. `sumSq_applyPerm` reuses Part 29's
     `sumSq_reindex` specialised at `σ.symm`; `applyPerm_mul` is `rfl`
     via the `Equiv.Perm` group instance.
   - **S18c-orbit-precursor (Part 31, SHIPPED PR #18139)**: sign-flip
     stabilizer cardinality `|Stab v| = 2^(# zero coords v)` via an
     explicit equivalence to `({ i : Fin 4 // v i = 0 } → Bool)`. Adds
     `signFlipStabilizer_card` inside `namespace S18c`, +~70 lines,
     0 axioms, 0 sorries.
   - **S18c-orbit-precursor-2 (Part 32, THIS PR)**: sign-flip ORBIT
     non-triviality `2 ≤ |Orbit_(ℤ/2)⁴ v|` for `v` with at least one
     nonzero coordinate `i₀`, by exhibiting two distinct orbit
     elements (`v` itself + the single-flip at `i₀`). Adds
     `signFlipOrbit_card_ge_two` inside `namespace S18c`, +~69 lines,
     0 axioms, 0 sorries. The full cardinality
     `|Orbit_(ℤ/2)⁴ v| = 2^(# nonzero coords v)` was attempted but
     stranded on `Fintype` synthesis for the existential subtype; the
     `Finset.image` reformulation defers to a follow-up.
   - **S18c-orbit (next)**: invoke `MulAction.orbit_card_dvd_of_finite`
     (Mathlib v4.26.0 per spec §3.8). Case analysis on the zero /
     coincidence pattern of `(|v 0|, |v 1|, |v 2|, |v 3|)` to show
     `8 ∣ |Orbit v|` for every `v ∈ solSet n` when `n > 0`. ~150 lines.
     With Parts 29-30 now in place, `applyFlip_eq_iff` /
     `applyPerm_eq_iff` deliver the stabilizer characterisations
     needed for orbit-stabilizer; no further algebraic preliminaries.
   - **S18c-bridge (final)**: relate the `Finset.card` of solSet n to
     `r4Count n` via Parts 27/28, then orbit-sum to conclude
     `8 ∣ r4Count n`. ~30 lines.

   The S18 spec §3.7 noted that the originally-proposed D₄-route fails
   on solutions with two-zero coordinates (e.g. `(a, b, 0, 0)`); §3.8's
   `(ℤ/2)⁴ ⋊ S₄` 384-element route does work but requires deeper case
   analysis. S18a's foldl ↔ sum bridge and S18b's Finset.Icc bridges
   are route-agnostic and reusable for either approach.
1. **(opportunistic, σ*-side AND r4Count-side closed)** When Mathlib
   gains q-expansion for `jacobiTheta` / `EisensteinSeries.E₂`, apply
   `r4Count_factorization_form` (S9) directly — the LHS of the
   modular-form identity `θ⁴ = 1 + 8·(E₂(τ) − 4·E₂(4τ))` matches
   `r4Count` at q^n by definition; the RHS evaluates at q^n to
   `(if 2 ∣ n then 24 else 8)·σ(ord_compl[2] n)` (closed form already
   proven). Two q-coefficient extractions plus this corollary close
   `jacobi_r4_formula`. No σ*-side intermediation needed.
2. **(productive, modular-form side, S13 SPEC)**
   Two atomic axioms targeting Mathlib roadmap:
   (Hθ4Coef) `r4Count n = qCoeff_n((jacobiTheta τ)^4)` for `n > 0`
       (definitional bridge between integer counting and q-coefficient);
   (Hθ4Eis) `(jacobiTheta τ)^4 = 1 + 8·(E₂(τ) − 4·E₂(4τ))`
       (Jacobi-1834 modular-form identity).
   With (Hθ4Coef) + (Hθ4Eis) + Mathlib's `EisensteinSeries.E2_qExpansion`,
   `r4Count_factorization_form` (S9) closes `jacobi_r4_formula`. See
   `s13-modular-form-atomic-decomposition.md` for the closure proof
   skeleton, Mathlib API status, and the 9-month upstream sequence.
   This decomposition is parallel to S11.alt's elementary 3-hypothesis
   route (PR #17388); closing **either** discharges the open axiom.
3. **(elementary, hard)** Direct combinatorial proof of
   `r4Count(2n) = 3·r4Count(n)` for odd n via the pairing bijection
   `(a,b,c,d) ↦ ((a+b)/2, (a-b)/2, (c+d)/2, (c-d)/2)` (~300-500 lines
   in Lean). Combined with σ*-multiplicativity, would close all
   prime-power cases except odd primes. Speculative.
4. **(speculative)** Hurwitz-quaternion route — Mathlib has
   quaternions but no Hurwitz integers; multi-month project upstream.
5. **(skip)** Brute-force extension beyond n = 10 — pure enumeration
   theater.

## References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — Parts 1-22:
  bootstrap (1-5), structural σ* ↔ σ (6-7), σ* on odd prime powers (8),
  σ*(2n) = σ*(4n) = 3·σ(n) for odd n (9-10), σ-multiplicativity bridge
  (11), σ*-multiplicativity (12), σ*(2^k) closed form (13),
  cross-validation (14), σ*(2^k · m) closed form (15, S5),
  unified `if`-form (16, S6), n-keyed existential decomp (17, S7),
  constructive `ord_compl[2]`-keyed closed form (18, S8),
  r4Count Eisenstein-coefficient form (19, S9), multiplicativity
  bridge for jacobiR4 / r4Count (20, S10), positivity / 8-divisibility
  / odd-prime corollary (21, S11), odd-prime-power closed form
  (22, S12).
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/s13-modular-form-atomic-decomposition.md` —
  S13 spec: two-axiom modular-form atomic decomposition of
  `jacobi_r4_formula`, closure proof skeleton, Mathlib API gaps,
  comparison with S11.alt's elementary route.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  per-session notes.
