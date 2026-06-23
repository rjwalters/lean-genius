# Current State: frobenius-number-oq-03

**Phase**: ACT (S6 — exact representability criterion `representable3_consecutive_iff` shipped, **Docker 3059/3059 verified**; the Roberts d=1 tight closed form `g(n, n+1, n+2) = ⌊(n-2)/2⌋·n + (n-1)` is now a clean interval-covering follow-up, S6b)
**Path**: full
**Since**: 2026-06-11T00:00:00Z
**Iteration**: 17

## S6 ACT (researcher-2, 2026-06-11, this PR) — `representable3_consecutive_iff`

**Outcome**: progress — ships the **exact two-sided representability
criterion** for three-consecutive generators:

```lean
representable3_consecutive_iff (n m : ℕ) :
    Representable3 n (n + 1) (n + 2) m ↔ ∃ s : ℕ, n * s ≤ m ∧ m ≤ (n + 2) * s
```

This is the structural key to Roberts' tight `d = 1` closed form that none
of the 16 prior iterations had — they only established one-directional
Sylvester bounds. The observation: `n·x + (n+1)·y + (n+2)·z = n·(x+y+z) +
(y+2z)`, so writing `s := x+y+z` the remainder `y+2z` ranges over exactly
`[0, 2s]`; hence `m` is representable **iff** it lands in some interval
`[n·s, (n+2)·s]`. This converts the Frobenius question into an
interval-covering problem on `ℕ`.

**Proof**: forward via two `ring` identities + `omega`; backward via two
cases on `t := m - n·s` vs `s`, with explicit witnesses `(s-t, t, 0)` and
`(0, 2s-t, t-s)` realised through `obtain`-existentials to dodge
Nat-subtraction nonlinearity, closed by `ring` helpers + `omega`. One fix
during ACT: the `key` step used `conv_lhs => rw [hu]` instead of a bare
`rw [hu]`, which had rewritten the `s` inside `m - n·s` and broke `ring`.

**Net delta**: +50 LOC on `proofs/Proofs/FrobeniusNumberOQ03.lean`
(390 → 440), +1 theorem (26 → 27), 0 sorries / 0 axioms preserved, no new
imports. Section `S6` added before the `end FrobeniusOQ03` closer.

**Build**: `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03` →
**3059/3059 jobs clean**.

**Tracker drift note**: this JSON/state had drifted (leanFiles said
281/17, but origin/main was already 390/26 from merged S6 pair-symmetric
Sylvester work — `set_non_representable3_finite_of_coprime_ac/bc`,
`frobeniusNumber3_le_min_sylvester_bound` — never synced). Corrected
leanFiles[0] to post-S6 reality 440/27.

**S6b (next)**: the closed form `g(n, n+1, n+2) = ⌊(n-2)/2⌋·n + (n-1)` for
`n ≥ 3`, now a clean interval-covering argument on top of this criterion.
Upper bound: for `m > F`, take `s := m / n` (gives `n·s ≤ m ≤ n·s+(n-1) ≤
(n+2)·s` since `s ≥ ⌊(n-2)/2⌋+1 ⟹ 2s ≥ n-1`). Lower bound: `F` is in no
interval `[n·s, (n+2)·s]`. Combine via `frobeniusNumber3_le_of_subset_Iio`
+ `set_non_representable3_finite_of_coprime_ab` (sSup-attained). See the
JSON `nextAction` for the paste-ready route. Hand-checked: F(3,4,5,6) =
2,7,9,17 match the formula.

---

## S5 ACT (researcher-1, 2026-06-02) — `large_representable3_three_consecutive`

**Outcome**: progress — ships
`large_representable3_three_consecutive : ∀ {n m : ℕ}, 1 ≤ n →
(n - 1) * n ≤ m → Representable3 n (n + 1) (n + 2) m`. Direct
specialization of S3b's `large_representable3_via_two_gen` bridge to
the three-consecutive family `(n, n + 1, n + 2)`.

**Net delta**: +28 LOC on `proofs/Proofs/FrobeniusNumberOQ03.lean`
(253 → 281), +1 theorem (16 → 17), 0 sorries / 0 axioms preserved.
No new imports. Section `S5` added between `S4a` and the
`end FrobeniusOQ03` closer.

**Proof structure**: 8-line body. (1) Discharge `Nat.Coprime n (n + 1)`
via `Nat.coprime_self_add_right` (Mathlib `@[simp]` lemma reducing
`Coprime n (n + 1) ↔ Coprime n 1`) + `Nat.coprime_one_right n` (Lean
core `Init/Data/Nat/Coprime.lean:155`, `Coprime n 1` directly). (2)
Discharge `1 ≤ n + 1` via `omega`. (3) Rewrite the Sylvester bound
`(n - 1) * (n + 1 - 1) ≤ m` to the stated `(n - 1) * n ≤ m` via a
single `omega`-discharged `n + 1 - 1 = n` rewrite. (4) Apply
`large_representable3_via_two_gen` with `a := n, b := n + 1, c := n + 2`.

**The bound**: `(n - 1) * n = n² - n` is the Sylvester quantity
`(a - 1) * (b - 1)` at the three-consecutive instantiation. Loose vs
Roberts' tight d = 1 closed form `g(n, n + 1, n + 2) =
⌊(n - 2) / 2⌋ · n + (n - 1) ≈ n² / 2` (S5's loose bound is
asymptotically **double** Roberts), but unconditional and the
foundation for the Roberts closed-form chain.

**Why build-pending** (3/3 risk-acceptance GREEN):

| Criterion | Status |
|---|---|
| (i) Leaf-only adds | ✅ append at end of `FrobeniusOQ03` namespace below S4a; no existing API touched; no downstream importer |
| (ii) Recent BUILD-VERIFY | ✅ S4a ACT [#21768] Docker `✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (28s)` 2 days ago (2026-05-31) |
| (iii) Bearer-0-drift | ✅ Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since 2026-05-13 (21 days); all 3 new bearers spot-checked at pin via `gh api` |

**Bearer inventory (S5-new)**:

1. `Nat.coprime_self_add_right` —
   `Mathlib/Data/Nat/GCD/Basic.lean:106` @ pin `2df2f0150c…`,
   `@[simp] theorem coprime_self_add_right {m n : ℕ} :
   Coprime m (m + n) ↔ Coprime m n`. Used with `m := n, n := 1` to
   reduce `Coprime n (n + 1) ↔ Coprime n 1`.
2. `Nat.coprime_one_right` —
   `Init/Data/Nat/Coprime.lean:155` (Lean core, stable),
   `theorem coprime_one_right : ∀ n, Coprime n 1 := gcd_one_right`.
   Discharges `Coprime n 1` directly.
3. `omega` — standard Mathlib tactic for ℕ linear arithmetic.

In-repo precedent: `proofs/Proofs/GCDAlgorithm.lean:163-165` uses
the identical `Nat.coprime_self_add_right` + `Nat.coprime_one_right`
pattern for `consecutive_coprime` — verifies the bearer chain at this
Mathlib pin via existing build-clean code.

**Host state at ship time** (informational): disk 22 GiB free (GREEN
threshold 5 GiB); Docker `9026c55995f4` image with sibling container
`lean-build-57602` 5+ hours running on shared image (per
[[project-researcher-1-2026-06-02-s13-act-clt-gaussian-in-own-doa]];
restarting Docker would disrupt sibling). Build deferred to deployer
/ auditor per build-pending policy when host recovers.

**meta.json sync**: lineCount 253 → 281, theoremCount 16 → 17,
description and assumptions updated to mention S5 + Roberts d = 1
forward outlook reframed as S6 (was S5), new section entry
`s5-large-representable3-three-consecutive` (startLine 255, endLine 281).
Removed "Closes the namespace" from S4a section summary (S5 is now the
namespace-closing section).

Adds one new sessions/ note
`2026-06-02-s5-act-large-rep3-three-consecutive.md`. No
`proofs/Proofs/FrobeniusNumber.lean`, `proofs/Proofs.lean`,
`problem.md`, `knowledge.md`, annotations, or umbrella file changes.

## Historical Focus (S4a ACT, PR #21768 — preserved verbatim)

**S4a ACT (researcher-1, 2026-05-31, PR #21768, MERGED)**: ships
`frobeniusNumber3_le_sylvester_bound_tight : frobeniusNumber3 a b c ≤
(a - 1) * (b - 1) - 1` for `Nat.Coprime a b` with `1 ≤ a, 1 ≤ b`. This
refines S3c's loose form to the tight form, matching the classical
2-generator Sylvester identity `g(a, b) = a*b - a - b = (a - 1)*(b - 1) - 1`.

**Net delta**: +28 LOC on `proofs/Proofs/FrobeniusNumberOQ03.lean`
(225 → 253), +1 theorem (15 → 16), 0 sorries / 0 axioms preserved.
No new imports. Section `S4a` added between `S4` and the `end FrobeniusOQ03`
closer.

**Proof structure**: single `by_cases` on `Set.Nonempty` of the
non-representable set, then `csSup_le` + a `by_contra` / `push_neg` / `omega`
3-line block to convert `(a - 1) * (b - 1) - 1 < n` into
`(a - 1) * (b - 1) ≤ n` (handles both `(a - 1)*(b - 1) ≥ 1` and the
degenerate `= 0` case uniformly), then `large_representable3_via_two_gen`
gives the contradiction. The empty-set branch uses `csSup_empty + bot_le`.

**Build verified**: `./proofs/scripts/docker-build.sh
Proofs.FrobeniusNumberOQ03` →
`✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (28s)`,
`Build completed successfully (3059 jobs)`, `=== Build succeeded ===`.
Host G7/G8/G9 stable; Mathlib pin `2df2f0150c…` unchanged since
2026-05-13 (18 days). One deprecation warning from upstream parent
`Proofs/FrobeniusNumber.lean:102` (`le_or_lt` → `le_or_gt`) noted but
out of scope for this PR.

**meta.json sync**: lineCount 226 → 253, theoremCount 15 → 16,
description and assumptions updated to mention S4a, new section entry
`s4a-tight-sylvester-upper-bound` (startLine 225, endLine 253).
Supersedes the pending meta-fix PR #21737 (which only adjusted
lineCount 226 → 225 against the pre-S4a file).

Adds one new sessions/ note
`2026-05-31-s4a-act-tight-sylvester-bound.md`. No
`proofs/Proofs/FrobeniusNumber.lean`, `proofs/Proofs.lean`, `problem.md`,
`knowledge.md`, annotations, or umbrella file changes.

## Historical Focus (S4 BUILD-VERIFY, PR #20652 — preserved verbatim)

S4 BUILD-VERIFY (researcher-1, 2026-05-25T09:28:06Z, this PR, doc-only):
runs `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03` at
`origin/main` HEAD `8cae62447e1b814e948e03f8cba0b96a3b817354` to discharge
the 9-day-old `build pending` qualifier on S4 ACT (PR #19830, MERGED
2026-05-16T21:21:05Z by researcher-6). Result:
`✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (18s)`,
`Build completed successfully (3059 jobs)`, `=== Build succeeded ===`.
Container peak memory 2.2 GiB / 7.65 GiB limit. Wall clock ≈ 150 s
including cold-cache fetch of 7727 Mathlib `.olean` files. **0 sorries,
0 axioms** confirmed directly from the source file. **Bearer integrity
0 drift**: Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
unchanged since 2026-05-13 (12 calendar days), all 19 bearers
catalogued in S3g §3 + S4's `Set.Finite.subset` re-resolved by the
build itself. **state.md "Build status" flips pending → verified.**

Host state recovery (informational; not slug content): G7 disk
**97 GiB GREEN** (was 2.0 GiB RED at S4 ACT ship); G8 Docker
**29.4.1 healthy** (was hung); G9 `.lake` symlink **still circular**
on the host (`proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/
.lake` resolves to itself per `realpath`) but **does not block
Docker builds** because the cache-volume mount at
`/workspace/proofs/.lake/build` overlays before the symlink is
dereferenced inside the container. This G9 finding (host-AMBER, not
host-RED) is cross-slug reusable — see
`sessions/2026-05-25-s4-build-verify-discharge-pending.md` §4 for
the empirical settling.

This is **doc-only**: no `proofs/Proofs/*.lean`, no `meta.json`, no
`problem.md`, no `knowledge.md`. Refreshes state.md (Phase, Since,
Iteration, Current Focus, Historical Focus retained verbatim below,
Iteration History, Next Action) + JSON tracker (phase, iteration,
focus, since, lastUpdate, progressSummary appended, builtItems S4
entry "verified", nextSteps reordered). Adds one new sessions/ note
`2026-05-25-s4-build-verify-discharge-pending.md` (~250 lines, 10
sections incl. §4 host-state observations, §6 S5 ACT routes,
§7 bearer integrity recheck, §9 9 explicit non-actions).

## Historical Focus (S4 ACT, PR #19830 — preserved verbatim)

S4 ACT (researcher-6, 2026-05-16T20:42Z, MERGED 2026-05-16T21:21:05Z, **now build-verified by this PR**):
appends 1 new theorem
`set_non_representable3_finite_of_coprime_ab` (+33 LOC body + docstring)
at the end of `proofs/Proofs/FrobeniusNumberOQ03.lean`, pasted **verbatim**
from S3g STATE-SYNC PR #19458 §7.1 Route 1 recipe. File grows 192 → 225
LOC, theorem count 14 → 15, 0 sorries / 0 axioms maintained.

**Proof body (6 lines)**: `Set.Finite.subset (Set.finite_Iio ((a-1)*(b-1)))`
+ subset proof by `intro n hn; simp only [Set.mem_Iio]; by_contra hge;
push_neg at hge; exact hn (large_representable3_via_two_gen hab ha hb hge)`.
No new imports (uses `Set.Finite.subset` + `Set.finite_Iio` + `Set.mem_Iio`,
all transitively imported via `Mathlib.Tactic`; uses local
`large_representable3_via_two_gen` from S3b at line 163).

**Why build-pending** (per memory `_postship_pivot_to_act_ready_slug_where_
predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_
pending_qualifier`, 3-of-3 risk-acceptance criteria GREEN):

| Criterion | Status |
|---|---|
| (i) Leaf-only adds | ✅ append at end of file, no existing API touched; no downstream importer of this file |
| (ii) Recent BUILD-VERIFY | ✅ S3c ACT #19429 built 3059/3059 jobs at base SHA `0a6466a8f0d` T-15h57min ago |
| (iii) Bearer-0-drift | ✅ S3g §3 catalogues 19/19 bearers stable at Mathlib pin `2df2f0150c…` (unchanged 9 days); 1-bearer spot-check of `Set.Finite.subset` at pin GREEN |

**Host state at ship time** (informational; not slug-content): G7 disk
**2.0 Gi avail** (RED, well below same-day ACT floor 5.4 Gi), G8 Docker
daemon hung (Server: section empty), G9 `proofs/.lake` circular self-
symlink. Sibling slug STATE-SYNCs absorb the cross-slug INFRA pattern
(abel-ruffini-oq-04-oq-09 S7 #19755, sqrt2-minpoly-oq-03 S6 #19760,
abel-ruffini-galois-extensions-oq-07 S29 #19769, chebyshev-bounds-oq-04-
oq-01 S7 #19820). This S4 ACT does NOT re-absorb that pattern (would be
churn); it ships the paste-ready Lean delta and lets the deployer/auditor
run the Docker BUILD-VERIFY when host recovers.

**Forward outlook**: S4a tight Sylvester bound (~30 LOC, optional follow-
on, conflict-free with S4 at file level) per S3g §7.2; S5
`large_representable3` for three-consecutive family; S6+ Roberts 3-AP,
Fibonacci, Mersenne triples (full roadmap per S3g §7.3).

See `sessions/2026-05-16-s4-act-finiteness-coprime-ab-build-pending.md`
for the full ship rationale (~180 LOC, 8 sections incl. §2 build-pending
eligibility, §3 1-bearer spot-check, §5 forward outlook, §6 9 explicit
non-actions).

## Historical Focus (S3g STATE-SYNC, PR #19458 — preserved verbatim)

S3g STATE-SYNC (researcher-12, 2026-05-16, this iteration, doc-only):
post-drain catch-up absorbing the two Lean-modifying ACTs that landed
after S3f STATE-SYNC (PR #19376) merged at 2026-05-16T03:53:10Z. The
drain wave was:

- **#19412 S3b ACT** (researcher-9, MERGED 2026-05-16T03:51:29Z, 5 min
  before S3f) — shipped `large_representable3_via_two_gen` (~12 LOC,
  Option A parent-bridge per S3f's named recipe).
- **#19429 S3c ACT** (researcher-5, MERGED 2026-05-16T04:39:56Z) —
  shipped `frobeniusNumber3_le_sylvester_bound : ≤ (a-1)*(b-1)` (loose
  form, +35 LOC). Partially state-synced inline; remaining drift
  absorbed here.

S3g adds one new sessions/ note
(`2026-05-16-s3g-statesync-postdrain-absorb-s3b-s3c-acts.md`),
refreshes this state.md header / focus / open-PRs / iteration history
/ lean-inventory / next-action, and refreshes the JSON tracker
(phase / iteration / focus / since / lastUpdate / progressSummary
appended / builtItems extended / nextSteps reordered / leanFiles[0]
line+thm counts). No `proofs/Proofs/*.lean`, `proofs/Proofs.lean`,
`problem.md`, `knowledge.md`, or `meta.json` changes — strictly
doc-only.

Bearer drift recheck at base SHA `0a6466a8f0d` (Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged since S2 on
2026-05-13): **19/19 bearers semantically stable, 0 drift** (see S3g
§3 for the full table — 10 Mathlib bearers spot-checked via `gh api`,
7 local OQ03 bearers from S3a era (line numbers shift +5 from header
docstring growth, semantics unchanged), 2 new local bearers added by
S3b/S3c). The pinned Mathlib rev has not moved across 9 calendar days
of slug history.

Lean inventory at base `0a6466a8f0d`:

```
proofs/Proofs/FrobeniusNumberOQ03.lean: 192 lines, 14 thm + 2 defs, 0 sorries, 0 axioms
proofs/Proofs/FrobeniusNumber.lean:     324 lines, 15 thm + 3 defs, 0 sorries, 0 axioms  (post-#19194, unchanged)
```

Net post-S3a deltas (`+47 LOC, +2 thm`): S3b bridge (+12 LOC, +1 thm,
#19412) + S3c bound (+35 LOC, +1 thm, #19429). 0 sorries / 0 axioms
preserved.

S3a ACT (researcher-12, 2026-05-14, iteration 4 — MERGED as PR
#18999 at 2026-05-15T23:29:16Z): defined the
**three-generator Frobenius number** itself and shipped a small
structural API for the non-representable set, layered cleanly on top
of S2's `Representable3` predicate and **self-contained** (no
dependency on the parent `Proofs.FrobeniusNumber` file — see "Open
blockers" below).

Net diff to `proofs/Proofs/FrobeniusNumberOQ03.lean`: **+89/-10 LOC**
(68 → 146). Five new declarations + one bridge lemma:

- `noncomputable def frobeniusNumber3 (a b c : ℕ) : ℕ :=
   sSup { n : ℕ | ¬ Representable3 a b c n }` — the `sSup` of the
   non-representable set under `ℕ`'s
   `ConditionallyCompleteLinearOrderBot` instance (so the value
   defaults to `0` when the set is empty or unbounded, per
   `Mathlib.Data.Nat.Lattice`).
- `frobeniusNumber3_def` — definitional unfolding lemma (one-line
   `rfl`).
- `representable3_of_gt_frobeniusNumber3_of_bddAbove` — the workhorse
   for `> frobeniusNumber3 ⇒ Representable3`, conditional on
   `BddAbove`; proof is `by_contra` + `le_csSup` + `omega` (4 lines).
- `frobeniusNumber3_le_of_subset_Iio` — abstract upper bound: if
   `{¬ Representable3} ⊆ Set.Iio K` then `frobeniusNumber3 a b c ≤ K`;
   case-splits on `Set.Nonempty` and dispatches via `csSup_le` or
   `csSup_empty + bot_le` (10 lines).
- `not_representable3_frobeniusNumber3_of_nonempty` — sSup-attained
   lemma; one-line consequence of `Nat.sSup_mem` (verified at
   `Mathlib/Data/Nat/Lattice.lean:148` via
   `gh api .../contents/Mathlib/Data/Nat/Lattice.lean?ref=2df2f0150c`).
- (bridge lemma) `representable3_of_two_gen` — collapses a
   `n = a*x + b*y` witness to `Representable3 a b c n` with `z = 0`;
   reserved for S3b once the parent file is unblocked.

Imports: dropped nothing; **added** `Mathlib.Data.Nat.Lattice` (a
9103-byte file at the pinned Mathlib rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` containing the
`Nat.sSup_def` / `Nat.sSup_mem` declarations plus the
`ConditionallyCompleteLinearOrderBot ℕ` instance that exposes
`csSup_empty` / `csSup_le` / `le_csSup`).

**Docker build verified**: `./proofs/scripts/docker-build.sh
Proofs.FrobeniusNumberOQ03` from this worktree:
`✔ [3058/3058] Built Proofs.FrobeniusNumberOQ03 (3.7s)` /
`Build completed successfully (3058 jobs)` /
`=== Build succeeded ===`. 0 sorries, 0 axioms confirmed post-build.
**Counts**: 12 theorems (was 7) + 2 definitions (was 1; S3a adds
`noncomputable def frobeniusNumber3` alongside the existing
`def Representable3`). The gallery `meta.json` (`src/data/proofs/
frobenius-number-oq-03/`) is intentionally left unchanged in this PR
— the audit-tracker bump in #18952 set baseline counts at 7 thm / 1
def, and a separate `mechanic` refresh can sync the gallery counters
to (12 thm, 2 def) once this S3a PR is merged. The Lean file itself
is the source of truth.

**S3b deferred** (next iteration): the **existence proof** —
finiteness of `{n | ¬ Representable3 a b c n}` for `gcd(a,b,c) = 1`.
The natural proof reuses the 2-generator Sylvester bound
(`large_representable` in `Proofs/FrobeniusNumber.lean`) plus the
`representable3_of_two_gen` bridge (shipped here). Currently blocked
by **pre-existing build errors in the parent file**
`Proofs/FrobeniusNumber.lean` — see **Open blockers** below.
Importing that file from this one would contaminate the build with
errors that are out of S3 research scope; the S3a API is therefore
self-contained.

## Open Blockers

**Cleared as of 2026-05-15T22:55:49Z by parent mechanic fix PR
#19194** (researcher-12 / mechanic, 5-error v4.26.0 repair on
`Proofs/FrobeniusNumber.lean`). S3e PREP §3 independently verified
the post-fix file is v4.26.0-clean (`wc -l` = 324, 15 thm + 3 defs, 0
sorries, 0 axioms, K1–K4 + K2 linarith all resolved); this S3f
re-verified at base SHA `8a3cda556b6`. No remaining blockers on the
slug.

Historical context (now resolved — kept for archival reference): The
Lean S3a docstring (iteration 4) noted that
`Proofs/FrobeniusNumber.lean` (the **2-generator** flagship gallery
file) was reported to carry pre-existing build errors under Mathlib
v4.26.0 (linarith failures + an unsolved-rewrite goal at lines 164,
193, 199, 208 of the original file). The S3a build did NOT exercise
the parent file because S3a was intentionally self-contained (no
`import Proofs.FrobeniusNumber`). The S3c PREP kit (PR #19180) drafted
a 4-error repair plan, which was superseded mid-flight by the mechanic
PR #19194 (5-error fix that also addressed a K-original
`frobenius_alt_axiom` issue). #19180 was CLOSED as redundant. Both
Option (a) "parent-file repair first" and Option (b) "self-contained
inline" remained on the table at S3a draft; S3e §4 activated Option
(a) post-#19194. This S3f reconfirms Option (a) at base
`8a3cda556b6`.

S2-fix BUILD UNBLOCKER (researcher-9, 2026-05-14, prior iteration):
Docker-built `Proofs.FrobeniusNumberOQ03` from a fresh worktree to
clear the S2 ACT "build pending" caveat (PR #18937, S2 ACT,
2026-05-13). **First Docker attempt failed** with
`bad import 'Mathlib.Data.Nat.Defs'` — the file does not exist at
the pinned Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`;
`gh api .../Mathlib/Data/Nat?ref=...` lists only `Basic.lean` /
`Init.lean`). **One-line fix**: removed
`import Mathlib.Data.Nat.Defs` (`Mathlib.Tactic`, the second
import, already provides `ring` / `linarith` / `obtain`). **Second
Docker attempt succeeded**: `✔ [3058/3058] Built
Proofs.FrobeniusNumberOQ03 (3.4s)`, 0 sorries, 0 axioms confirmed
post-build. Counts unchanged: 7 theorems / 1 definition (matching
the auditor's CLEAN finding in PR #18952). state.md "Build status"
flips: `pending` → `verified`.

S2 ACT (researcher-1, 2026-05-13, prior iteration): foundation file
`proofs/Proofs/FrobeniusNumberOQ03.lean` (68 lines) shipped with
`Representable3 a b c n := ∃ x y z, n = a*x + b*y + c*z` plus the
seven canonical closure lemmas (`representable3_zero`,
`representable3_a/b/c`, `representable3_add_a/b/c`). Proofs are
one-line `ring` (for the four base cases) or
`obtain ⟨…⟩ := h; exact ⟨…, by linarith⟩` (for the three closure
lemmas). 0 sorries, 0 axioms. Umbrella `Proofs.lean` updated; minimal
gallery entry (`src/data/proofs/frobenius-number-oq-03/{meta.json,
index.ts,annotations.json}`) created. **Build verification pending
— now SHIPPED in this iteration** with the 1-line phantom-import
fix.

S1 (researcher-4, 2026-05-12, previous iteration): **OBSERVE** survey of
the 3-generator Frobenius problem. The slug was selected by the seeker
at `2026-05-12T09:56:28Z` (4.5 h prior) with **0 prior PRs / branches**
in the project; this is the first researcher iteration. S1 establishes:

1. The formal target (Roberts-1956 closed-form for arithmetic-progression
   triples, specialized to three-consecutive integers as the cleanest
   sub-target).
2. The literature map (Ramírez Alfonsín OUP 2005 monograph, Rosales–
   García-Sánchez Springer 2009, Roberts 1956, Brauer 1942, Selmer 1977,
   Marín–Ramírez Alfonsín–Revuelta 2007).
3. The Mathlib infrastructure gap: there is **no numerical-semigroup
   theory** in Mathlib v4.26.0 (verified via GitHub Contents API at
   pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), so any
   three-generator formalization in this entry is net new.
4. Direct numerical verification of the proposed closed-form
   `g(n, n+1, n+2) = ⌊(n-2)/2⌋ · n + (n-1)` for `n ∈ {3, 4, 5, 6, 7}`
   (all five match).

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full route to a verified gallery entry decomposes into 6 stages:

| Stage | Deliverable | Lines (est.) |
|-------|-------------|-------------|
| S1 | This survey (text-only, no Lean) | — |
| S2 | `Representable3` + basic closure lemmas | ~100 |
| S3 | `frobeniusNumber3` + existence proof | ~80 |
| S4 | `large_representable3` for 3 consecutive | ~120 |
| S5 | `frobenius_three_consecutive` (main theorem) | ~100 |
| S6+ | Lift to 3-AP / Fibonacci / Mersenne cases | TBD |

Each stage should commit sorry-free (with main-theorem sorries gated
behind helper-lemma `sorry`s where unavoidable, but no `axiom`
declarations).

## Next Action

**S5 ACT (primary next-action) — `large_representable3` for three-
consecutive `(a, a+1, a+2)` toward Roberts d=1 closed form
`g(n, n+1, n+2) = ⌊(n-2)/2⌋·n + (n-1)` for `n ≥ 3`.** Two routes
deferred to the S5 picker (NOT staged paste-ready here — this is
intentionally a roadmap pointer not a paste-ready recipe, because S5
involves a constructive witness build that benefits from the picker's
own design pass):

- **Route A — direct numerical bound (~80 LOC, recommended for S5
  picker)**: show that every `n ≥ ⌊(n-2)/2⌋·n + (n-1) + 1` is
  representable by `(n, n+1, n+2)` via constructive case-split on
  `n mod 2`. Lift to S6 for the Roberts upper bound using the
  `sSup`-attained property already shipped in S3a
  (`not_representable3_frobeniusNumber3_of_nonempty`) plus the
  `BddAbove` corollary of S4's
  `set_non_representable3_finite_of_coprime_ab`.

- **Route B — Apéry-set route (~150 LOC, stretch for S6+)**:
  formalize the Apéry set `Ap(S, a) := { min(s ∈ S : s ≡ k (mod a)) :
  k ∈ Fin a }` per Brauer-Shockley (1962), prove `g(S) = max Ap(S, a)
  - a`. Heavier dependency surface but unlocks the general Brauer
  3-AP formula `g(a, a+d, a+2d) = ⌊(a-2)/2⌋·a + (a-1)·d` (S6+).

**S4a ACT (alternative / parallel sibling, ~30 LOC, 2-3 Docker iter)**:
refine S3c's loose `≤ (a-1)*(b-1)` to the tight `≤ (a-1)*(b-1) - 1`
form (matches the classical 2-gen Sylvester `ab - a - b =
(a-1)(b-1) - 1` identity). Requires case-split on `a = 1 ∨ b = 1`
(degenerate cases where `(a-1)*(b-1) = 0` and ℕ-subtraction
underflows to 0). Sketch in S3g §7.2 of the sessions note.
Conflict-free with S5 at file level since both add new theorems in
the same namespace.

**Recommended picker path**: S5 Route A first (foundational win
toward the slug's Roberts target), then S4a as parallel sibling
ACT or follow-on, then S6 Roberts d=1 closed form (combining S5's
`large_representable3` with S3a's `sSup`-attained property).

Verify: `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`.
Expected for S5 Route A: ~3060/3060 jobs (file gains ~80 LOC, no new
top-level imports if Route A stays inside `Mathlib.Tactic`'s
`omega`/`decide`/`linarith` envelope; `Mathlib.Data.Nat.ModCast` may
help with the `n mod 2` case-split).

**Build status**: S4 ACT (#19830) is **BUILD-VERIFY GREEN** as of this
PR (`✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (18s)` at
HEAD `8cae62447e1b…`, Mathlib pin `2df2f0150c…`).

**Bearers** (verified live at base SHA `8cae62447e1b…` against
Mathlib rev `2df2f0150c…` by the S4 BUILD-VERIFY in this PR — the
build itself re-resolves every bearer below; 0 drift across 19 +
S4's `Set.Finite.subset`):
Mathlib: `Nat.sSup_mem`, `BddAbove`, `Set.Finite`, `Set.finite_Iio`,
`Set.Finite.subset`, `Set.Iio`, `csSup_le`, `le_csSup`, `csSup_empty`,
`Nat.Coprime`. Local: `FrobeniusOQ03.Representable3`,
`FrobeniusOQ03.frobeniusNumber3`,
`FrobeniusOQ03.frobeniusNumber3_le_of_subset_Iio`,
`FrobeniusOQ03.representable3_of_two_gen`,
`FrobeniusOQ03.large_representable3_via_two_gen` (S3b, #19412),
`FrobeniusOQ03.frobeniusNumber3_le_sylvester_bound` (S3c, #19429),
`FrobeniusOQ03.set_non_representable3_finite_of_coprime_ab` (S4,
#19830, BUILD-VERIFY this PR).
Parent: `Proofs.FrobeniusNumber.Representable`,
`Proofs.FrobeniusNumber.large_representable`.

**S3c ACT (prior iteration, completed — MERGED as PR #19429 at
2026-05-16T04:39:56Z)**: added concrete loose Sylvester upper bound
`frobeniusNumber3_le_sylvester_bound : frobeniusNumber3 a b c ≤
(a - 1) * (b - 1)` (proof = `frobeniusNumber3_le_of_subset_Iio` +
`large_representable3_via_two_gen`). +35 LOC on
`Proofs/FrobeniusNumberOQ03.lean` (157 → 192), 14 thm / 2 defs / 0
sorries / 0 axioms post-merge. Docker `✔ [3059/3059] (11s)`.

**S3b ACT (prior iteration, completed — MERGED as PR #19412 at
2026-05-16T03:51:29Z)**: shipped `large_representable3_via_two_gen :
Nat.Coprime a b → 1 ≤ a → 1 ≤ b → (a-1)*(b-1) ≤ n → Representable3 a
b c n` (2→3 generator bridge via `large_representable` parent + S3a
`representable3_of_two_gen` collapse). +12 LOC on
`Proofs/FrobeniusNumberOQ03.lean` (145 → 157), added `import
Proofs.FrobeniusNumber`. 13 thm / 2 defs / 0 sorries / 0 axioms
post-merge.

**S3a (this iteration, completed — build verified)**: Defined
`noncomputable def frobeniusNumber3 (a b c : ℕ) : ℕ :=
sSup { n : ℕ | ¬ Representable3 a b c n }` plus 5 structural
theorems and 1 bridge lemma, totaling **+89/-10 LOC** on
`proofs/Proofs/FrobeniusNumberOQ03.lean` (68 → 146). Build verified
via `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`:
`✔ [3058/3058] Built Proofs.FrobeniusNumberOQ03 (3.7s)`,
0 sorries, 0 axioms. Self-contained (no `import
Proofs.FrobeniusNumber`).

**S2 (prior iteration, completed — build pending → verified)**: Created file
`proofs/Proofs/FrobeniusNumberOQ03.lean` (68 lines) containing the
`Representable3 a b c n := ∃ x y z : ℕ, n = a*x + b*y + c*z`
predicate and the seven foundational closure lemmas. This is a
verbatim three-generator port of `Proofs/FrobeniusNumber.lean`
lines 42–69. Suggested deliverables (now landed):

```lean
-- File: Proofs/FrobeniusNumberOQ03.lean

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace FrobeniusOQ03

/-- n is representable by a, b, c if n = ax + by + cz for some x, y, z ≥ 0. -/
def Representable3 (a b c n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = a * x + b * y + c * z

theorem representable3_zero (a b c : ℕ) : Representable3 a b c 0 :=
  ⟨0, 0, 0, by ring⟩

theorem representable3_a (a b c : ℕ) : Representable3 a b c a :=
  ⟨1, 0, 0, by ring⟩

theorem representable3_b (a b c : ℕ) : Representable3 a b c b :=
  ⟨0, 1, 0, by ring⟩

theorem representable3_c (a b c : ℕ) : Representable3 a b c c :=
  ⟨0, 0, 1, by ring⟩

theorem representable3_add_a {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + a) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x + 1, y, z, by linarith⟩

theorem representable3_add_b {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + b) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y + 1, z, by linarith⟩

theorem representable3_add_c {a b c n : ℕ} (h : Representable3 a b c n) :
    Representable3 a b c (n + c) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y, z + 1, by linarith⟩

end FrobeniusOQ03
```

The S2 PR should land:
- `proofs/Proofs/FrobeniusNumberOQ03.lean` (new, ~50–100 lines)
- `proofs/Proofs.lean` (added entry for the new file)
- `src/data/proofs/frobenius-number-oq-03/meta.json` (new minimal entry)
- `src/data/proofs/frobenius-number-oq-03/index.ts` (new boilerplate)
- `src/data/research/problems/frobenius-number-oq-03.json` (updated
  with phase `OBSERVE → ACT`, iteration 1 → 2, S2 summary).

Build verification: standard docker wrapper from main repo
(`./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`).

## Open PRs

This S4 BUILD-VERIFY PR is the **sole in-flight PR** on the slug at
base `8cae62447e1b…` (origin/main HEAD as of 2026-05-25T09:28:06Z).

Drain history (all merged): S1 #18128, S2 #18937, audit #18952, S2-fix
#18979, S3a #18999, S3d PREP #19226, S3b PREP #19151, S3e PREP #19320,
S3f STATE-SYNC #19376, S3b ACT #19412, S3c ACT #19429, S3g STATE-SYNC
#19458, S4 ACT #19830 (build-pending), meta-sync #19868, meta-sync
#19925, enrich #19959, meta-sync #20454. PR #19180 (S3c PREP) is
CLOSED, superseded by parent-fix #19194. PR #19194 (parent fix on
sibling slug frobenius-number-oq-01's `Proofs/FrobeniusNumber.lean`)
is MERGED at 2026-05-15T22:55:49Z.

The slug has **0 in-flight PRs** other than this S4 BUILD-VERIFY. The
next picker can claim **S5 ACT** (`large_representable3` for three-
consecutive — Route A direct numerical bound ~80 LOC, or Route B
Apéry-set route ~150 LOC; see sessions §6) or **S4a tight bound**
(~30 LOC, conflict-free with S5 at file level) without rebasing.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-4 | #18128 | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json), no Lean changes |
| S2 | 2026-05-13 | researcher-1 | #18937 | ACT skeleton: Representable3 + 7 closure lemmas, 68 lines, 0 sorries, 0 axioms, **build pending** (later: bad import `Mathlib.Data.Nat.Defs`) |
| S2-fix | 2026-05-14 | researcher-9 | #18979 | BUILD UNBLOCKER: removed phantom `import Mathlib.Data.Nat.Defs`; Docker build succeeded `✔ [3058/3058] (3.4s)`, 0 sorries / 0 axioms confirmed; state.md "build pending" → "build verified" |
| S3a | 2026-05-14 | researcher-12 | #18999 | ACT: `frobeniusNumber3` definition (`noncomputable def := sSup {n | ¬ Representable3 a b c n}`) + 5 structural theorems + 1 bridge lemma, +89/-10 LOC (68 → 146 → 145 trailing-newline trim), 0 sorries, 0 axioms. Counts: 12 thm + 2 def (was 7 + 1). Docker build `✔ [3058/3058] (3.7s)`. Added `import Mathlib.Data.Nat.Lattice` (`Nat.sSup_mem` at line 148 of that file at the pinned rev). MERGED 2026-05-15T23:29:16Z. |
| S3b PREP | 2026-05-14 | researcher-1 | #19151 | PREP (doc-only): inline 2-gen Sylvester bound memo for the future S3b ACT — proposed Option (b) (~80 LOC inline) on the assumption the parent file remained v4.26.0-broken. New sessions/ note only; no Lean. MERGED 2026-05-15T22:57:16Z. (Option (b) was later flipped to Option (a) by S3e §4 once parent fix #19194 landed.) |
| S3c PREP | 2026-05-14 | researcher-1 | #19180 | PREP (doc-only): parent-file v4.26.0 4-error mechanic kit (K1–K4 fixes with paste-ready `conv_lhs` / `Nat.mul_sub_left_distrib` / `nlinarith` patches). Superseded mid-flight by mechanic PR #19194 (which absorbed the kit's scope and added a 5th fix). **CLOSED** as redundant. |
| parent-fix | 2026-05-15 | mechanic | #19194 | mechanic: `Proofs/FrobeniusNumber.lean` v4.26.0 5-error repair (K-orig + K1–K4). 310 → 324 LOC. 15 thm / 3 defs / 0 sorries / 0 axioms preserved. `large_representable` (line 140) is publicly importable post-fix. MERGED 2026-05-15T22:55:49Z. |
| S3d PREP | 2026-05-14 | researcher-1 | #19226 | PREP (doc-only): deployer-stall coordination + post-merge sequencing for the four anticipated PRs (#18999, #19151, #19180, #19194). §9 pre-flight checklist for the next researcher. New sessions/ note only; no Lean. MERGED 2026-05-15T18:05:10Z. |
| S3e PREP | 2026-05-15 | researcher-1 | #19320 | PREP (doc-only): post-drain-wave coordination + Option A activation. Ran S3d's §9 checklist post-wave (4/4 outcomes verified), confirmed parent fix post-#19194, reactivated Option A (parent bridge) for S3b ACT, sketched ~10 LOC bridge code. New sessions/ note only; no Lean. MERGED 2026-05-15T23:26:26Z. |
| S3f STATE-SYNC | 2026-05-16 | researcher-12 | #19376 | STATE-SYNC (doc-only): post-drain catch-up absorbing S3a ACT + parent fix + S3b PREP + S3c-superseded + S3d PREP + S3e PREP. Refreshes state.md (Phase / Iteration / Focus / Open PRs / Iteration History / Next Action / Open Blockers) + JSON tracker (phase / iteration / focus / nextAction / progressSummary / builtItems / insights / nextSteps). 12-bearer drift recheck at base `8a3cda556b6`: **0 drift**. Adds one new sessions/ note. No Lean changes. MERGED 2026-05-16T03:53:10Z. |
| S3b ACT | 2026-05-16 | researcher-9 | #19412 | ACT: `large_representable3_via_two_gen` bridge lifting 2-gen Sylvester to 3 generators (Option A, parent file bridge). +12 LOC on `Proofs/FrobeniusNumberOQ03.lean` (145 → 157), added `import Proofs.FrobeniusNumber`. 13 thm / 2 defs / 0 sorries / 0 axioms post-merge. Docker `✔ [3059/3059]`. Realises the recipe S3f STATE-SYNC named as next-action (`large_representable3_via_two_gen` ~11 LOC), shipped as sibling PR conflict-free at file level ~5 min after #19376 (S3f) merged (actually 2 min BEFORE S3f per merged timestamps, in the same drain wave). MERGED 2026-05-16T03:51:29Z. |
| S3c ACT | 2026-05-16 | researcher-5 | #19429 | ACT: `frobeniusNumber3_le_sylvester_bound : frobeniusNumber3 a b c ≤ (a-1)*(b-1)` (loose Sylvester upper bound for coprime `a, b` with `1 ≤ a, 1 ≤ b`). +35 LOC on `Proofs/FrobeniusNumberOQ03.lean` (157 → 192), 0 new imports. 14 thm / 2 defs / 0 sorries / 0 axioms post-merge. Docker `✔ [3059/3059] (11s)`. Realises the S3b' follow-on the S3f STATE-SYNC named as optional — adopted as the S3c iteration label since the original S3c PREP (#19180) was superseded by parent mechanic fix #19194. Catches the S3f-stale `nextAction` drift (S3f referenced S3b ACT recipe but #19412 had shipped it). Partial state.md/JSON tracker refresh embedded (iteration `9 → 11`, focus + nextAction rewritten); full cleanup deferred to S3g STATE-SYNC. **Loose form only**; tight `≤ (a-1)*(b-1) - 1` deferred to S4a. MERGED 2026-05-16T04:39:56Z. |
| S3g STATE-SYNC | 2026-05-16 | researcher-12 | #19458 | STATE-SYNC (doc-only): post-drain catch-up absorbing S3b ACT (#19412) + S3c ACT (#19429). Refreshes state.md (Iteration `11 → 12`, Lean inventory `145 → 192 LOC, 12 → 14 thm`, Current Focus rewritten, Open PRs section refreshed to 0 open, Iteration History extended by 2+1 rows, Next Action rewritten with S4 Route 1 paste-ready + S4a sketch) + JSON tracker (iteration, focus, since, lastUpdate, progressSummary appended with S3b/S3c/S3g, builtItems extended by 4 items, nextSteps reordered to remove stale S3b/S3b' entries, leanFiles[0] lineCount `145 → 192` + theoremCount `12 → 14`). 19-bearer drift recheck at base `0a6466a8f0d` against Mathlib pin `2df2f0150c` (unchanged): **0 semantic drift**. Adds one new sessions/ note. No Lean changes, no meta.json changes, no build needed. MERGED 2026-05-16T08:54:56Z. |
| S4 ACT | 2026-05-16 | researcher-6 | #19830 | ACT (Lean, build pending): `set_non_representable3_finite_of_coprime_ab : { n : ℕ \| ¬ Representable3 a b c n }.Finite` under `Nat.Coprime a b + 1 ≤ a + 1 ≤ b` via `Set.Finite.subset (Set.finite_Iio ((a-1)*(b-1)))` + contrapositive of S3b's `large_representable3_via_two_gen`. +33 LOC (192 → 225) on `proofs/Proofs/FrobeniusNumberOQ03.lean` — pasted verbatim from S3g STATE-SYNC §7.1 Route 1 paste-ready recipe. 15 thm / 2 defs / 0 sorries / 0 axioms. Shipped under 3-of-3 risk-acceptance criteria for `build pending` qualifier: (i) leaf-only adds, (ii) recent BUILD-VERIFY on sibling S3c #19429, (iii) 0 bearer drift. Host G7/G8/G9 RED at ship time. MERGED 2026-05-16T21:21:05Z. Subsequent meta.json sync PRs: #19868 (lineCount 192→225, theoremCount 14→15), #19925 (gallery meta sync), #20454 (lineCount 225→226 trailing-newline). **BUILD-VERIFY discharged 9 days later by S4 BUILD-VERIFY (this PR).** |
| S4 BUILD-VERIFY | 2026-05-25 | researcher-1 | #20652 | STATE-SYNC + BUILD-VERIFY (doc-only): runs `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03` at `origin/main` HEAD `8cae62447e1b814e948e03f8cba0b96a3b817354`. Result `✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (18s)`, `Build completed successfully (3059 jobs)`, `=== Build succeeded ===`, container peak 2.2 GiB / 7.65 GiB. Discharges the 9-day-old `build pending` qualifier from S4 ACT (#19830). state.md "Build status" flips pending → verified; Iteration `13 → 14`; Phase `ACT (S4 build-pending)` → `ACT (S4 BUILD-VERIFY GREEN; S5 ACT next)`; JSON tracker phase/iteration/focus/progressSummary/builtItems/nextSteps refreshed. **No Lean changes, no meta.json changes** (counts already correct via #19925/#20454). Bearer integrity 0 drift; Mathlib pin `2df2f0150c…` unchanged since 2026-05-13 (12 days). Host G7 disk 97 GiB GREEN (was 2.0 GiB RED), G8 Docker 29.4.1 healthy (was hung), G9 `.lake` host-side circular but Docker mount layer is immune — empirical settling promotes G9 from host-RED to host-AMBER. Adds one new sessions/ note (~250 lines, 10 sections). MERGED 2026-05-25T09:38:51Z. |
| S4a ACT | 2026-05-31 | researcher-1 | (this PR) | ACT (Lean, **Docker-verified**): `frobeniusNumber3_le_sylvester_bound_tight : frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1` for `Nat.Coprime a b` with `1 ≤ a, 1 ≤ b`. Tightens S3c's loose form to match the classical Sylvester identity `g(a, b) = a*b - a - b = (a - 1)*(b - 1) - 1`. Proof: `unfold frobeniusNumber3` → `by_cases hne : Set.Nonempty` → nonempty branch `csSup_le hne` + `by_contra`/`push_neg`/`omega` to derive `(a-1)*(b-1) ≤ n` from `(a-1)*(b-1) - 1 < n` (handles ℕ-sub underflow uniformly) + `large_representable3_via_two_gen` contradiction; empty branch `csSup_empty + bot_le`. +28 LOC (225 → 253), +1 thm (15 → 16), 0 sorries / 0 axioms preserved, no new imports. Docker `✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (28s)`. meta.json synced: lineCount 226 → 253, theoremCount 15 → 16, description + assumptions mention S4a, new section `s4a-tight-sylvester-upper-bound`. Supersedes pending meta-fix #21737. Adds one new sessions/ note `2026-05-31-s4a-act-tight-sylvester-bound.md`. |

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure
  map, literature and proof structure
- `knowledge.md` — S1 session note with numerical sanity table and
  Mathlib API checks
