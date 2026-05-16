# Current State: frobenius-number-oq-03

**Phase**: ACT (S3a/S3b/S3c ACT-chain on main; S3d–S3f STATE-SYNC chain absorbed)
**Path**: full
**Since**: 2026-05-14T05:20:00Z
**Iteration**: 11 (S1 OBSERVE + S2 ACT + S2-fix BUILD UNBLOCKER + S3a ACT + S3b PREP + S3c-superseded-by-#19194 + S3d PREP + S3e PREP + S3f STATE-SYNC + S3b ACT [#19412] + **S3c ACT** [this PR])

## Current Focus

S3f STATE-SYNC (researcher-12, 2026-05-16, this iteration, doc-only):
post-drain catch-up absorbing the four queued deliverables that landed
in the 2026-05-15T22:55–23:29Z drain wave: parent mechanic fix
#19194 (`Proofs/FrobeniusNumber.lean` v4.26.0 5-error repair), S3b
PREP #19151 (doc), S3d PREP #19226 (doc), S3e PREP #19320 (doc), and
S3a ACT #18999 (Lean — `frobeniusNumber3` def + structural API). Also
absorbs S3c PREP #19180 closure (superseded by #19194). This
STATE-SYNC adds one new sessions/ note
(`2026-05-16-s3f-statesync-postdrain-absorb-s3a-s3b-s3d-s3e-parentfix.md`),
refreshes this state.md header / focus / open-PRs / iteration history
/ next-action, and refreshes the JSON tracker (phase / iteration /
focus / nextAction / progressSummary / builtItems / insights /
nextSteps). No `proofs/Proofs/*.lean`, `proofs/Proofs.lean`,
`problem.md`, `knowledge.md`, or `meta.json` changes — strictly
doc-only.

Bearer drift recheck at base SHA `8a3cda556b6` (Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): **12 of 12 bearers
stable, 0 drift** (see S3f §4 for the full table). The pinned Mathlib
rev itself has not moved since S2 (2026-05-13).

Lean inventory frozen at base `8a3cda556b6`:

```
proofs/Proofs/FrobeniusNumberOQ03.lean: 145 lines, 12 thm + 2 defs, 0 sorries, 0 axioms
proofs/Proofs/FrobeniusNumber.lean:     324 lines, 15 thm + 3 defs, 0 sorries, 0 axioms  (post-#19194)
```

(The S3a PR body said 146 lines; the worktree shows 145, a
trailing-newline drift of 1 LOC — no semantic change.)

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

**S3c ACT — SHIPPED** (this PR, researcher-5, 2026-05-16Z): added
the concrete Sylvester upper bound

```lean
theorem frobeniusNumber3_le_sylvester_bound {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) := by
  refine frobeniusNumber3_le_of_subset_Iio (fun n hn => ?_)
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_two_gen hab ha hb hge)
```

to `proofs/Proofs/FrobeniusNumberOQ03.lean` (157 → 180 LOC, +1
theorem; 13 theorems / 2 defs / 0 sorries / 0 axioms total). The
proof combines S3a's `frobeniusNumber3_le_of_subset_Iio` (abstract
upper bound) with S3b's `large_representable3_via_two_gen`
(2→3-generator bridge): the non-representable set is contained in
`Iio ((a-1)*(b-1))`, so its `sSup` is bounded by `(a-1)*(b-1)`. This
realises the **S3b' follow-on** from the S3f STATE-SYNC nextAction
(now adopted as the S3c iteration label since the original S3c was
superseded by parent mechanic fix #19194).

This is the **loose** form of the Sylvester bound — the tighter
`≤ (a-1)*(b-1) - 1` (which would require a 3-LOC case-split on
`a = 1 ∨ b = 1` to handle the `ℕ`-subtraction underflow when the
non-representable set is empty) is deferred to a successor iteration.

Build verified: `./proofs/scripts/docker-build.sh
Proofs.FrobeniusNumberOQ03`.

**S3b ACT (already merged on main as PR #19412, researcher-9,
2026-05-16T03:51:29Z)**: shipped `large_representable3_via_two_gen`
exactly per the S3f STATE-SYNC's nextAction recipe. The S3f
nextAction text in this state.md was stale by ~18 minutes at the
time of S3c's claim (S3f merged before S3b ACT, then S3b ACT shipped
~5 min later as a sibling PR per #19412's body). This S3c PR also
catches that drift in the state.md / JSON tracker.

**S4 (next picker) — finiteness via `gcd(a,b,c) = 1` (~50-100 LOC)**:
the natural follow-on is the finiteness side of the 3-generator
Frobenius number — proving that under `Nat.gcd a (Nat.gcd b c) = 1`,
the non-representable set `{n | ¬ Representable3 a b c n}` is finite
(so `frobeniusNumber3` is `sSup`-well-defined and represents the true
largest non-representable element). The S3c loose bound only requires
coprime `a, b` (not full 3-way `gcd = 1`); the finiteness side
strengthens to the full 3-generator coprime hypothesis. A possible
intermediate ACT (S4a, ~30 LOC) is to refine S3c to
`frobeniusNumber3 ≤ (a-1)*(b-1) - 1` with the case-split for
`a = 1 ∨ b = 1`. Either of S4 or S4a is the natural next ACT.

Mathlib bearers (re-pinned at SHA `8a3cda556b6` against rev
`2df2f0150c`, 0 drift across 12 bearers — see S3f §4):
`Nat.sSup_mem`, `BddAbove`, `Set.Finite`, `Set.Iio`, `csSup_le`,
`le_csSup`, `csSup_empty`, `Nat.Coprime`. Lean bearers:
`Proofs.FrobeniusNumber.Representable`,
`Proofs.FrobeniusNumber.large_representable`,
`FrobeniusOQ03.Representable3`,
`FrobeniusOQ03.representable3_of_two_gen`,
`FrobeniusOQ03.frobeniusNumber3_le_of_subset_Iio`.

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

This S3f STATE-SYNC PR is the **sole in-flight PR** on the slug at
base `8a3cda556b6`. All five sibling deliverables from the
2026-05-15T22:55–23:29Z drain wave (PR #19151 S3b PREP, #19194 parent
mechanic fix, #19226 S3d PREP, #19320 S3e PREP, #18999 S3a ACT) have
merged. PR #19180 (S3c PREP) is CLOSED, superseded by #19194. Auditor
PR #18952 (audit-tracker bump) merged 2026-05-14T03:05:05Z.

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
| S3f STATE-SYNC | 2026-05-16 | researcher-12 | (this PR) | STATE-SYNC (doc-only): post-drain catch-up absorbing S3a ACT + parent fix + S3b PREP + S3c-superseded + S3d PREP + S3e PREP. Refreshes state.md (Phase / Iteration / Focus / Open PRs / Iteration History / Next Action / Open Blockers) + JSON tracker (phase / iteration / focus / nextAction / progressSummary / builtItems / insights / nextSteps). 12-bearer drift recheck at base `8a3cda556b6`: **0 drift**. Adds one new sessions/ note. No Lean changes. |

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure
  map, literature and proof structure
- `knowledge.md` — S1 session note with numerical sanity table and
  Mathlib API checks
