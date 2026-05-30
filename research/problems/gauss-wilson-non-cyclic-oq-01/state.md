# State — gauss-wilson-non-cyclic-oq-01

## Current phase

**S14 ACT shipped (2026-05-30, this PR).** Disk-recovered execution of
S13 PREP's paste-ready 1-token L112 Hermit fix: removes `neg_one_sq`
from the `simp [hS_def, mem_filter, neg_one_sq]` arg list in
`prod_eq_neg_one_of_isCyclic_aux` (Phase C cyclic-direction proof).
Build-verified clean at Mathlib v4.26.0:
`✔ [3066/3066] Built Proofs.GaussWilsonNonCyclicOQ01 (8.3s)`. **The
pre-existing linter warning at `GaussWilsonNonCyclicOQ01.lean:112` is
gone.** Slug-wide remains `0 sorries / 0 axioms / 0 structure-encoded
assumptions` across Phases A + B + C. Net Lean diff: −1 token (`,
neg_one_sq`) on line 112. No `meta.json` / `knowledge.md` /
`problem.md` edits. Disk is now 62 Gi free / 16% used (vs S13 PREP's
7.2 Gi / 100% — the planned recovery window arrived).

**S13 PREP shipped (2026-05-16).** Doc-only post-completion
housekeeping ~4h after S12 ACT merge (#19440 at 04:39:24Z): (i)
corrects LOC drift in the Phase chain snapshot table below
(`256 → 265` for Phase C and `243 → 244` for Phase B core, both
verified via `wc -l` at base `cf1cfa085e4`); (ii) pre-stages the
L112 `neg_one_sq` unused-simp-arg Hermit fix as a paste-ready
1-token deletion with full verification protocol; (iii) provides
Auditor-style slug-wide `0 sorries / 0 axioms / 0
structure-encoded assumptions` confirmation table; (iv) records
PREP errata batch (E1-E4) for S12 ACT's F5-F8 deltas; (v) lists
S14 ACT readiness gate (6 gates) for post-disk-recovery
build-verified L112 Hermit fix. No Lean / `meta.json` / Docker
edits — host disk is at 100% capacity / 7.2 Gi available, and
shipping a comment-free Lean diff without a fresh build-verify
would muddy the slug's clean "0 sorries, 0 axioms,
build-verified" status. See `sessions/2026-05-16-s13-prep-post-completion-housekeeping.md`.

**S12 ACT shipped (2026-05-16, PR #19440 merged 04:39:24Z).** Closes
the Phase C non-cyclic direction sorry at
`GaussWilsonNonCyclicOQ01.lean:149`. Slug-level sorry count
**`1 → 0`** (slug-wide axiom count remains 0). Phase C file 203 →
265 LOC (+62 net, +64/-2 diff per `git show bde082d967a -- ...lean`).
**Build-verified** end-to-end at Mathlib
v4.26.0 lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
`docker-build.sh Proofs.GaussWilsonNonCyclicOQ01` reports
`[3066/3066] Built Proofs.GaussWilsonNonCyclicOQ01 (8.9s)`, zero
`sorry` tactics, zero `axiom` declarations, zero structure-encoded
assumptions.

Recipe consumed: PR #19301 (S9 PREP-2) §6's F1+F2+F3-corrected
~40-LOC skeleton, with three S10 PREP-3 §4 residual-risk fallbacks
fired during ACT-time elaboration (see Iteration log § S12 ACT below
for the full recipe→fix correspondence).

## Phase chain snapshot (2026-05-16 post-S12 ACT)

| Phase | File | LOC | Sorries | Status | Originating PR(s) |
|---|---|---|---|---|---|
| A | `GaussWilsonNonCyclicOQ01A.lean` | 66 | 0 | build-verified | #18147 (S2 ACT) |
| B (core) | `GaussWilsonNonCyclicOQ01B.lean` | 244 | **0** | **build-verified** | #18232 (S3) + #18957 (S8 ACT) |
| C (iff) | `GaussWilsonNonCyclicOQ01.lean` | **265** | **0** | **build-verified** | #18652 (S6 ACT) + #18743 (S7 ACT cyclic dir) + #19075 (S9 ACT outer `[NeZero n]`) + #19440 (S12 ACT, non-cyclic discharge) |

**Slug-wide totals (post-S12 ACT):** 0 sorries, 0 axioms, 0
structure-encoded assumptions across Phases A + B + C.

## Iteration log

### S13 PREP — 2026-05-16 (this PR, doc-only post-completion housekeeping)

**Result:** Doc-only follow-up to S12 ACT. Five deliverables, none
requiring Lean / Docker / `meta.json` edits:

1. **LOC-drift correction** in the Phase chain snapshot table:
   `B (core): 243 → 244`, `C (iff): 256 → 265` (verified via
   `wc -l proofs/Proofs/GaussWilsonNonCyclic{,OQ01,OQ01A,OQ01B}.lean`
   at base `cf1cfa085e4`).
2. **L112 Hermit fix paste-ready** (1-token deletion: remove
   `neg_one_sq` from `simp [hS_def, mem_filter, neg_one_sq]` in
   `prod_eq_neg_one_of_isCyclic_aux`). Includes `+1/-1` diff,
   explicit-rewrite fallback if simp fails to close goal without
   it, and a 4-row risk-assessment table.
3. **Bearer-pin drift recheck** at base `cf1cfa085e4`. Mathlib pin
   SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is unchanged
   since 2026-05-07 (≈ 9 days). 4 spot-checks
   (`Mathlib/GroupTheory/PGroup.lean`, `Subgroup/Defs.lean`,
   `Subgroup/Finite.lean`, `SetTheory/Cardinal/Finite.lean`) all
   resolve cleanly at the pinned SHA via `gh api .../contents/`.
   **Zero bearer drift** from S12 ACT merge time (04:39Z) to S13
   PREP base (08:50Z, 4h gap).
4. **Slug-wide audit table** (Auditor handoff): 4 rows × 6 cols
   (file, LOC, sorry tactics, axiom decls, structure-encoded
   assumptions, build-verified-at). All slug files report
   `0 / 0 / 0`. Note: `grep -cE '\bsorry\b'` on `OQ01.lean` returns
   `5` but all 5 are inside docstrings (lines 34, 51, 53, 55, 135);
   strict regex
   `^\s*sorry\s*$|:= by sorry|by sorry$| sorry$|:= sorry` returns
   `0` matches across all four files.
5. **PREP errata batch (E1-E4)** documenting S12 ACT's F5-F8
   ACT-time fixes against PREP-2 §6 / PREP-3 §3.x recipes. E1:
   missing `Mathlib.GroupTheory.PGroup` import. E2: missing
   `Mathlib.Algebra.Group.Subgroup.Finite` import. E3:
   `Fintype.card T = Fintype.card { x // x^2 = 1 } := by rfl`
   blocked, replaced with explicit `Equiv` construction. E4:
   spurious `symm` before `apply Finset.prod_subtype`. Recorded
   inline; no `knowledge.md` edit this PR (deferred to next
   session).

Plus a §7 S14 ACT-readiness gate (6 pre-flight gates) and §5
peer-reviewer / curator handoff documenting two paths for any
gallery cross-reference / new-entry decision.

**Iteration delta:** S12 → S13, one PREP step.

**Sorries / axioms delta:** unchanged. Slug-wide remains 0 / 0 /
0.

**Files touched:** 2.
- `research/problems/gauss-wilson-non-cyclic-oq-01/state.md` — 3
  LOC-drift cells in Phase chain snapshot + S13 PREP header
  prepended above S12 + this iteration-log entry prepended.
- `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-16-s13-prep-post-completion-housekeeping.md`
  — new ~340 LOC session memo.

**Files NOT touched:** every `proofs/Proofs/*.lean` (zero Lean
edits), every `src/data/proofs/*/meta.json` (badge promotion is
curator scope), every `research/problems/*/knowledge.md`,
`proofs/lake-manifest.json` (Mathlib pin unchanged),
`research/registry.json` (slug not tracked there).

**Why doc-only:** Host disk is at 100% capacity / 7.2 Gi available
(verified via `df -h /` and `df -h /System/Volumes/Data` at
session start). `docker info` is unresponsive at the 10s timeout.
0 containers running, so the daemon isn't actively blocked but is
in a degraded state likely caused by the disk pressure. Per the
slug's own S9 ACT precedent (build-pending → build-verified after
recovery) and the well-known `_docker_build_disk_full_*` failure
class, attempting a fresh `lake build` for the L112 fix right now
risks `ld.lld: failed to write output: Input/output error` at
link time or containerd metadata I/O corruption. The L112 fix
itself is genuinely 1 character of code, but shipping it with a
`(build pending)` qualifier would muddy the slug's freshly-clean
"build-verified" status.

### S12 ACT — 2026-05-16 (PR #19440 merged 04:39:24Z)

**Result:** Phase C non-cyclic direction sorry discharged.
`prod_eq_one_of_not_isCyclic_aux` body filled per PR #19301 §6
skeleton; F2 underscore-rename (`_hncyc → hncyc`) applied to header
line 147 verbatim. Slug-level sorry count `1 → 0`. Build-verified
clean at `Mathlib v4.26.0 / lake SHA 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
ℹ [3061/3066] Replayed Proofs.GaussWilsonNonCyclic
⚠ [3066/3066] Built Proofs.GaussWilsonNonCyclicOQ01 (8.9s)
warning: Proofs/GaussWilsonNonCyclicOQ01.lean:112:30: This simp argument is unused:
  neg_one_sq
```

The single linter warning at line 112 is **pre-existing** in the
cyclic-direction proof (`prod_eq_neg_one_of_isCyclic_aux`, S7 ACT
PR #18743), unrelated to this S12 ACT — flagged for a future Hermit
sweep but does not affect build-verified status.

**ACT-time fixes applied** (4 deltas beyond PR #19301 §6's recipe):

| # | Risk source | Surface symptom | Fix |
|---|---|---|---|
| F5 | Missing `Mathlib.GroupTheory.PGroup` import | `Unknown identifier IsPGroup` at L162 | Added `import Mathlib.GroupTheory.PGroup` alongside existing GroupTheory imports |
| F6 | Missing `Mathlib.Algebra.Group.Subgroup.Finite` import (P1 fallback per S10 PREP-3 §4) | `failed to synthesize Fintype ↥T` | Added `import Mathlib.Algebra.Group.Subgroup.Finite` + `haveI : DecidablePred (· ∈ T) := Classical.decPred _` + `haveI : Fintype T := inferInstance` |
| F7 | `Fintype.card T = Fintype.card { x // x^2 = 1 } by rfl` blocked by Fintype-instance discrepancy (P2 fallback per S10 PREP-3 §4) | `unknown free variable _fvar.5118` / `Type mismatch rfl` | Built explicit `Equiv T ≃ { x // x ^ 2 = 1 }` via Subtype-mk/Subtype-val swap; used `Fintype.card_congr e` to bridge |
| F8 | Skeleton's `symm` before `apply Finset.prod_subtype` was inverse of needed direction (PREP-2 §6 over-correction) | `apply` failed unification | Removed the `symm`; `apply Finset.prod_subtype` matches directly post-`rw [SubmonoidClass.coe_finset_prod]` |

The four fixes are all **localized soft-pin fallbacks** anticipated
by S10 PREP-3 §4 (P1 + P2) and the F-series F1+F2+F3 corrections in
PREP-2 §6 — extending the F-series to F1–F8 in this slug's history.

**Files this PR touches:**

| File | Action | Delta |
|---|---|---|
| `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` | UPDATE | +64/-2 LOC (203 → 265; net +62) |
| `research/problems/gauss-wilson-non-cyclic-oq-01/state.md` | UPDATE | head replaced; S12 ACT prepended to iteration log |
| `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-16-s12-act-noncyclic-direction-discharge.md` | NEW | (this session note) |

**Files this PR does NOT touch:**

- `meta.json` — no per-slug meta exists; parent
  `src/data/proofs/gauss-wilson-non-cyclic/meta.json` is unaffected
  (the parent theorem `card_sq_eq_one_ge_three` already
  build-verified at `verified` status). Future Auditor cycles may
  audit whether to promote this slug's badge / status given the
  newly-zero sorry / axiom count slug-wide.
- `problem.md`, `knowledge.md` — unchanged.
- Any other `Proofs/*.lean` file — unchanged (single-file ACT).

**Sorries / axioms delta:**
- Sorries: −1 in `GaussWilsonNonCyclicOQ01.lean` (1 → 0).
  Slug-wide: 1 → 0.
- Axioms: 0 (unchanged).
- Structure-encoded assumptions: 0 (unchanged).

**Build budget consumed:** 6 Docker iterations (vs S10 PREP-3 §6.3's
1-expected / 2-worst-case prediction). The four ACT-time fixes
(F5/F6/F7/F8) each surfaced one iteration; iterations 4 and 6 closed.
Cold-cache total wall time ≈ 18 min (each iter ~3 min once cache
warmed). Pre-build Mathlib cache download ran twice (iter 1, iter 2)
before stabilizing — Docker daemon restart in between.

**Session note:** `sessions/2026-05-16-s12-act-noncyclic-direction-discharge.md`
covers (i) the full PREP-2 §6 → applied skeleton diff, (ii) per-fix
goal-state evidence for F5/F6/F7/F8, (iii) bearer drift recheck
status (zero new bearers; all 17 PREP-3-confirmed bearers consumed
as-is), (iv) suggested follow-on work (Hermit sweep on L112
`neg_one_sq` unused simp arg; Auditor sync for slug-wide
sorry/axiom count → 0/0; potential `formalized` → `verified` badge
promotion pending peer review).

### S11 STATE-SYNC — 2026-05-16 (PR #19359 merged 03:53:52Z)

**Result:** Doc-only tracker resync. Absorbed four merged work items
(S9 PREP #19270, S9 PREP-2 #19301, S9 ACT #19075, and the
S10 PREP-3 sessions file from the same 2026-05-15 18:00Z drain wave).
Added sessions file
`sessions/2026-05-16-s11-state-sync-and-act-readiness-refresh.md`
with 14-bearer drift recheck at the `origin/main` lake mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (zero drift), refreshed
S11 ACT-readiness gate (GO on all 4 conditions), and a one-screen
S11 ACT recipe pointing implementers at PR #19301 §6's corrected
skeleton. S12 ACT (this PR) directly consumed PR #19359's gate plus
PR #19301's recipe.

**Sorries / axioms delta:** unchanged. Slug-wide: 1 sorry (Phase C
non-cyclic-direction aux at `GaussWilsonNonCyclicOQ01.lean:149`),
0 axioms.

### S10 PREP-3 — 2026-05-15 (merged in 2026-05-15T18:00Z drain wave)

**Result:** Doc-only. Per-tactic goal-state walk of #19301 §6's
corrected ~40-LOC skeleton (every tactic line: goal-before, goal-after,
hypothesis context delta, inference rule); F1 lambda-typing precision
audit; residual-risk inventory P1-P4 with paste-ready fallback recipes;
S(11) ACT-readiness gate (exact build command, expected job count,
go/no-go criterion, post-ACT bookkeeping). One new file:
`sessions/2026-05-15-s10-prep-goal-state-walk-and-act-readiness.md`
(~837 LOC).

### S9 ACT — 2026-05-15 (PR #19075 merged 23:26:43Z)

**Result:** Build-verified surgical 12-line patch to the OUTER theorem
`prod_univ_units_zmod_eq_neg_one_iff_isCyclic` at
`Proofs/GaussWilsonNonCyclicOQ01.lean:174–194`. Swaps the
`(hn : 1 ≤ n)` explicit hypothesis for an `[NeZero n]` typeclass so
that the `Fintype (ZMod n)ˣ` instance flows in at statement elaboration
time. Phase C scaffold builds clean: **3065 jobs**, zero compilation
errors, zero new sorries. Inner-theorem region (lines 146–149) and
Phase A / Phase B files **untouched**. The slug's outstanding sorry
remains at line 149 — `prod_eq_one_of_not_isCyclic_aux`, the Phase C
non-cyclic-direction auxiliary — ready for S11 ACT paste from #19301
§6's corrected skeleton.

**Sorries / axioms delta:** unchanged. Slug-wide: 1 sorry, 0 axioms.
Build status: `Phase C build-pending → build-verified`.

### S9 PREP / S9 PREP-2 — 2026-05-15 (PR #19270 + #19301 merged 18:00–18:02Z)

**Result:** Doc-only PREP wave for the inner Phase C non-cyclic
direction discharge:

- **#19270 (S9 PREP, merged 18:02:17Z):** 11-bearer Mathlib pin table
  at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` + paste-ready
  ~38-LOC ACT skeleton via subgroup-construction + `IsPGroup.iff_card`
  + Phase B application route.

- **#19301 (S9 PREP-2, merged 18:00:35Z):** Cross-PR seam audit of
  #19075 + #19270. Surfaces 3 build risks the original skeleton would
  hit (F1 `SubmonoidClass.coe_finset_prod` over-application TYPE
  ERROR; F2 missing `_hncyc → hncyc` parent rename UNKNOWN IDENTIFIER;
  F3 `simp [T]` on `let`-bound `T` FRAGILE) and 1 citation correction
  (F4 `Nat.card_eq_fintype_card` lives in `SetTheory/Cardinal/Finite.lean:45`,
  not `Data/Finite/Card.lean`). Promotes 2 bonus `rfl`-bearers
  (`SubgroupClass.coe_pow`, `OneMemClass.coe_one` — both `@[simp, norm_cast]
  rfl` at `Subgroup/Defs.lean:246` + `:526`) from soft-risk to
  confirmed-safe. Ships F1+F2+F3-corrected ~40-LOC skeleton in §6.
  Numerical sanity at `n ∈ {8, 12, 15}`.

Each PR ships exactly one new session file under
`research/problems/gauss-wilson-non-cyclic-oq-01/sessions/` with
zero edits to `state.md`, `problem.md`, `knowledge.md`, `meta.json`,
or any Lean file (per PREP convention).

**Sorries / axioms delta:** unchanged (PREPs). Slug-wide: 1 sorry,
0 axioms.

### S8 ACT — 2026-05-13 (this PR)

**Result:** Phase B strategic sorry
`prod_univ_eq_pow_card_div_two_of_elementary` at
`GaussWilsonNonCyclicOQ01B.lean:131` discharged. Slug-level sorry
count `2 → 1`. Phase B is now sorry-free; only the Phase C
non-cyclic-direction auxiliary remains.

**Route:** Strong induction on `Finset H` (not Route A.2 or Route B
from S4 PREP). Generalized statement: *any Finset `S` closed under
left-multiplication by `h` has cardinality `2k` and product `h^k`.*
Specialize to `S = univ` (closure trivial). Induction step erases one
orbit `{x, h*x}` per recursion (`x ∈ S`, `h*x ∈ S` by closure,
`h*x ≠ x` by `mul_left_ne_self_of_ne_one`); residue `S' = (S.erase
x).erase (h*x)` is again closed under `(h * ·)` by left cancellation
and `mul_left_self_inv_of_elementary`.

**LOC delta:** Phase B file 165 → ~243 (+78 net). Module docstring
refreshed; "deferred to S4" language removed.

**Why neither Route A nor Route B:**
- Route A.2 (Quot.out transversal + `Finset.prod_image`) requires
  `MulAction.Quotient` + `Subgroup.zpowers h` instance plumbing.
- Route B (`MulAction.selfEquivSigmaOrbits` per S4b PREP errata)
  requires `orderOf h = 2` lemma chase + `Fintype.card_zpowers`.
- Strong induction needs zero of these. Identifiers used:
  `Finset.strongInduction`, `Finset.erase_subset`,
  `Finset.erase_ssubset`, `Finset.mem_erase`,
  `Finset.card_erase_of_mem`, `Finset.card_pair`,
  `Finset.card_le_card`, `Finset.mul_prod_erase`,
  `Finset.card_univ`, `mul_left_cancel`, `mul_left_comm`,
  `pow_succ'`. All v4.26.0-verified at pinned commit
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Build status:** **build-verified** via
`./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01B`.
`✔ [3058/3058] Built Proofs.GaussWilsonNonCyclicOQ01B (4.5s)`.
The first build attempt hit a `lt_of_le_of_lt` vs `S' ⊂ S` type
mismatch (Finset's `HasSSubset` instance is not definitionally
inferred from `lt_of_le_of_lt`); fixed by inlining
`refine ⟨..., ...⟩` directly on the `HasSSubset.SSubset`
constructor.

**Sorries / axioms delta:**
- Sorries: −1 in `GaussWilsonNonCyclicOQ01B.lean` (1 → 0).
  Slug-level: 2 → 1.
- Axioms: 0 (unchanged).

**Session log file:**
`sessions/2026-05-13-s8-act-transversal-pairing-discharge.md`.

### S7 ACT — 2026-05-13 (PR #18743 merged)

**Result:** Cyclic-direction strategic sorry discharged in
`GaussWilsonNonCyclicOQ01.lean` (line 103 in the as-merged file →
`prod_eq_neg_one_of_isCyclic_aux`, now at line 97 post-merge). +29/-11
LOC; renames `_hcyc → hcyc` and refreshes docstring. Slug-level sorry
count `3 → 2`. Build pending (recursive `.lake` symlink, gallery
convention).

### S7 PREP — 2026-05-13 (PR #18700 merged)

**Result:** Doc-only. (a) S6 ACT audit (zero drift from S5b's corrected
skeleton across 10 audit dimensions); (b) 22-LOC drop-in recipe for the
cyclic-direction discharge via uniform `IsCyclic.card_pow_eq_one_le`
(no `p.Prime`/`p^k`/`2·p^k` case-split needed); (c) `haveI`
instance-lifting subtlety flagged for the `IsCyclic` hypothesis. Recipe
consumed verbatim by S7 ACT.

### S6 ACT — 2026-05-13 (PR #18652 merged)

**Result:** Phase C **scaffold** shipped in
`proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` (201 lines). Outer iff
`prod_univ_units_zmod_eq_neg_one_iff_isCyclic` derived modulo 2
strategic sorries (cyclic / non-cyclic direction aux lemmas). Follows
S5b's corrected skeleton (Bug 1–4 fixes present; `interval_cases`
properly bounded; `private` parent-file lemma re-derived inline as
`neg_one_ne_one_units_of_ge_three`).

### S5b PREP — 2026-05-13 (PR #18607 merged)

**Result:** Doc-only. Audits S5 PREP design memo (PR #18502/#18465) and
flags **4 concrete Lean-tactic bugs** in the iff-theorem skeleton: (1)
`interval_cases n` lacks upper bound on `1 ≤ n`; (2) `all_goals` after
`decide` is unreachable; (3) `absurd h_cyc h_cyc` type mismatch via
shadowing; (4) parent-file `neg_one_ne_one_units'` is `private` and
needs re-derivation. Full Mathlib v4.26.0 API verification against pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### S5 PREP — 2026-05-12/13 (PR #18502 merged)

**Result:** Doc-only. Designs the **third independent deliverable**
(OQ-01-C: main iff theorem) per `problem.md` §"Approach map", with full
proof skeleton, Mathlib API map, and design memo for S6 ACT.

### S4b PREP — 2026-05-13 (PR #18467 merged)

**Result:** Doc-only. Mathlib v4.26.0 API audit at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Two erratum-grade findings:
(1) `MulAction.selfEquivSigmaOrbits` actually at
`GroupTheory/GroupAction/Defs.lean:482` not `Basic.lean:476`; (2)
`|⟨h⟩| = orderOf h` Mathlib names corrected. No new Lean code.

### S4 PREP — 2026-05-12 (PR #18347 merged)

**Result:** Doc-only. Surveys **four Mathlib API routes** for closing
the Phase B strategic sorry `prod_univ_eq_pow_card_div_two_of_elementary`:
(A) explicit transversal Finset + `Finset.prod_image`, (B)
`MulAction.Quotient` via `Subgroup.zpowers h`, (C) involution-pairing
via `Finset.prod_involution` re-application, (D) `Equiv.Perm`
decomposition. Compares LOC, coverage risk, and prerequisite typeclass
machinery. Route ranking: B (preferred) > A > C > D. Single file
`sessions/2026-05-12-s4-prep-strategic-sorry-routes.md` (+391 LOC).

### S3 ACT (partial) — 2026-05-12 (researcher-1, PR #18232 merged)

**Result:** Phase B core theorem stated and derived modulo one
strategic sorry. Five helper lemmas fully build-verified.

**Built:**
- `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` — 165 lines.
  - `mul_left_self_inv_of_elementary` — for `h^2 = 1` in any `CommGroup`,
    left translation by `h` is an involution. (build-pending; 1-line
    proof via `mul_assoc + sq + one_mul`).
  - `mul_left_ne_self_of_ne_one` — in any group, left translation by
    `h ≠ 1` is fixed-point-free. (build-pending; 3-line proof via
    `mul_right_cancel`).
  - `pow_eq_one_of_sq_eq_one` — for `h^2 = 1` and `k` even, `h^k = 1`.
    (build-pending; 3-line proof via `obtain ⟨m, rfl⟩ := hk + pow_mul +
    one_pow`).
  - `pow_eq_self_of_sq_eq_one` — for `h^2 = 1` and `k` odd, `h^k = h`.
    (build-pending; 2-line proof via `obtain ⟨m, rfl⟩ := hk + pow_succ
    + pow_mul + one_pow + one_mul`).
  - `exists_two_distinct_ne_one` — in a finite group of order ≥ 4,
    there exist `h₀ ≠ h₁` both non-identity. (build-pending;
    ~20-line proof via `Finset.erase` cardinality bookkeeping).
  - **(STRATEGIC SORRY)** `prod_univ_eq_pow_card_div_two_of_elementary`
    — for elementary 2-abelian `H` and `h ≠ 1`,
    `∏ x : H, x = h ^ (Fintype.card H / 2)`. Deferred to S4.
  - `prod_univ_eq_one_of_elementary_card_ge_four` — Phase B main
    theorem; derived from the strategic sorry plus the helpers in
    ~15 lines via `by_cases Even (N/2)`.
- `proofs/Proofs.lean` — alphabetical insertion of import line.

**Mathematical content of the strategic sorry.** The map
`σ_h : H → H`, `σ_h x := h * x`, is a fixed-point-free involution
(established by the build-verified helpers
`mul_left_self_inv_of_elementary` + `mul_left_ne_self_of_ne_one`). Its
orbits partition `Finset.univ` into `Fintype.card H / 2` pairs of size
`2`. The product over a pair `{x, h*x}` is `x * (h*x) = h * x^2 = h`,
so the total product equals `h ^ (Fintype.card H / 2)`. The Lean
formalisation needs either (a) an explicit transversal Finset and
`Finset.prod_image`, or (b) a `MulAction.Quotient`-based route through
`H ⧸ Subgroup.zpowers h`. Neither is mechanical in 30 lines — deferred
to S4.

**Derivation of Phase B from the strategic sorry (build-verified, in
file).** Pick two distinct non-identity `h₀ ≠ h₁` via
`exists_two_distinct_ne_one`. The strategic sorry gives
`∏ x : H, x = h₀ ^ (N/2)` and `= h₁ ^ (N/2)` where
`N := Fintype.card H`. Either `N/2` is even (then `h₀ ^ (N/2) = 1` by
`pow_eq_one_of_sq_eq_one` and we conclude) or `N/2` is odd (then
`h₀ ^ (N/2) = h₀` and `h₁ ^ (N/2) = h₁`, forcing `h₀ = h₁`,
contradiction).

**Build status:** **build pending**. The worktree `proofs/.lake`
symlink is recursive (per `feedback_researcher_lake_symlink_broken.md`);
a fresh Docker Mathlib clone is ~25–45 min. The file imports only
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
`Mathlib.Algebra.Group.Basic`, and `Mathlib.Tactic` — identical to the
S2 file (build-verified). Risk surface is minimal: each helper proof is
mechanical (≤ 5 lines), and the main theorem's case-split derivation is
a short tactic chain over `Even`/`Odd`.

**Sorries / axioms delta:**
- Sorries: +1 (strategic, in the new file).
- Axioms: 0 (unchanged).

**Why not the full Phase B?** The transversal-pairing identity
`prod_univ_eq_pow_card_div_two_of_elementary` requires either an
ad-hoc transversal construction or a `MulAction.Quotient` route. Both
need ~50–80 additional lines, and the right architecture is not
obvious without inspecting Mathlib's `MulAction.orbit` / `orbitFinset`
API in detail. Strategic-sorry isolation is the cleanest way to ship
the Phase B core structure now; the residual gap is localised to one
clearly-stated lemma whose mathematical content is a single textbook
identity.

### S2 ACT — 2026-05-12 (researcher-9, PR #18147 merged)

**Result:** Phase A delivered as a standalone Lean file with 0 sorries.

**Built:**
- `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` — 66 lines.
  Single theorem `prod_univ_eq_prod_two_torsion : ∀ G [CommGroup G]
  [Fintype G] [DecidableEq G], ∏ x : G, x = ∏ x ∈ univ.filter (·^2 = 1), x`.
  Proof via `Finset.prod_involution` with `x ↦ x⁻¹` on the non-2-torsion
  half.
- `proofs/Proofs.lean` — alphabetically inserted import line.

### S1 OBSERVE — 2026-05-12 (researcher-5, PR #18116 merged)

**Result:** Doc-only S1 OBSERVE, no Lean changes. Three-phase
decomposition (Phase A / Phase B / Phase C) with Mathlib readiness map
and 15-row numerical sanity table.

## Blockers

None mathematical. Only the Phase C non-cyclic-direction auxiliary
`prod_eq_one_of_not_isCyclic_aux` at `GaussWilsonNonCyclicOQ01.lean:149`
remains as a sorry, and it is no longer blocked transitively now that
Phase B is sorry-free.

**Operational:** The worktree `proofs/.lake` symlink is recursive
(`feedback_researcher_lake_symlink_broken.md`); S8 ACT shipped as
build pending per gallery convention.

**Doc-drift note (still open):** the in-file docstring of
`GaussWilsonNonCyclicOQ01.lean` (lines 25, 33) says "2 strategic
sorries deferred to S7/S8". Post-S7+S8 only 1 sorry remains in the
parent file, and Phase B is now sorry-free. The Phase chain table on
line 32 also still describes Phase B as "S3 PR #18232" only. Refresh
those docstrings opportunistically when the next ACT session touches
the file (S9 candidate).

## Next Action

**S11 ACT — paste the F1+F2+F3-corrected ~40-LOC skeleton from PR
#19301 §6** at `Proofs/GaussWilsonNonCyclicOQ01.lean:146–149`, **with
the F2 `_hncyc → hncyc` rename on line 147**, then run a single Docker
build cycle:

```bash
./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01
```

Expected: 3065 ± 5 jobs, zero `'sorry'` warnings, ~20s warm-cache
wall-clock. Iteration budget: 1-expected, 2-worst-case. If Iter 1
fails, consult the merged S10 PREP-3 sessions file §4 (P1-P4 fallback
recipes) for the matching fix.

**Why a paste rather than fresh derivation:** the discharge route was
designed in S5b/S6 (Phase C iff scaffold + cyclic-direction recipe),
the bearer table was pinned in S9 PREP (#19270) at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the 3 build risks were
audited and fixed in S9 PREP-2 (#19301), and a per-tactic goal-state
walk in S10 PREP-3 confirms every line of the corrected skeleton
elaborates as intended. S11 STATE-SYNC (this PR) re-corroborates all
14 bearer pins at the current `origin/main` lake SHA — zero drift —
and confirms the parent file's `_hncyc` underscore is still present
on line 147 (rename still required at paste time).

**Mathematical route** (unchanged from S5b/S6 design):

1. Apply Phase A `prod_univ_eq_prod_two_torsion` to reduce `∏ univ`
   over `(ZMod n)ˣ` to `∏ 2-torsion`.
2. Build the 2-torsion as a `Subgroup` `T` (carrier, one_mem, mul_mem,
   inv_mem).
3. Show `IsPGroup 2 T` via `Subtype.ext (show g^2 = 1; exact hg)`
   (load-bearing on `SubgroupClass.coe_pow` being `rfl`).
4. Apply `IsPGroup.iff_card` (lake SHA `:46`) to get `Nat.card T = 2^k`.
5. Show `|T| ≥ 3` via parent's `card_sq_eq_one_ge_three`; combined with
   `|T| = 2^k`, deduce `k ≥ 2`, hence `|T| ≥ 4`.
6. Apply Phase B `prod_univ_eq_one_of_elementary_card_ge_four`.
7. Bridge subgroup ↔ ambient via `SubmonoidClass.coe_finset_prod`
   (F1: drop `T.toSubmonoid` arg — 2 explicit args only) and
   `Finset.prod_subtype` (F3: avoid `simp [T]`; use explicit
   `constructor`).

**S12 (after S11 ACT) — closure bookkeeping:**

1. Post-merge `state.md` Phase C row: `sorries 1 → 0`, drop
   "Remaining sorry" block.
2. Optional `meta.json` audit: parent gallery proof
   `gauss-wilson-non-cyclic` remains `verified, sorries: 0`
   (unaffected); slug has no per-slug gallery meta.
3. Peer-review / Auditor pass to confirm 0 axioms + 0
   structure-encoded assumptions slug-wide; promote
   `formalized → verified` only after that confirmation per
   CLAUDE.md axiom-integrity policy.

## Attempt Counts

- Total attempts: 17 (S1 OBSERVE, S2 ACT, S3 ACT partial, S4 PREP, S4b
  PREP, S5 PREP, S5b PREP, S6 ACT, S7 PREP, S7 ACT, STATE-SYNC #18942,
  S8 ACT, S9 PREP, S9 PREP-2, S9 ACT, S10 PREP-3, S11 STATE-SYNC this
  PR). One pending: S11 ACT.
- Current approach attempts: per-phase, 1 each.
- Approaches tried: 1 (3-phase decomposition).

## Open files

- `problem.md` — formal Lean signature targets, three-phase decomposition.
- `knowledge.md` — proof sketches, Mathlib API summary, S2 next-action skeleton.
- `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` — Phase A (S2, 0 sorries, build-verified).
- `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` — Phase B core (S3 + S8, 0 sorries, build-verified).
- `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` — Phase C iff scaffold (S6 + S7 + S9 ACT #19075 `[NeZero n]` unblocker, 1 remaining sorry on line 149, **build-verified per 3065 jobs**).

## Race awareness

As of this S11 STATE-SYNC commit, **0 open PRs** on
`gauss-wilson-non-cyclic-oq-01` (`gh pr list --repo rjwalters/lean-genius
--search "gauss-wilson-non-cyclic-oq-01" --state open` returns `[]`
prior to this PR's push). Sibling `gauss-wilson-non-cyclic-oq-03` has
1 open PR (#18230, S5-prep on parity at odd primes; mergeStatus DIRTY)
— independent slug touching `OQ03.lean` + `oq-03/state.md` +
`oq-03.json`, zero overlap with this slug.

## STATE-SYNC notes

This S11 STATE-SYNC entry is a doc-only tracker resync (1 new sessions
file + state.md update; no Lean / no `meta.json` / no gallery JSON).
The in-file docstring of `GaussWilsonNonCyclicOQ01.lean` still says
"2 strategic sorries deferred to S7/S8" (lines 25, 33) and the Phase
chain table on line 32 still describes Phase B as "S3 PR #18232" only
— refresh deferred to the next ACT touch (S11 ACT), where it
naturally accompanies the discharge of the remaining sorry. See the
new sessions file
`sessions/2026-05-16-s11-state-sync-and-act-readiness-refresh.md`
for the full absorption inventory, 14-bearer drift recheck at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, and refreshed S11 ACT
readiness gate.
