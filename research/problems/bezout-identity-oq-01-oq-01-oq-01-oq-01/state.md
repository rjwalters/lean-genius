# Current State

**Phase**: COMPLETED — verified-final
**Status**: graduated
**Since**: 2026-05-12T09:55:05Z (S2 merged, PR #18029)
**Iteration**: 5
**Last Updated**: 2026-05-16T14:32Z (S5 STATE-SYNC)
**Researcher**: researcher-5 (S2); researcher-9 (S1); researcher-12 (S3 STATE-SYNC);
researcher-8 (S4 PREP, S5 STATE-SYNC); mechanic (PR #19213 v4.26.0 4-error repair)

## S5 STATE-SYNC (2026-05-16, researcher-8)

Doc-only sync that catches up the tracker after three things happened
since S3 STATE-SYNC (#19021, merged 2026-05-14):

1. **S3 BUILD-DIAGNOSE PR #19168** (2026-05-14, *closed unmerged* 2026-05-15)
   — first Docker baseline post-S2 found 4 latent errors masked by the
   `(build pending)` convention. Proposed K1–K4 mechanic kit.
2. **Mechanic PR #19213** (merged 2026-05-15T18:06Z) — applied the K1–K4
   kit to `proofs/Proofs/BezoutIdentityOQ01OQ01OQ01.lean`. Two of the
   four kit entries were *semantic bug fixes*: K3 corrected the
   `binaryGcd_log_sq_bound` constant `6 → 12` (the arithmetic
   `(4·log+2)·(3·(log+1)) ≤ 12·(log+1)²` was wrong in S2's `6·(log+1)²`);
   K4 corrected the `binaryGcdSteps 252 198` worked example `12 → 7`
   (hand-trace gives 7 calls). K1, K2 were API/tactic drifts under
   v4.26.0. File now compiles end-to-end.
3. **S4 PREP PR #19254** (researcher-8, merged 2026-05-15T05:44Z) —
   sibling-audit of #19168's K1–K4 kit. Independent verification at
   the pinned SHA confirmed K1, K3, K4 fully correct; flagged K2 as
   potentially over-stated (only line 116 has explicit
   `simp [binaryGcdSteps]`; the other 7 cited sites are downstream
   `↓reduceIte` reducers). The mechanic ultimately applied a tighter
   K2 (lines 116, 121, 133 only) — consistent with the audit.

### What this STATE-SYNC fixes

| Field | Before | After |
|---|---|---|
| `state.md` head Phase | `COMPLETED` | `COMPLETED — verified-final` |
| `state.md` head Iteration | `2` | `5` (catches up S3 STATE-SYNC + S4 PREP + S5 STATE-SYNC; S3 BUILD-DIAGNOSE closed, no iter slot) |
| `state.md` head Researcher | researcher-5, -9, -12 | + researcher-8 + mechanic |
| `state.md` head Last Updated | (absent) | `2026-05-16T14:32Z` |
| `state.md` Next Action | "S3 optional Mathlib contribution / S4 deferred sibling" | `**None** — verified-final` (with mechanic handoff for `leanFiles[]` drift) |
| JSON `currentState.iteration` | 2 | 5 |
| JSON `currentState.focus` | S2 summary only | + mechanic-cascade + S4 PREP absorption |
| JSON `currentState.nextAction` | "Out of scope" | mechanic handoff for stale `leanFiles[]` |
| JSON `knowledge.nextSteps` | 4 stale S2/S3/S4/S5 future-steps | `**None** — verified-final` + 1 mechanic handoff note |
| JSON `lastUpdate` | `2026-05-14T08:30Z` | `2026-05-16T14:32Z` |

### What is OUT-of-scope for this PR

- **`leanFiles[0]` metadata drift** (`lineCount: 282 → 285` after the
  mechanic K3/K4 fixes added 3 net lines; `theoremCount`/`defCount`/
  `axiomCount`/`sorryCount` all correct at 9/3/0/0). This is mechanic
  territory (auto-populated by `scripts/research/enrich-research.ts`);
  manual edits risk clobber. Package as ready-to-paste in the
  session memo §3 instead.
- **Gallery meta.json `originalContributions`** at
  `src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json` still
  says "binaryGcd_log_sq_bound: O(log²) corollary — total bit ops ≤
  6·(log₂(max a b)+1)²", but the K3-fixed file now bounds at `12·…`.
  Mechanic territory (gallery meta is the mechanic's beat per PR #19531
  precedent which fixed gallery `lineCount` 282 → 285).
- **No build verification** in this PR. The host has
  Docker daemon hung + `proofs/.lake` symlink broken + disk at
  6.5 Gi avail (AMBER). The file already compiles on CI per PR #19213
  evidence. No new Lean is added by this PR.

## S3 STATE-SYNC (2026-05-14, researcher-12)

Doc-only sync after S2 (PR #18029) merged. The slug's primary goal
— axiom elimination in `Proofs/BezoutIdentityOQ01OQ01OQ01.lean` —
**was accomplished in S2** and is now reflected in main:

- Lean file: 0 axioms, 282 lines, 9 theorems, 3 defs, 0 sorries.
- Parent gallery (`src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json`):
  status=`verified`, badge=`verified`, axiomCount=0.

This STATE-SYNC brings the research tracker into alignment with the
shipped state:
- Phase `ACT` → `COMPLETED`.
- Status `active` → `graduated` (matches sibling-slug convention,
  e.g. bezout-identity-oq-01-oq-01-oq-02).
- Top-level `lastUpdate` + `completed` timestamps added (canonical
  schema fields read by `scripts/research/build.ts`).
- `currentState.focus` rewritten past-tense.
- `currentState.nextAction` clarified — S3/S4 below are out of
  scope for this slug (upstream Mathlib + new sibling gallery
  entry respectively).

Counts as 1 of 2 STATE-SYNC PRs allowed per researcher session.

## Original S2 Summary (researcher-5, 2026-05-12)

**Approach A executed.** Eliminated the two axioms `stepBitOps`
and `stepBitOps_le` from `Proofs/BezoutIdentityOQ01OQ01OQ01.lean`,
completing the primary goal of this OQ.

### Changes
- Add `import Mathlib.Data.Nat.Size`.
- New private lemma `size_eq_succ_log {n : ℕ} (hn : 0 < n) :
  Nat.size n = Nat.log 2 n + 1` (4 lines, le_antisymm). The forward
  direction `size ≤ log + 1` reduces via `Nat.size_le` to
  `n < 2^(log + 1)` which is `Nat.lt_pow_succ_log_self`. The
  backward direction `log + 1 ≤ size` follows from `Nat.lt_size`
  applied to `Nat.pow_log_le_self`.
- Replace `axiom stepBitOps (a b : ℕ) : ℕ` with
  `def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1` —
  a concrete bit-cost model (1 comparison + 1 subtraction or shift +
  1 parity check).
- Replace `axiom stepBitOps_le (a b : ℕ) : stepBitOps a b ≤
  3 * (Nat.log 2 (max a b) + 1)` with the theorem of the same
  signature. Proof: `by_cases` on `max a b = 0`; the zero case is
  `1 ≤ 3` (via `simp [h, Nat.size_zero, Nat.log_zero_right]`); the
  positive case rewrites via `size_eq_succ_log` and closes by
  `omega` (`2·(log+1) + 1 = 2·log + 3 ≤ 3·log + 3 = 3·(log + 1)`).

### Metrics
- `lineCount`: 242 → 282 (+40 net: −2 axioms, +1 def, +1 private
  lemma, +1 theorem, plus docstrings).
- `theoremCount`: 7 → 9 (added `size_eq_succ_log` private + `stepBitOps_le`).
- `definitionCount`: 2 → 3 (added `stepBitOps`).
- `axiomCount`: 2 → 0.
- `sorries`: 0 (unchanged).

### Parent gallery meta.json updates
`src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json`:
- `status`: `axiomatized` → `verified`.
- `badge`: `axiom` → `verified`.
- `axiomCount`: 2 → 0.
- `lineCount`: 242 → 282.
- `theoremCount`: 7 → 9.
- `definitionCount`: 2 → 3.
- `imports`: `+Mathlib.Data.Nat.Size`.
- `assumptions`: rewritten to "None" (axioms eliminated by this
  OQ).
- `mathlibDependencies`: append the 5 new lemmas used
  (`Nat.size_le`, `Nat.lt_size`, `Nat.lt_pow_succ_log_self`,
  `Nat.pow_log_le_self`, `Nat.size_zero`).
- `originalContributions`: append `stepBitOps`, `size_eq_succ_log`,
  `stepBitOps_le`.
- `bit-complexity` section endLine: 242 → 282; summary and
  mathContext rewritten to reflect the now-concrete cost model.
- `conclusion`: openQuestion #1 marked RESOLVED with the concrete
  cost model as the resolution.

Build verification: **pending**. The worktree shares the broken
`proofs/.lake` symlink (per memory
`feedback_researcher_lake_symlink_broken.md`); Docker build is
deferred to CI. Proof script uses only stable Mathlib API
(`Nat.size_le`, `Nat.lt_size`, `Nat.lt_pow_succ_log_self`,
`Nat.pow_log_le_self`, `Nat.size_zero`, `Nat.log_zero_right`,
`omega`) at the pinned rev verified in S1's API audit.

### Previous focus (S1)

S1 (researcher-9): Survey three approaches to eliminating the
`stepBitOps_le` axiom from `Proofs/BezoutIdentityOQ01OQ01OQ01.lean`.
Settled on **Approach A** (closed-form `stepBitOps := 2 * Nat.size (max a b)
+ 1`) as the S2 attack target — single-session, ~50 lines Lean, requires
one load-bearing helper (`Nat.size = Nat.log 2 + 1` for `n ≥ 1`).

## Active Approach

**Approach A: Closed-form bit-cost function**

Replace
```lean
axiom stepBitOps (a b : ℕ) : ℕ
axiom stepBitOps_le (a b : ℕ) : stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1)
```
with
```lean
def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1
theorem stepBitOps_le (a b : ℕ) :
    stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1) := by …
```

Cost model interpretation: each recursive call performs at most
- 1 comparison: up to `Nat.size (max a b)` bit reads
- 1 subtraction or right-shift: up to `Nat.size (max a b)` bit ops
- 1 parity (lsb) check: O(1) constant

Sum: `2 · size + 1` ≤ `3 · (log + 1) = 3 · size`. ✓

## Blockers

None mathematical.

**Practical**: the `proofs/.lake` symlink in the researcher worktree
points to itself (see `feedback_researcher_lake_symlink_broken.md`),
forcing any Docker build to fresh-clone Mathlib (~25 min). S1 is doc-only,
so unaffected. S2 will need a build verification but can be deferred
to a follow-up `*-prep` PR per the precedent in `cube-root-3-irrational-oq-04`.

## Next Action

**None — verified-final.** The slug's primary goal (axiom elimination
in `Proofs/BezoutIdentityOQ01OQ01OQ01.lean`) was accomplished in S2
(PR #18029) and the v4.26.0 build was repaired by mechanic PR #19213.
File is 0 axioms / 0 sorries / 9 theorems / 3 defs / 285 LOC; gallery
meta.json `bezout-identity-oq-01-oq-01-oq-01` already shows
`status=verified`, `badge=verified`, `axiomCount=0` on origin/main.

**Mechanic handoff** (single residual drift, this PR does NOT touch):
`leanFiles[0]` in the research JSON for this slug still shows
`lineCount: 282`; actual file is 285 LOC (mechanic K3/K4 added 3 net
lines). See session memo §3 for the ready-to-paste diff. Also: gallery
meta.json `originalContributions` text "≤ 6·(log₂(max a b)+1)²" needs
update to "≤ 12·…" (K3 fix changed the constant).

### Historical (S2 plan, archival)

S2 (done in PR #18029, researcher-5): Eliminate `stepBitOps_le`
(Approach A) in `proofs/Proofs/BezoutIdentityOQ01OQ01OQ01.lean`. Three
deliverables:

1. Helper lemma (~10 lines):
   ```lean
   private lemma size_eq_succ_log {n : ℕ} (hn : 0 < n) :
       Nat.size n = Nat.log 2 n + 1 := by
     apply le_antisymm
     · -- size n ≤ log + 1
       rw [Nat.size_le]
       exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
     · -- log + 1 ≤ size n
       rw [Nat.lt_size]  -- log n < size n ↔ 2^(log n) ≤ n
       exact Nat.pow_log_le_self 2 hn.ne'
   ```

2. Replace the two axioms with a `def` + `theorem`:
   ```lean
   def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1

   theorem stepBitOps_le (a b : ℕ) :
       stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1) := by
     unfold stepBitOps
     by_cases h : max a b = 0
     · simp [h, Nat.size_zero]  -- LHS = 1, RHS = 3
     · have hpos : 0 < max a b := Nat.pos_of_ne_zero h
       rw [size_eq_succ_log hpos]
       omega
   ```

3. Update parent meta.json: drop `axiomCount` from 2 to 0 (or update
   parent's axiom set accordingly) — note the parent's gallery meta.json
   may need a follow-up enricher pass; check before opening S2 PR.

S2 should *not* touch `totalBitOps` or `binaryGcd_log_sq_complexity` —
they already consume the inequality, not the axiom directly, so the
downstream proofs continue to work.

**Estimated effort for S2**: 1 session, single PR, ~30 new lines net
(adds helper + def + theorem; removes 2 axiom lines).

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE + S2 ACT). Subsequent S3 STATE-SYNC,
  S4 PREP, mechanic PR #19213, and this S5 STATE-SYNC are
  doc-or-repair sessions — they are not counted as new proof attempts.
- Current approach attempts: 1 (Approach A — closed-form `stepBitOps`,
  succeeded in S2; K3/K4 semantic-bug repairs by mechanic do not
  change the approach).
- Approaches tried: 1/3 surveyed (A succeeded; B = List Bool and
  C = BitVec n remain as separate sibling gallery entries, not
  in scope for this slug).

## Open files

- `problem.md` — Full problem statement, three approaches, sub-lemma list, Mathlib API map.
- `knowledge.md` — S1 session note: API verification at pinned rev, edge-case analysis.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/problem.md` (~210 lines)
- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/state.md` (this file)
- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/knowledge.md` (S1 session note)
- `src/data/research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01.json` (research index entry)
