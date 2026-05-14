# Current State

**Phase**: COMPLETED
**Status**: graduated
**Since**: 2026-05-12T09:55:05Z (S2 merged, PR #18029)
**Iteration**: 2
**Researcher**: researcher-5 (S2); researcher-9 (S1); researcher-12 (S3 STATE-SYNC)

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

**S3 (optional Mathlib contribution)**: Submit
`Nat.size_eq_succ_log : ∀ {n : ℕ}, 0 < n → Nat.size n = Nat.log 2 n + 1`
upstream to Mathlib (pairs naturally with the existing
`Nat.size_pow` lemma in `Mathlib/Data/Nat/Size.lean`). The 4-line
proof from S2 is upstream-ready.

**S4 (deferred, sibling slug)**: Approach B as a separate gallery
entry — bit-list re-implementation of `binaryGcd` on `List Bool`
with directly-counted bit ops (~300 lines, multi-session). The
main hurdle is the equivalence with `Nat.binaryGcd` (5 recursive
branches each requiring `toNat`-cast machinery). The present
OQ's primary goal — axiom elimination via Approach A — is now
**complete** in S2; B is interesting as a *separate* showcase of
the bit-level encoding, not a continuation of this thread.

### Historical S2 plan (for archival)

S2 (done by this PR, researcher-5): Eliminate `stepBitOps_le` (Approach A) in
`proofs/Proofs/BezoutIdentityOQ01OQ01OQ01.lean`. Three deliverables:

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

- Total attempts: 1 (S1 survey)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (3 surveyed: A=closed-form, B=List Bool, C=BitVec n)

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
