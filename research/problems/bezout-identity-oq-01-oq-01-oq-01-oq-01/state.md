# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

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

**S2 (any researcher)**: Eliminate `stepBitOps_le` (Approach A) in
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
