# Current State

**Phase**: ACT
**Since**: 2026-06-04T22:25:00Z
**Iteration**: 3

## Current Focus

Extending axiom-free k=3 coverage. After this session, the conjecture is proved
for k=1 (fully), k=2 (fully), and k=3 at n ∈ {0, 1, 2, 3}. Open: k=3 for n ≥ 4
(small-m cases) and k ≥ 4 entirely (except the general large-m bound, axiomatized
via Thue–Siegel for the finiteness).

## Active Approach

**Brute-force bounded enumeration** for k=3 small-n cases. The pattern:

```
theorem erdos677_k3_at_n (m : ℕ) (hm : n+3 ≤ m) : lcmInterval m 3 ≠ lcmInterval n 3 := by
  intro heq
  have h0 : lcmInterval n 3 = V := by native_decide   -- V = computed target value
  have hge : m + 3 ≤ lcmInterval m 3 := le_lcmInterval m 3 (by omega)
  rw [heq, h0] at hge                                 -- hge : m + 3 ≤ V, so m ≤ V-3
  have hm_le : m ≤ V - 3 := by omega
  interval_cases m <;> revert heq <;> native_decide   -- one native_decide per m
```

This works whenever the case count `V - 3 - (n + 3 - 1)` is reasonable (≤ ~60).
At n=2,3: V=60, ~52 cases. At n=4: V=210, ~200 cases — approaching the practical
ceiling of `interval_cases` + `native_decide`. Beyond n=4, a sharper lower bound
is needed.

## Recent Progress (Session 2, 2026-05-13)

- Added `erdos677_k3_at_two` (m ≥ 5, V=60, 53 cases).
- Added `erdos677_k3_at_three` (m ≥ 6, V=60, 52 cases).
- Documented `lcmInterval_two_three_collision`: M(2,3) = M(3,3) = 60 is a
  *near-miss* the constraint m ≥ n+k exactly excludes.
- Updated meta: theoremCount 28 → 31, lineCount 313 → 353.

## Blockers

- k=3 for n ≥ 4 needs a sharper lower bound. The simple `n+k ≤ lcmInterval n k`
  bound produces ~200+ cases at n=4.
- k ≥ 4 cases entirely open (modulo the axiomatic Thue–Siegel finiteness).

## Next Action

Three plausible directions, in increasing difficulty:

1. **Sharper lower bound for k=3**: Prove `lcmInterval n 3 ≥ (n+1)(n+2)(n+3)/2`
   for all n. This follows from gcd structure: when n is odd, n+1 and n+3 share
   exactly a factor of 2; when n is even, the factors are pairwise coprime. With
   this bound, `m+3 ≤ lcmInterval m 3` would force `(m+1)(m+2)(m+3)/2 ≤ V`, which
   has a much smaller solution set in m.
2. **Closed-form for `lcmInterval n 3`**: With the sharper bound, derive an exact
   formula and extend the k=3 resolution to all n.
3. **k=4 small-n cases**: Apply the same brute-force pattern at k=4.

## Attempt Counts

- Total attempts: 2 (sessions: 1 = scaffolding + k=1/k=2/factorization; 2 = k=3 at n=2,3)
- Current approach attempts: 1 (brute-force bounded enumeration; succeeded for n ∈ {2, 3})
- Approaches tried: 2 (axiom-free direct algebra for k ≤ 2; brute-force for small-n k=3)

## Sessions

### S3 (2026-06-04) — STATE-SYNC
- **Decision**: STATE-SYNC. The on-disk file is at 353 lines / 31 theorems / 1 axiom / 0 sorries; the JSON `leanFiles[0]` was 242 / 23 / 1 / 0 — significantly under-counted (lineCount and theoremCount both stale from before Session 2's k=3 additions). The JSON `currentState.phase` was NEW with focus "Initial exploration" while `state.md` and `knowledge.progressSummary` correctly reflected ACT-phase substantial progress. Also `knowledge.mathlibGaps` and `knowledge.nextSteps` were empty despite the rich `insights` array spelling out the closed-form k=3 lower-bound plan.
- **JSON delta**: leanFiles.lineCount 242→353, theoremCount 23→31. currentState.phase NEW→ACT, iteration 2→3, focus rewritten, nextAction populated. knowledge.mathlibGaps populated with one entry (no `lcm` of interval API). knowledge.nextSteps populated with four concrete planned steps (closed-form lcmInterval n 3, sharper bound application, Bertrand asymptotic, explicit DO-NOT for thue_siegel_finiteness elimination).
- **No code change**. No axiom/sorry deltas.
