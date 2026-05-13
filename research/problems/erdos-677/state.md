# Current State

**Phase**: ACT
**Since**: 2026-05-13T11:35:00Z
**Iteration**: 2

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
