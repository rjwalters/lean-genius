# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-03
**Iteration**: 19

## Current Focus

Proving `jdt_weight_sum` b ≥ 2 — via weight factorization (S18 correct approach).
Session 17 proved `jdt_weight_sum_b_one` (b=1 base case, ~95 lines).
Session 18 discovered the "violation element" bijection is NON-INJECTIVE for b≥2.
Session 19 fixed `rel_head` bug in b=1 proof; submitted Aristotle (ID: c6967eb8).
2 sorries remain in main file.

## Active Approach

**b≥2 correct approach** (Session 18 discovery):
- Key insight: `wt(P)*wt(Q) = ((P.1+Q.1).map X).prod` — weight depends only on total multiset M
- Strategy: group LHS sum by M; show #{non-cs (a,b) splits of M} = #{all (a+1,b-1) splits of M}
- The counting equality holds by a simple combinatorial bijection (move min of Q to P)
- This avoids the complex seam tracking that caused 17 sessions of failure

**ABANDONED**: "First violation element" bijection — NON-INJECTIVE for b≥2 (S18 counterexample)

Completed:
- `jdt_weight_sum_b_one` (S17): b=1 bijection, ~95-line proof, 0 remaining sorry
  - S19 fixed `rel_head` bug: `cases+pairwise_cons` replaces non-existent `Pairwise.rel_head`
- `not_colStrictSym_a_one_iff_qhead_le_phead` (S16)
- `colStrictSym_a_one_iff_phead_lt_qhead` (S16)
- `sym_one_sort_head_singleton` (S15)
- `jdt_weight_preserved` (S~9)

## Attempt Count
- Total attempts: 19 (sessions 1-19)
- Approaches tried:
  1. SSYT infrastructure (sessions 1-14)
  2. Decompose jdt_weight_sum (session 15)
  3. ColStrictSym b=1 characterisation (session 16)
  4. Prove jdt_weight_sum_b_one bijection (session 17) ✓
  5. Violation-element bijection for b≥2 (sessions 1-18) — ABANDONED (non-injective)
  6. Weight-factorization + ballot principle (session 18 → 19+) — CURRENT

## Blockers

None. Weight-factorization approach is combinatorially sound.
Remaining sorries:
- `jdt_weight_sum` b≥2 (line ~617): weight-factorization approach, ~100-150 lines
- `jacobi_trudi_ssyt_eq` k≥3 (line ~848): RSK/LGV, long-term open

## Next Action

1. Implement b≥2 via weight factorization:
   - Prove `wt(P)*wt(Q) = ((P.1+Q.1).map X).prod`
   - Group sum by total multiset M
   - Ballot bijection: #{non-cs (a,b) splits} = #{all (a+1,b-1) splits}
2. Aristotle (ID: c6967eb8) may solve companion file b=1 proof independently.
3. After b≥2 closes: `jacobi_trudi_ssyt_eq` k ≥ 3 (RSK/LGV).
