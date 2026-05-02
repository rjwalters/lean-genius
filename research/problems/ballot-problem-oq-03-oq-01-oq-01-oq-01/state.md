# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-03
**Iteration**: 20

## Current Focus

Proving `jdt_weight_sum` b ≥ 2 — the RSK/JDT bijection is the standard approach.
Session 17 proved `jdt_weight_sum_b_one` (b=1 base case, ~95 lines).
Session 18 discovered the "violation element" bijection is NON-INJECTIVE for b≥2.
Session 19 fixed `rel_head` bug in b=1 proof.
Session 20 integrated Aristotle proof into companion file (0 sorries remaining there).
1 sorry in main file (b≥2), 1 long-term sorry (jacobi_trudi_ssyt_eq k≥3).

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

b≥2 bijection is genuinely hard. Both "min-of-Q" and "violation-element" bijections
are non-injective. The correct bijection is RSK/JDT (standard but ~300-500 lines).
Remaining sorries:
- `jdt_weight_sum` b≥2 (line ~617): RSK or algebraic approach, ~300-500 lines
- `jacobi_trudi_ssyt_eq` k≥3 (line ~848): RSK/LGV, long-term open

Companion file: 0 sorries (Aristotle job 9ddf3174 proved b=1 standalone form).

## Next Action

1. Try b=2 special case first: for b=2, violation at i=0 or i=1, case-split (~50 lines).
2. Submit b≥2 sorry to Aristotle as standalone (fiber counting identity).
3. Investigate algebraic approach: h_a*h_b - h_{a+1}*h_{b-1} = ∑_{cs} wt via Mathlib ring lemmas.
4. After b≥2 closes: `jacobi_trudi_ssyt_eq` k ≥ 3 (RSK/LGV).
