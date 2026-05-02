# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-02
**Iteration**: 17

## Current Focus

Proving `jdt_weight_sum` b ≥ 2 — the general JDT seam bijection.
Session 17 proved `jdt_weight_sum_b_one` (the b=1 base case). 2 sorries remain.

## Active Approach

The next target is `jdt_weight_sum` b ≥ 2:
- Forward: find first violation column c (min j with P.sort[j] ≥ Q.sort[j]),
  let v = Q.sort[c]; return (Sym.cons v P, Sym.erase Q v h)
- Inverse: find the "seam" element in P'.sort (the unique element that came
  from Q), move it back to form Q'
- Weight preserved: `jdt_weight_preserved` already proved this

Completed:
- `jdt_weight_sum_b_one` (S17): b=1 bijection, 75-line proof, 0 remaining sorry
- `not_colStrictSym_a_one_iff_qhead_le_phead` (S16)
- `colStrictSym_a_one_iff_phead_lt_qhead` (S16)
- `sym_one_sort_head_singleton` (S15)
- `jdt_weight_preserved` (S~9)

## Attempt Count
- Total attempts: 17 (sessions 1-17)
- Approaches tried:
  1. SSYT infrastructure (sessions 1-14)
  2. Decompose jdt_weight_sum (session 15)
  3. ColStrictSym b=1 characterisation (session 16)
  4. Prove jdt_weight_sum_b_one bijection (session 17) ✓

## Blockers

None for current approach. b≥2 seam bijection is intricate (~150-200 lines)
but well-understood combinatorially.

## Next Action

1. Implement `jdt_weight_sum` b ≥ 2 seam bijection.
2. Alternative: submit jdt_weight_sum b≥2 sorry to Aristotle.
3. After jdt_weight_sum closes: `jacobi_trudi_ssyt_eq` k ≥ 3 (RSK/LGV).
