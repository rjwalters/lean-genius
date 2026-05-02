# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-02
**Iteration**: 15

## Current Focus

Proving `jdt_weight_sum_b_one` — the `b = 1` base case of `jdt_weight_sum`,
extracted as a focused subproblem in Session 15.

## Active Approach

Build the bijection
`ψ : { (P, Q) : Sym (Fin n) a × Sym (Fin n) 1 // ¬ColStrictSym a 1 P Q } ≃ Sym (Fin n) (a+1)`:
- forward: `(P, Q, _) ↦ q ::ₛ P`, where `q` is the unique element of `Q`
- inverse: `S ↦ ((S.erase qS hS, ⟨{qS}, _⟩), _)`, where `qS = (S.1.sort)[0]`

Helper `sym_one_sort_head_singleton` (proved Session 15) extracts `q` cleanly.
Estimated 100-130 lines for the full bijection.

## Attempt Count
- Total attempts: 15 (sessions 1-15)
- Current approach attempts: 1 (jdt_weight_sum_b_one decomposition, Session 15)
- Approaches tried:
  1. SSYT infrastructure approach (sessions 1-14): defined `SSYTFin`, proved
     k=0, k=1, k=2 (modulo `jdt_weight_sum`); `jdt_weight_sum` b ≥ 1 was stuck.
  2. Decompose `jdt_weight_sum` b ≥ 1 (session 15): split into b=1 helper +
     b ≥ 2 sorry. b=1 is now focused.

## Blockers

- Pre-existing build failure in `BallotProblemOQ03OQ02.lean` (upstream dependency)
  may prevent Docker build verification. Not caused by our changes.

## Next Action

1. Implement the bijection in `jdt_weight_sum_b_one` (the sorry at line ~426).
   Use `sym_one_sort_head_singleton` for the Q-side decomposition.
2. After b=1 closes: tackle `jdt_weight_sum` b ≥ 2 (the seam algorithm,
   ~150-200 lines).
3. After `jdt_weight_sum` closes: `jacobi_trudi_ssyt_eq` k=2 is proved
   (only k ≥ 3 RSK/LGV remains).
