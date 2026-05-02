# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-02
**Iteration**: 16

## Current Focus

Proving `jdt_weight_sum_b_one` — the `b = 1` base case of `jdt_weight_sum`.
Session 16 added two characterisation helpers; the residual bijection
construction is the only remaining sub-task.

## Active Approach

Build the bijection
`ψ : { (P, Q) : Sym (Fin n) a × Sym (Fin n) 1 // ¬ColStrictSym a 1 P Q } ≃ Sym (Fin n) (a+1)`:
- forward: `(P, Q, _) ↦ q ::ₛ P`, where `q` is the unique element of `Q`
- inverse: `S ↦ ((S.erase qS hS, ⟨{qS}, _⟩), _)`, where `qS = (S.1.sort)[0]`

Helpers in place:
- `sym_one_sort_head_singleton` (S15): extracts `q` from `Q : Sym (Fin n) 1`
- `colStrictSym_a_one_iff_phead_lt_qhead` (S16): characterises ColStrictSym
  at b=1 as a single inequality `(P.sort)[0] < (Q.sort)[0]`
- `not_colStrictSym_a_one_iff_qhead_le_phead` (S16): negation form
  `q ≤ (P.sort)[0]` ready for direct use in the bijection

Estimated 80-100 lines for the residual bijection (down from 100-130 with
the characterisation in hand).

## Attempt Count
- Total attempts: 16 (sessions 1-16)
- Current approach attempts: 2 (jdt_weight_sum_b_one decomposition,
  Session 15 + characterisation helpers, Session 16)
- Approaches tried:
  1. SSYT infrastructure approach (sessions 1-14): defined `SSYTFin`, proved
     k=0, k=1, k=2 (modulo `jdt_weight_sum`); `jdt_weight_sum` b ≥ 1 was stuck.
  2. Decompose `jdt_weight_sum` b ≥ 1 (session 15): split into b=1 helper +
     b ≥ 2 sorry. b=1 is now focused.
  3. Characterise ColStrictSym at b=1 (session 16): two helpers reduce the
     subtype predicate to a single inequality, simplifying the bijection.

## Blockers

- Docker daemon hung during S16 (other agent's `BinaryGcdOQ03OQ02` build
  has been running since 04:57 AM, apparently stuck). Build verification
  deferred to CI.

## Next Action

1. Implement the bijection in `jdt_weight_sum_b_one` (the sorry at
   line ~466). Use `Sym.oneEquiv` to convert Q to Fin n, then the
   characterisation helpers, then the cons/erase chain.
2. Alternative: submit `BallotProblemOQ03OQ01OQ01OQ01Aristotle.lean`
   to Aristotle now that the characterisation helpers are in place.
3. After b=1 closes: tackle `jdt_weight_sum` b ≥ 2 (the seam algorithm,
   ~150-200 lines).
4. After `jdt_weight_sum` closes: `jacobi_trudi_ssyt_eq` k=2 is proved
   (only k ≥ 3 RSK/LGV remains).
