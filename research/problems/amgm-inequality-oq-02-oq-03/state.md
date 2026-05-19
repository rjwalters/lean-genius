# Current State

**Phase**: COMPLETED
**Since**: 2026-03-28T06:36:47.429Z (per `research/registry.json`)
**Iteration**: 2 (S2 STATE-SYNC, 2026-05-17)

## Outcome

Sub-OQ `amgm-inequality-oq-02-oq-03` — "Can the Maclaurin step
$M_k \geq M_{k+1}$ be derived from Newton's log-concavity, eliminating
the `maclaurin_step` axiom from the parent file?" — is **proved**.

The file `proofs/Proofs/AmgmInequalityOQ02OQ03.lean` carries out the
classical Hardy-Littlewood-Pólya §2.22 derivation:

1. Define $a_k = e_k / \binom{n}{k}$ (normElemSymm).
2. Newton's log-concavity gives $a_k^2 \geq a_{k-1} a_{k+1}$.
3. By induction, $a_k^{k+1} \geq a_{k+1}^k$ (power_inequality).
4. By rpow monotonicity, $M_k = a_k^{1/k} \geq a_{k+1}^{1/(k+1)} = M_{k+1}$
   (maclaurin_step_from_newton, maclaurin_step_proved).

The `newton_log_concavity` axiom is **inherited** from
`AmgmInequalityOQ02.lean`; this file does not introduce new `axiom`
declarations. The `maclaurin_step` axiom that previously sat in
`AmgmInequalityOQ02.lean` is eliminated by this file.

## Lean Source

`proofs/Proofs/AmgmInequalityOQ02OQ03.lean` — 226 LOC, 6 theorems,
1 definition (normElemSymm), 0 `axiom` declarations in this file
(one inherited from parent), 0 sorries.

| Field | Value |
|---|---|
| `axiom` declarations in this file | 0 |
| Inherited axioms (parent) | 1 (`newton_log_concavity`) |
| Structure-encoded assumptions | 0 |
| Tactic `sorry` | 0 |
| Definition `sorry` | 0 |

Gallery `src/data/proofs/amgm-inequality-oq-02-oq-03/meta.json` records
`status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 1` (the inherited
assumption, per the project's axiom integrity policy), `sorries: 0`, and
now (post this S2) `theoremCount: 6`, `definitionCount: 1` matching the
Lean source. Prior `theoremCount: 7` over-counted by +1.

## Theorem Inventory

1. `normElemSymm_zero` — $a_0 = 1$
2. `normElemSymm_nonneg` — non-negativity of normalized symmetric polys
3. `newton_lc` — Newton's log-concavity in $a_k$ form (uses parent axiom)
4. `power_inequality` — $a_k^{k+1} \geq a_{k+1}^k$
5. `maclaurin_step_from_newton` — main result (continuous form)
6. `maclaurin_step_proved` — packaged conclusion: $M_k \geq M_{k+1}$

## Active Approach
None — file is at rest. Any future work:

- Eliminate the inherited `newton_log_concavity` axiom by formalizing
  Newton's classical proof from real-rooted polynomial roots
  (Symmetric Functions chapter of Macdonald, or via Schur convexity).

## Attempt Counts
- Total attempts: 1 (original formalization + this STATE-SYNC)
- Current approach attempts: 0
- Approaches tried: 1 (Hardy-Littlewood-Pólya §2.22 induction)

## Blockers
None at the researcher level.

## Next Action
None required.

## Iteration History

| Iter | Date | Phase | Notes |
|---|---|---|---|
| 1 | 2026-03-26 → 2026-03-28 | NEW → ACT → COMPLETED | Original formalization (226 LOC, 0 file-local axioms, 1 inherited, 0 sorries); registry.completed 2026-03-28T06:36:47Z |
| 2 | 2026-05-17 | STATE-SYNC | Doc sync: state.md NEW iter-1 → COMPLETED iter-2; meta.json theoremCount 7→6 (top+leanFile) |
