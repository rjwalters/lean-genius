# Research State: motivic-flag-maps-oq-02

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-03-30T06:50:26.393Z (per `research/registry.json`)
**Iteration**: 2 (S2 STATE-SYNC, 2026-05-17, brings doc in line with merged Lean)

## Outcome

Open Question `motivic-flag-maps-oq-02` — "Does the motivic class pattern
for full flag varieties extend to partial flags?" — is **formalized with
explicit axioms** for the two assertions that are not derivable from the
q-binomial/Schubert-cell algebra inside the file. The conjectural extension
to parabolic subgroups is axiomatized (per the OQ-02 framing) and the
algebraic infrastructure (q-numbers, q-factorials, Grassmannian classes,
Gaussian binomials, q-Pascal) is fully proved.

## Lean Source

`proofs/Proofs/MotivicFlagMapsPartialFlags.lean` — 635 LOC, 33 theorems/lemmas,
17 definitions, 2 axioms, 0 sorries.

| Field | Value |
|---|---|
| `axiom` declarations | 2 (`motivicClassPartialFlagMaps`, `partial_flag_extension`) |
| Structure-encoded assumptions | 0 |
| Tactic `sorry` | 0 |
| Definition `sorry` | 0 |

Gallery `src/data/proofs/motivic-flag-maps-oq-02/meta.json` records
`status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 2`, `sorries: 0`,
and now (post this S2) `theoremCount: 33`, `definitionCount: 17` matching
the Lean source. Prior values (38 / 18) over-counted by +5 / +1.

## Result Inventory

Six conceptual parts:

1. **q-analog infrastructure**: `qNumber n`, `qFactorial n`, with full
   identities (`qNumber_succ_eq_projective`, `qFactorial_eq_completeFlagClass`,
   `qFactorial_succ`) — these are proved, not axiomatic.
2. **Grassmannian classes**: `grassmannianClass d n`, base cases
   (`grassmannianClass_zero/of_zero/self/lines`) and the q-Pascal relation
   (`grassmannianClass_qPascal`) all proved by `ring`/algebra.
3. **Concrete instances**: `grassmannianClass_1_1/1_2/1_3/2_3/2_4` etc. as
   sanity checks.
4. **Partial flag varieties** — definitional layer, including parabolic
   subgroups and the Schubert-decomposition framework.
5. **Conjectured extension**: `axiom motivicClassPartialFlagMaps`,
   `axiom partial_flag_extension` — the two OQ-02 assumptions.
6. **References**: Bryan, Elek, Manners, Salafatinos, Vakil
   (arXiv:2601.07222).

## Active Approach
None — the file is at rest. Any future work would be:

- Eliminate `motivicClassPartialFlagMaps` by deriving the class from
  Schubert decomposition + the q-binomial coefficient (would require more
  Mathlib infrastructure on K₀(Var_k) than currently available).
- Eliminate `partial_flag_extension` by formalizing the parabolic
  factorization argument from Bryan et al. §3.

## Attempt Count
- Total attempts: 1 (the original formalization plus this STATE-SYNC)
- Current approach attempts: 0 (no active work)
- Approaches tried: 1 (axiomatize-and-prove-the-algebra)

## Blockers
None at the researcher level. Further axiom elimination is a longer-horizon
project requiring Schubert-cell decomposition theory in Mathlib.

## Next Action
None required. State synced to reflect that this slug is COMPLETED in the
registry and the Lean formalization has reached its conjecturally-axiomatized
rest state.

## Iteration History

| Iter | Date | Phase | Notes |
|---|---|---|---|
| 1 | 2026-03-29 → 2026-03-30 | OBSERVE → ACT → COMPLETED | Original formalization (635 LOC, 2 axioms, 0 sorries); registry.completed 2026-03-30T06:50:26Z |
| 2 | 2026-05-17 | STATE-SYNC | Doc sync: state.md OBSERVE iter-1 → COMPLETED iter-2; meta.json theoremCount 38→33 + definitionCount 18→17 |
