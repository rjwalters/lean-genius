# Current State

**Phase**: COMPLETED (axiom-eliminated; gallery meta drift pending mechanic)
**Since**: 2026-05-06T21:21:23Z (PR #16378 merge)
**Last Updated**: 2026-06-02 (Session 6, researcher-1 — STATE-SYNC)
**Iteration**: 6

## Current Focus

File in stable end state: **0 axioms**, 0 sorries, 13 theorems in
`proofs/Proofs/Erdos183Problem.lean` (770 LOC).

The `R3k_exponential_lower` axiom (deep Ageron et al. 2021 Schur-number lower
bound) was eliminated in **PR #16378** ("research(erdos-183): prove
exponential lower bound via doubling construction", merged 2026-05-06T21:21:23Z)
by the planned doubling construction `R(3;k+1) ≥ 2·R(3;k) - 1`, yielding
`R(3;k) ≥ 2^k + 1` by induction — which is sufficient for the `∃ c > 1`
existential statement with c = 2.

## Gallery meta.json drift (re-flagged for next Mechanic cycle)

`src/data/proofs/erdos-183/meta.json` is internally inconsistent: it shows

| Field | Value | Comment |
|---|---|---|
| `status` | `"axiomatized"` | STALE — should be `"verified"` post-#16378 |
| `badge` | `"axiom"` | STALE — should match status |
| `axiomCount` | 0 | ✅ matches file reality |
| `sorries` | 0 | ✅ matches file reality |
| `lineCount` | 770 | ✅ matches file reality |

So `axiomCount: 0` is correct but `status`/`badge` reflect the pre-#16378
era. Per CLAUDE.md axiom-integrity policy ("0 axiom declarations AND 0
structure-encoded assumptions = verified") and `grep -c "^structure\|^class.*where\|^def.*Axioms"`
returning 0 lines, this file qualifies for `status: "verified"` once
the gallery is updated.

Suggested mechanic PR title:
`fix(meta): erdos-183 status axiomatized→verified + badge axiom→original (post-#16378 doubling-construction merge)`.

Researcher-role boundary forbids touching gallery `meta.json`.

## Active Approach

None — formalization is at its stable end state. Future enhancement
candidates (NOT REQUIRED):

1. Tighten the lower-bound constant: the doubling argument gives c = 2;
   Ageron–Bordeleau–Bormashenko–Yoshikawa (2021) give a stronger constant.
2. Match the Ramsey-theoretic upper bound: an inductive proof of
   `R(3;k) ≤ 3·k!` is in the file; the literature gives tighter forms.
3. Promote any of the metric/Ramsey helpers upstream to Mathlib once
   adjacent theory matures.

## Blockers

None — file is at stable end state.

## Next Action

For researcher-loop: **release as completed**. No tractable new work in
the researcher scope; gallery `meta.json` status/badge fix is mechanic
territory (see drift table above).

For mechanic cycle: flip `status: "axiomatized"` → `"verified"` and
`badge: "axiom"` → `"original"` in
`src/data/proofs/erdos-183/meta.json`.

## Attempt Counts

- Total attempts: 6 (5 prior + this STATE-SYNC)
- Current approach attempts: 0 (at end state)
- Approaches tried: pigeonhole induction (Ramsey), explicit constructions
  (R(3,3)=6), monotonicity via castLE, factorial upper bound via induction,
  **doubling construction (SUCCESS — #16378 eliminated last axiom)**

## File metrics @ 2026-06-02

- `proofs/Proofs/Erdos183Problem.lean`: 770 LOC / 13 theorems / 0 axioms /
  0 sorries / 0 structure-encoded assumptions
- Last git-touch: cosmetic co-touch `ecb47b35601` (sperner PR #19454,
  2026-05-29)
- Last substantive commit: `352e8872bf1` (fix: simp for
  doubleColoring_avoids case analysis, 2026-05-12)
- Last axiom-touching commit: `51187e5b175` ("prove exponential lower
  bound via doubling construction" — PR #16378 merge of
  `f0a7413c185`)
