# Current State

**Phase**: COMPLETED
**Since**: 2026-05-17T04:19Z (researcher-3 S4 STATE-SYNC — post-#13816 drift catchup + JSON registry catchup + pool flip)
**Iteration**: 4

## Current Focus

S4 STATE-SYNC: doc-only catchup absorbing PR #13816 (rjwalters, merged
2026-04-29T05:08Z — added trivial upper bounds `erdos1183_f n ≤ 2^n` and
`erdos1183_F n ≤ 2^n`) that was not propagated to the research JSON registry
or pool. State.md "Since" was still pointed at S3's audit timestamp 30 min
*before* #13816 merged. All three of S3's "optional future work" upper-bound
items were in fact delivered by #13816; only the small-case computations
(f(0)=1, f(1)=1, f(2)=2) remain — and they are decoration, not load-bearing.

## Active Approach

None — formalization complete and pool-status now reflects completion.

`proofs/Proofs/Erdos1183Problem.lean` (**314 lines** post-#13816,
17 theorems, 14 definitions, 0 axioms, 0 sorries — `wc -l` canonical
convention; was 280 LOC pre-#13816) proves:

- **Lower bound** (Sessions 1–2): `f(n) ≥ ⌈(n+1)/2⌉` via the standard
  chain `∅ ⊂ {0} ⊂ {0,1} ⊂ ... ⊂ Fin n` and pigeonhole, plus
  `F(n) ≥ f(n)` via `csSup_le_csSup` (sublattices are union-closed).
- **Upper bound** (PR #13816, NEW in Part VII): `erdos1183_f_upper_bound`
  and `erdos1183_F_upper_bound` give `f(n), F(n) ≤ 2^n` via `csSup_le` and
  `Fintype.card_finset` — a constructive bound on the abstract `sSup`
  definitions corrected in Session 2.

Both open conjectures (`erdos1183_f_growth_conjecture`,
`erdos1183_F_superpolynomial_conjecture`) remain stated as `Prop`
definitions, not assumed true. 0 axiom declarations.

## Blockers

The remaining open questions (true asymptotic growth of f(n) and F(n)) are
genuine open problems in extremal combinatorics — Erdős and Ulam reported
having "no plausible conjecture" for the order of magnitude. Improving the
trivial chain bound is a research-paper-scale task, not a session task.

## Drift catchup ledger (this PR)

S3 (researcher-1, 2026-04-29T04:30Z) marked the slug COMPLETED and pool-
synced `in-progress → completed` for the pool entry. Thirty minutes later,
PR #13816 added Part VII (~34 LOC, 2 theorems) but did not update the
research JSON registry. As of S4 entry:

| Surface | Pre-S4 value | Post-S4 value | Reason |
|---------|--------------|---------------|--------|
| state.md "Since" | 2026-04-29T04:30Z (S3) | 2026-05-17T04:19Z (S4) | This PR |
| state.md "Iteration" | 3 | 4 | This PR |
| state.md "Active Approach" LOC | "280 lines" | "314 lines" | Canonical `wc -l` post-#13816 |
| state.md "Next Action" upper-bound bullet | OPTIONAL | DONE in #13816 | Bullet moved to Active Approach Part VII |
| JSON top-level `phase` | `OBSERVE` | `COMPLETED` | Matches state.md COMPLETED since S3 |
| JSON top-level `status` | `active` | `completed` | Standard `completed`+`COMPLETED` pairing (336 slugs) |
| JSON `currentState.phase` | `ACT` | `COMPLETED` | S3 already said COMPLETED in state.md |
| JSON `currentState.iteration` | 2 | 4 | Match state.md (S3 said 3, this S4 = 4) |
| JSON `currentState.focus` | "Formalized problem statement and proved trivial chain bound" | "S4 STATE-SYNC: ... upper bounds (PR #13816) absorbed" | Reflects #13816 delivery |
| JSON `currentState.nextAction` | "Begin problem exploration." | "Slug COMPLETED. Only optional decoration remains (f(0)/f(1)/f(2) small cases). Improving chain bound is research-paper-scale." | Reflects state.md S3 + S4 framing |
| JSON `currentState.attemptCounts.total` | 1 | 2 | This S4 = +1 (Sessions 1–3 already collapsed to "1" pre-S3 by an older convention; S4 adds 1 honest increment) |
| JSON `leanFiles[0].lineCount` | 315 | 314 | Mechanic-canonical `wc -l` (gallery meta.json already at 314) |
| JSON `knowledge.builtItems` | 14 items, no upper bound | append PR #13816 entry | Catchup |
| JSON `lastUpdate` | 2026-03-13T07:52:17Z | 2026-05-17T04:19Z | This PR |
| sessions/ directory | absent | bootstrapped + S4 memo added | Convention parity |
| Pool entry (`.lean/state/candidate-pool.json`) | `status: in-progress` | `status: completed` (post-PR via `claim-problem.sh update completed`) | Reflects state.md S3 + S4 |

## Next Action

**Nothing material**. The slug is closed:

- Lower bound: ✅ (Sessions 1–2)
- Upper bound: ✅ (PR #13816)
- Definitions corrected (`sInf → sSup`): ✅ (Session 2)
- 0 sorries, 0 axioms: ✅ (verified via `grep -c \\bsorry\\b` and `grep -c '^axiom '`)
- Pool / JSON registry / state.md mutually consistent: ✅ (this PR)

The remaining "optional" small-case computations (f(0)=1, f(1)=1, f(2)=2) are
decoration; the abstract bounds already imply them at n=0,1,2 (the chain
bound `⌈(n+1)/2⌉` gives 1, 1, 2 respectively, matching the trivial computed
values). A future researcher landing here should **RELEASE without PR**
unless new substantive drift accumulates (e.g., a mechanic sibling-batch
touches `Erdos1183Problem.lean` directly, or a Mathlib pin bump breaks
the build).

## Attempt Counts

- Total attempts: 4 (researcher-4 S1; researcher-2 S2; researcher-1 S3 audit; researcher-3 S4 STATE-SYNC + #13816 absorption)
- Current approach attempts: 0
- Approaches tried: 1 (chain + pigeonhole — the only known general technique; the upper bound is constructive from `Fintype.card_finset`)
