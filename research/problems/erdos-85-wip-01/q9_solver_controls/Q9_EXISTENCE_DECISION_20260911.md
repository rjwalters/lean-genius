# Q9 existence decision experiment — 2026-09-11

IN PROGRESS. Owner of solver ledger: codex-sol-3. Operator scope: squad board39.
Zero spend; local kissat; proof logging OFF. Two graph-control runs are terminal.
No q9 instance has launched. The second-control specification needs correction.

## Known values

f(N)=1+max δ(G) over C4-free N-vertex graphs, and R(n)=R(C4,K1,n).
The exact bridge is f(N)>=d+1 iff R(N-d)>N. The independently reviewed
[literature component](/Users/rwalters/lean-genius-q9-known-values-20260911/Q9_KNOWN_VALUES_20260911.md)
contains primary source links, qualifications and deductions; review2137 PASS.
Intervals below mean unresolved by the traced sources, not proof of globally
unknown status. The reported column preserves cited values with unresolved
source dependencies.

| N | Traced f(N) | Reported f(N) |
|---:|:---:|:---:|
| 73 | 9 | 9 |
| 74 | 9 | 9 |
| 75 | 8–9 | 9 |
| 76 | 9 | 9 |
| 77 | 9 | 9 |
| 78 | 9–10 | 9–10 |
| 79 | 9 | 9 |
| 80 | 9–10 | 9–10 |
| 81 | 9–10 | 9–10 |
| 82 | 9–10 | 10 |
| 83 | 9–10 | 10 |
| 84 | 10 | 10 |
| 85 | 9–10 | 10 |
| 86 | 10 | 10 |
| 87 | 10 | 10 |
| 88 | 10 | 10 |
| 89 | 10 | 10 |
| 90 | 10 | 10 |
| 91 | 10 | 10 |

N79/delta9 is excluded by the published R70=79 theorem. The relevant N78/N80
existence decisions remain unresolved by these sources. See the literature
component for the repaired R72 lower-bound dependency and remaining citation gaps.

## Positive controls

| Control | CNF variables / clauses | Current status |
|---|---:|---|
| N48, delta>=7, m24 | 3757 / 13047 | SAT, 0.046s; independent review2142 PASS and registered |
| N63, delta>=8, m21 | 11074 / 38347 | Interrupted UNKNOWN after377.202s; separately excluded by paper proofs2144/2145 |
| N63, delta>=8, m63 | — | Impossible circulant control; no solver run |

The generator passed independent encoding review2138. The revised runner has
eight passing software tests and accepted independent review2134. Tiny SAT,
UNSAT and interrupted-process fixtures do not count as graph controls. Both
actual positive controls require independent decoded-graph receipts before q9
launches. N48 satisfies this condition; the specified N63 action orders are
mathematically impossible. A correction to the explicit affine m7 control has
been requested by the squad and is pending; it has not been substituted. The m7 affine diagnostic from sol1 is a construction/encoding test,
not a substitute for the specified m21/m63 control.

## Action classes and budgets

| N | Cyclic action order m | Seed | Initial / UNKNOWN requeue cap | Status |
|---:|---:|---:|---|---|
| 80 | 40 | — | — | Paper exclusion, review2139 PASS |
| 80 | 20 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 16 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 10 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 8 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 5 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 4 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 2 | 0 (planned) | 1h / 4h | Not launched |
| 79 | All | — | — | Literature exclusion, review2137 PASS |
| 78 | 39 | — | — | Paper exclusion, review2139 corollary |
| 78 | 78 | — | — | Paper exclusion: circulant degree bound |
| 78 | 26 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 13 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 6 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 3 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 2 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |

N78/m78 is a circulant and also fails the elementary degree bound; no solve is
needed. Other listed m values remain eligible; m1 is not silently added.

The runner preserves UNKNOWN, binds each requeue to the exact CNF, variable
map and seed, and permits at most one four-hour requeue after an initial
UNKNOWN. Aggregate solver wall time, including controls, is limited to48h.
Observed q9 SAT output stops new launches independently of final exit/status.
Any witness is saved as an adjacency list and independently checked by a
second seat before the editor reports it to Robb. No cloud, q11/q13, or N81
nonexistence campaign is authorized by this experiment. Phase B stays gated.

Graph-solver time charged so far:377.247884959 seconds (about0.104791hours),
including the interrupted control. Exact histories, caps, exit codes and hashes
are in q9-solver-controls/ledger.json. No own solver remains live.

The m21 run was stopped only after accepted paper review2145 made its intended
positive-control purpose impossible. The recorded solver result is UNKNOWN,
exit−15, with no SAT observed; the paper exclusion is a separate result.
It will not be retried. The N48 graph has48vertices,168edges and degree7
throughout, with two free24cycles preserving adjacency.

Accepted paper review2140 also derives regularity from minimum degree below
square order. Thus N78/N80 delta>=9 witnesses would have exactly351/360edges;
N79 is excluded independently by odd degree sum. Generic CNFs remain
minimum-degree encodings, without silently assumed regularity.

## Current verdict

The N48 positive control succeeded and passed independent graph/model/map
validation. Both originally specified N63 action orders are mathematically
excluded: m63 by the circulant bound and m21 by two independently reviewed
Fourier arguments. The interrupted m21 solver remains recorded as UNKNOWN.
A concrete replacement control using the known N63 affine graph with m7 is
prepared by the generator owner but awaits correction of board39. No q9
class has run; N79 and the two-orbit N80/m40,N78/m39 classes are excluded by
separate reviewed arguments. Nothing here establishes nonexistence on all
N78/N80 graphs, sporadic behavior at49, or the full Erdős85 result.
