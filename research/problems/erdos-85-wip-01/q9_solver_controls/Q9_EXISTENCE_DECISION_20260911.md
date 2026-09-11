# Q9 existence decision experiment — 2026-09-11

IN PROGRESS. Owner of solver ledger: codex-sol-3. Operator scope: squad board39,
amended by editor messages50462/50463. At the2026-09-11 17:30 UTC snapshot, N80/m10
and N80/m8 are RUNNING in the two host solver slots. Local kissat; proof logging
OFF. No q9 verdict or graph witness has been reported.

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
| N63, delta>=8, m7 | 39337 / 134146 | Authorized replacement; queued for next shared slot |

The generator passed independent encoding review2138. The original serialized
runner passed eight software tests and independent review2134. The amended
two-slot `runner_launch.py` is a separate revision: the author reports four
focused process/concurrency checks, and sol-2 independently verified25 policy
cases on copied ledger data. The latter checks do not claim a live-concurrency
audit. Evidence is at
`/Users/rwalters/lean-genius-q9-known-values-20260911/q9-runner-launch-policy-audit`.
Tiny SAT, UNSAT and interrupted-process fixtures do not count as graph controls.
The editor's
50462/50463 amendment makes the independently verified N48 control sufficient
for q9 launches. N63/m7 is authorized as a replacement calibration control,
using the existing affine input. It runs in parallel at the next available
shared solver slot and does not gate q9 launches. The old m21/m63 specification
remains mathematically impossible; its historical UNKNOWN is preserved.

## Action classes and budgets

| N | Cyclic action order m | Seed | Initial / UNKNOWN requeue cap | Status |
|---:|---:|---:|---|---|
| 80 | 40 | — | — | Paper exclusion, review2139 PASS |
| 80 | 20 | — | — | Whole action class excluded: reviews2147–2149,2151 PASS |
| 80 | 16 | — | — | Necessary-condition exclusion, reviews2152/2154/2155/2157/2158/2160 PASS |
| 80 | 10 | 0 | 1h / 4h | RUNNING: run002, PID68975 |
| 80 | 8 | 0 | 1h / 4h | RUNNING: run003, PID77447 |
| 80 | 5 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 4 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 2 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 1 (no symmetry) | 0 (planned) | 1h / 4h | Authorized; not launched |
| 79 | All | — | — | Universal exclusion; independent Lean review2165 PASS |
| 78 | 39 | — | — | Paper exclusion, review2139 corollary |
| 78 | 78 | — | — | Paper exclusion: circulant degree bound |
| 78 | 26 | — | — | Whole action class excluded: reviews2141,2146 PASS |
| 78 | 13 | — | — | Whole action class excluded: reviews2153/2161/2162 PASS |
| 78 | 6 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 3 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 2 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 1 (no symmetry) | 0 (planned) | 1h / 4h | Authorized; scheduling follows N80 |

N78/m78 is a circulant and also fails the elementary degree bound; no solve is
needed. The amended launch order is N80 m10,8,5,4,2,1, then N78 m6,3,2,1.
The unsymmetrized m1 cases are explicitly authorized by50462. All ten inputs
passed [byte-regeneration and edge-map preflight](launch_input_preflight/results.json).

Accepted review2153 gives exactly two necessary N78/m13 quotient types (70
labelled matrices), both with Q²=9I+12J. Review2161 excludes type A by
complementary difference sets around a triangle. Review2162 excludes type B
because two internally degree2 Z13 orbits cannot support a degree3 cross block.
Together these close N78/m13; full evidence is in
[the m13 closure](../q9_n78_m13_exclusion/STATUS.md).

N80/m10 has an incomplete necessary quotient frontier (review2156): all16
roots reached their original100000-row caps, leaving1998 saved candidates.
Every root remains UNKNOWN, including roots with no retained matrix. This
frontier neither excludes the action class nor supplies a complete quotient
cover; it has not been restarted or expanded.

N80/m8 likewise has an incomplete necessary quotient frontier (review2168):
all13 roots reached100000-row caps, retaining24 matrices; none completed.
Accepted2164 excludes the all-singleton quotient and supplies local cyclic
constraints, but does not close the class. No capped search was replayed.


The runner preserves UNKNOWN, binds each requeue to the exact CNF, variable
map and seed, and permits at most one four-hour requeue after an initial
UNKNOWN. Aggregate solver wall time, including controls, is limited to48h.
Observed q9 SAT output stops new launches independently of final exit/status.
Any witness is saved as an adjacency list and independently checked by a
second seat before the editor reports it to Robb. No cloud, q11/q13, or N81
nonexistence campaign is authorized by this experiment. Phase B stays gated.

Terminal graph-solver time is377.247884959 seconds (about0.104791hours),
including the interrupted control. The two active runs additionally accrue
wall time and reserve their full caps against the48-hour aggregate budget.
The live ledger at `/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls/ledger.json` is authoritative for statuses and accounting.
Use `runner_launch.py`, which locks only ledger transactions and supports two
slots; the old serialized `runner.py` must not be run concurrently.
Independent live-start checks bind both processes to their exact preflight
CNFs/maps, seed0,3600-second caps, and recorded runner/solver hashes.

The m21 run was stopped only after accepted paper review2145 made its intended
positive-control purpose impossible. The recorded solver result is UNKNOWN,
exit−15, with no SAT observed; the paper exclusion is a separate result.
It will not be retried. The N48 graph has48vertices,168edges and degree7
throughout, with two free24cycles preserving adjacency.

Accepted paper review2140 also derives regularity from minimum degree below
square order. Thus N78/N80 delta>=9 witnesses would have exactly351/360edges;
N79 is excluded independently by odd degree sum. Generic CNFs remain
minimum-degree encodings, without silently assumed regularity.

The N80/m16 action class is now also excluded by the independently reviewed
necessary-condition chain2152/2154/2155/2157/2158/2160. Complete quotient
coverage, mixed-triangle parity, parity/order-four character filters and actual
block relabellings reduce to four order-eight systems; all four are inconsistent
with independent reproduction. All relevant cases completed under original
caps. This is a computational algebraic exclusion, not a SAT verdict or Lean
theorem. The full evidence is in
[the m16 closure](../q9_n80_m16_exclusion/STATUS.md). No graph solver was
launched by this chain; the separate amended q9 launch campaign is now active.

## Formal checks and general symmetry restrictions

Independent direct-source Lean review2165 verifies the general odd-order
below-square obstruction and its N79/minimum-degree9 specialization. The
latter excludes N79 without a symmetry assumption. Its axiom audit contains
only propext, Classical.choice and Quot.sound, with no sorryAx. The remaining
finite action-class exclusions are separately reviewed paper/computational
results, not fully formalized Lean theorems.

Accepted2163 rules out automorphisms of prime order greater than9 for either
N78 or N80. Accepted2166 rules out order5 automorphisms at N78 and shows
that every order5 automorphism at N80 must be free. Accepted2169 rules out
order7 automorphisms at either order, including those with fixed vertices.
Thus the automorphism-group order of any hypothetical witness has prime
divisors only2,3 at N78, and only2,3,5 at N80. These restrictions do not
exclude asymmetric witnesses or settle unrestricted existence.

Accepted2176 restricts exact-order3 automorphisms to fixed counts0or3 at N78
and initially2or5 at N80. Accepted2214 closes the entire N80/F5 case by a
complete necessary-domain composition: its1284 cases partition as
708+516+58+1+1, with no uncovered case. Therefore **every order3 automorphism
at N80 fixes exactly2 vertices**. The fixed set is independent, and each
fixed vertex lies in three triangles. This is a paper/computational symmetry
restriction, not unrestricted N80 nonexistence or a Lean theorem. Its
independent audit is at
`/Users/rwalters/lean-genius-q9-known-values-20260911/review-2214`.

The N78/F3 residual problem from2179 remains open:48 vertices of degree6
with three prescribed partitions. The earlier N80/F5 residual form is now
part of the excluded branch, not an open case. Foundational evidence remains
in [the fixed-count proof](../q9_order3_fixed_counts/STATUS.md) and
[the residual form](../q9_order3_tight_normal_form/STATUS.md).

### Accepted N78 symmetry results — cutoff 2026-09-11 17:30 UTC

The [accepted review snapshot](symmetry-accepted-snapshot-20260911.json)
records exact acceptance timestamps, scopes and source-artifact hashes.
Pending reviews and explicitly scoped partial results are preserved separately;
UNKNOWN and unvisited cases supply no exhaustive exclusions.

Review2487 excludes full order16, using the accepted fixed-center action,
kernel and residual chains2447/2438/2450/2479/2482/2477/2481/2484/2485.
Together with2408, this gives the full-group order cover1,2,3,4,6,8,12.
For full order12,2489/2494 give C12, Dic12, C3×V4, S3×C2 or A4.
Review2555 excludes C12/Dic12,2544 excludes C3×V4, and2627 excludes
S3×C2 through all fourteen profiles2553/2572/2577/2579/2583/2586/2588/2589.

The final A4/order12 composition2629 was not accepted by the cutoff.
Consequently the frozen accepted full-group order cover remains
**{1,2,3,4,6,8,12}, hence at most12**. Accepted A4 components are recorded
with their exact scopes; they do not independently promote this snapshot's
global bound without acceptance of the exhaustive composition.

Review2611 separately excludes any Q8 automorphism subgroup, through
2245/2608/2609 and its complete106 center partitions and nine Q8 quotient
choices. This is a subgroup exclusion, stronger than merely excluding
fullAut=Q8. Positive C8 necessary-domain witnesses in that packet do not
exclude C8.

The terminal C8 packet2622 was not accepted at the cutoff and supplies no exclusion here.

Per editor50462/50463, this symmetry programme is frozen at the cutoff;
no new exclusion lane or capped retry is opened. These are reviewed paper
and computational results, not Lean theorems or proof-logged SAT certificates.
Asymmetric graphs, surviving symmetry classes and unrestricted N78/N80
existence remain open. No conclusion that49 is sporadic follows.

### Frozen N80 cubic-fixed involution class0 LP frontier

The accepted class0 chain ends at2585: among91 remaining arrangement
models,12 exact contradictions leave79 rational feasible necessary models
across all12 surviving support roots. Rational feasibility is not a graph
witness. No entire class0 or surviving support root is excluded by this step.

The chain is2515/2518/2539,2542/2543/2546,2550,2556,2558,2561,2563,
2566,2568,2570,2576 (also2231),2578,2581,2582,2585. It includes exact
source coverage, retained old constraints, necessary strengthened rows,
full local domains and independently checked rational/Farkas certificates.
Review2585 checks all25116 joint matrix choices and18652 forbidden weights;
its12 contradictions and79 feasible certificates are exact. Earlier saved
UNKNOWN receipts are preserved; exact later certificate recovery does not
resume those capped producers. Subsequent packets2587 onward were pending
at the cutoff and supply no additional accepted exclusion here.

The [amended launch archive](amended-launch/README.md) contains the exact
runner/controller source, authorization, independent policy audit, input copies
and timestamped live process/ledger snapshot. This snapshot is not a verdict.

The [independent encoding audit](../q9_encoding_audit_claude/README.md)
covers all ten scheduled q9 inputs and both N48/N63-m7 controls. It checks
orbit maps, functional auxiliary gates and constraint semantics, with zero
observed mismatches. Its17 package files, including13 logs, were independently
verified against the published hash manifest. Encoding validation does not
turn a proof-OFF UNSAT report into a nonexistence certificate.

Independent review2628 accepts the [offline witness decoder](decoder-review/REVIEW.md):
3087 small graph/degree/action cases agree with a separate cycle oracle,
and the accepted N48 adjacency is reproduced exactly. Each future SAT
artifact still requires independent model and graph validation.

## Current verdict

IN PROGRESS. N79 is excluded independently by literature and the accepted
below-square odd-order theorem. The N48 positive control is independently
verified. The corrected N63/m7 calibration is authorized and queued without
blocking q9. N80/m10 and N80/m8 are live under their initial one-hour caps;
the other eight scheduled q9 instances have not launched. Each terminal
UNKNOWN permits only one four-hour requeue with identical CNF, map and seed,
subject to the aggregate48-solver-hour and first-witness stop rules.

The accepted symmetry exclusions restrict possible witnesses but do not
settle unrestricted existence at N78 or N80. A solver report with proof
logging off must be distinguished from an independently verified
nonexistence certificate; any SAT output requires independent graph/model
validation. Keep this deliverable IN PROGRESS until every scheduled instance
has a verdict or its allowed requeue/budget has expired, or a verified witness
ends the campaign. No conclusion that49 is sporadic or that Erdős85 is solved
is justified by the current evidence.
