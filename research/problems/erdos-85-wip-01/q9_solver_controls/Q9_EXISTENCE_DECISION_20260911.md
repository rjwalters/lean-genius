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
| 80 | 20 | — | — | Whole action class excluded: reviews2147–2149,2151 PASS |
| 80 | 16 | — | — | Necessary-condition exclusion, reviews2152/2154/2155/2157/2158/2160 PASS |
| 80 | 10 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 8 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 5 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 4 | 0 (planned) | 1h / 4h | Not launched |
| 80 | 2 | 0 (planned) | 1h / 4h | Not launched |
| 79 | All | — | — | Universal exclusion; independent Lean review2165 PASS |
| 78 | 39 | — | — | Paper exclusion, review2139 corollary |
| 78 | 78 | — | — | Paper exclusion: circulant degree bound |
| 78 | 26 | — | — | Whole action class excluded: reviews2141,2146 PASS |
| 78 | 13 | — | — | Whole action class excluded: reviews2153/2161/2162 PASS |
| 78 | 6 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 3 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |
| 78 | 2 | 0 (planned) | 1h / 4h | Not launched; scheduling follows N80 |

N78/m78 is a circulant and also fails the elementary degree bound; no solve is
needed. Unexcluded listed m values remain eligible; m1 is not silently added.

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

The N80/m16 action class is now also excluded by the independently reviewed
necessary-condition chain2152/2154/2155/2157/2158/2160. Complete quotient
coverage, mixed-triangle parity, parity/order-four character filters and actual
block relabellings reduce to four order-eight systems; all four are inconsistent
with independent reproduction. All relevant cases completed under original
caps. This is a computational algebraic exclusion, not a SAT verdict or Lean
theorem. The full evidence is in
[the m16 closure](../q9_n80_m16_exclusion/STATUS.md). No graph solver was
launched by this chain, and the positive-control correction is still pending.

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
and2or5 at N80. The fixed set is independent, and each fixed vertex lies in
three triangles. Accepted2179 gives a necessary residual form for N78/F3 and
N80/F5: respectively48vertices of degree6 with three prescribed partitions,
and30vertices of degree4 with five. These are unresolved residual problems,
not graph witnesses or exclusions. Evidence is preserved in
[the fixed-count proof](../q9_order3_fixed_counts/STATUS.md) and
[the residual form](../q9_order3_tight_normal_form/STATUS.md).

### Accepted N78 automorphism bound — snapshot 2026-09-11 16:43 UTC

The [accepted review snapshot](symmetry-accepted-snapshot-20260911.json)
records exact PASS scopes, review timestamps and hashes of the referenced
artifacts. It separates in-flight reviews from the accepted global bound.

Review2487 PASS strengthens the earlier review2408 bound: every hypothetical
N78/minimum-degree9 witness has full automorphism-group order in
**{1,2,3,4,6,8,12}**, hence at most12. This is a list of possible orders,
not a divisibility-by12 statement. Review2408 supplies the order48 exclusion
and preceding global order cover; review2487 excludes the full order16 case
through the accepted fixed-center action, kernel and residual branches
(2447,2438,2450,2479,2482,2477,2481,2484,2485 and their premise chains).
Its independent assembly audit is at `/tmp/erdos85-sol1-review2487`.

For the possible **full group of order12**, reviews2489/2494 give the group
cover. Accepted2544 excludes C3×V4; accepted2555 excludes C12 and Dic12.
Their scopes are full automorphism groups of these types, not unrestricted
N78 nonexistence. S3×C2 and A4 closure packets remain pending, so the accepted
bound stays12. Review2544's assembly audit is at
`/tmp/erdos85-sol1-review2544`; review2555's is at
`/tmp/erdos85-sol1-cyclic-composition-audit`.

The terminal C8 subgroup packet2622, Q8 subgroup packet2611, and subsequent
C4×C2 branch packets have **not been accepted** at this snapshot and are not
used to strengthen the bound. The order12 composition likewise awaits its
remaining reviews. Per editor messages50462/50463, new symmetry work stops;
the accepted snapshot will be refreshed at the17:30 UTC cutoff as pending
reviews finish. Every exclusion above is a reviewed paper/computational
result; it is not presented as a Lean theorem or SAT UNSAT certificate.
Asymmetric graphs and the surviving symmetry classes remain open. These
restrictions alone do not establish that the order49 example is sporadic.

## Current verdict

The N48 positive control succeeded and passed independent graph/model/map
validation. Both originally specified N63 action orders are mathematically
excluded: m63 by the circulant bound and m21 by two independently reviewed
Fourier arguments. The interrupted m21 solver remains recorded as UNKNOWN.
A concrete replacement control using the known N63 affine graph with m7 is
prepared by the generator owner but awaits correction of board39. No q9
class has run; N79 and the two-orbit N80/m40,N78/m39 classes are excluded by
separate reviewed arguments. N80/m20,m16 and N78/m26,m13 are also excluded
by accepted necessary-condition proofs, with no graph solver runs. The remaining
scheduled orders are10,8,5,4,2 at N80 and6,3,2 at N78. Nothing here establishes nonexistence on all
N78/N80 graphs, sporadic behavior at49, or the full Erdős85 result.
