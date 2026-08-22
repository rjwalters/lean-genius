# Weight-two cycle synchronization audit

## Exact reduction

Let `C` be a weight-two second-order-defect component at binary parameter
`q`.  Then `|C| = 2q`, `A[C]` is 2-regular, and every outside vertex has a
two-point trace in `C`.

For `x in C`, inspect the `q-2` outside A-neighbors of `x`.  If an outside
trace through `x` is an internal A-edge, the corresponding cross edge uses
its unique common neighbor inside `C`.  Otherwise its unique common neighbor
lies outside `C`; those outside neighbors pair up in `A[N_A(x) outside C]`.
Consequently the number of edge-traces through `x` is even.  Away from an
internal triangle it is at most two, so it is zero or two.  Therefore every
cycle of length at least five in `A[C]` is uniformly one of:

* T-saturated: none of its edges occurs as an outside trace;
* cross-saturated: every edge occurs as one outside trace.

This recovers the known `deg_T in {0,2}` propagation in its sharpest local
form.  The proposed all-or-nothing trace lemma additionally requires all
cycles of `A[C]` to choose the same orientation.

## Reduced countermodel at a binary parameter

`q16_weight_two_cycle_sync_reduced_sat.py` constructs a satisfiable exact
component-selector model at `q=16`.  Take two orientable even internal cycles

```text
A[C] = C6 disjoint-union C26.
```

Represent the `q^2-2q = 224` outside vertices by their distinct two-point
traces.  Thus the traces form a simple `(q-2)=14`-regular graph `F` on the
32 points of `C`.  The model imposes:

* degree 14 at every point of `C` (the exact component quotient degree);
* no repeated trace (simplicity, forced by C4-freeness);
* no trace pair having an internal common neighbor (the exact pair-codegree
  exclusion forced by C4-freeness);
* every trace joins opposite signs of the alternating vector on the two even
  cycles (the exact exterior-kernel/eigenline condition);
* the exact integral commutator `[H,F]=0`, where `H=A[C]`;
* no C6 edge in `F` (that cycle is T-saturated);
* every C26 edge in `F` (that cycle is cross-saturated).

Z3 finds such an `F`.  It has all 224 required traces but exactly 26
edge-traces.  Since there are no internal triangles, this is strictly between
the corrected synchronization endpoints 0 and `2q = 32`.  (The earlier
uncorrected endpoint `q^2-2q` counts all outside traces, most of which must be
non-edge pairs, and is not the right maximum.)  The script then independently
checks every listed invariant against the model.

The script also realizes the next cross-resolution layer explicitly.  Treat
each edge of `F` as an outside vertex joined across the cut to its two
endpoints.  At every `x in C`, pair the incident non-edge traces and put an
outside A-edge across each pair.  Edge-traces already resolve their two
cross edges through the other endpoint in `C`; the new matching edges resolve
every remaining cross edge through exactly one outside common neighbor.
The local matchings never reuse an outside edge, because two distinct trace
pairs cannot share two endpoints.  Direct checks give outside resolution
degree zero on the 26 edge-traces and degree two on all 198 non-edge traces,
with exactly one resolver for every cross incidence.

These numbers saturate the complete corrected two-component triangle ledger,
not just the vertexwise resolution law.  For component weights `2` and
`q-2`, there is no all-distinct triangle term and no cross `T` edge, so

```text
2q(q-2) = 2 t_12 + 2 t_21,
```

or `t_12+t_21=q(q-2)`.  Each selected internal edge of the weight-two
component contributes one `1,1,2` triangle, hence `t_12=26`; each constructed
outside resolution edge contributes one `1,2,2` triangle, hence `t_21=198`.
At q=16 their sum is exactly 224.  Thus the integer ledger and its mod-8
consequence are fully compatible with desynchronization; they merely divide
the cross-edge owners between the two sides.

The induced defect block is also exact, not a free placeholder.  Each of the
32 internal vertices supplies one selector pair consisting of its two
distance-two H-neighbors.  By the banked
`binarySquare_regular_sizeTwoSelectorGraph_eq_componentDefectComplementGraph`,
the induced defect graph is the loopless complement of these distance-two
pairs together with the 224 outside trace pairs.  The script reconstructs it
directly and verifies that it is 15-regular, connected, and non-bipartite on
all 32 vertices.  A global minimum-cut computation also gives exact edge
connectivity 15=`q-1`, with a singleton shore witnessing equality.  Thus the
reduced witness satisfies both the defining NONBIP defect-component condition
and the new maximal-edge-connectivity law of `8b427fab6c`; its missing layer
is outside adjacency, not the component's own defect realization or cut
structure.

A separate binary cut MILP, checked to optimality by HiGHS, minimizes over
shores of sizes 2 through 30 and returns 28=`2q-4`.  Hence every minimum
15-edge cut is trivial: this defect block is super-edge-connected and sharply
saturates the next nontrivial-cut lower bound discussed after `8b427fab6c`.
This is computational control evidence rather than a certificate, but it
shows that strengthening maximal edge-connectivity to super-edge-connectivity
still does not eliminate the reduced desynchronization pattern.

The alternating eigenline is also realized, rather than inferred merely from
the even cycle lengths.  Give consecutive vertices on each H-cycle signs
`+1,-1`.  Every selected outside trace joins opposite signs, so `M^T s=0`,
while `Hs=-2s`.  The reconstructed defect block directly verifies
`D[C]s=(q-5)s=11s`.  Hence this reduced witness survives the full
SIZE-TWO-EIGENLINE interface as well as the broader NONBIP-MIXED laws.

The commutator is not an optional strengthening.  If `M` is the component-to-
outside incidence matrix and `K` the outside induced adjacency matrix, the
cross block of `A^2` is

```text
H M + M K = J.
```

Multiplying by `M^T` and comparing with the transpose cancels the symmetric
term `M K M^T`.  Both margins of `M` are constant (`q-2` and 2), so the two
remaining all-ones terms agree, yielding `[H,MM^T]=0` over the integers.
Since `MM^T=(q-2)I+F`, this is exactly `[H,F]=0`.  The C6+C26 witness
therefore survives the full q-generic K-law/commutator interface, not merely
its mod-two shadow.

## Full exterior-completion frontier

For this explicit `F`, a full outside adjacency `K` must be a symmetric
zero-diagonal 0/1 matrix of degree 14 satisfying `HM+MK=J`.  Equivalently,
for every outside trace `r={u,v}`, its 14 neighbors in `K` must form an
`F`-perfect matching of the 28 component vertices outside
`N_H(u) union N_H(v)`.  Mutual selection turns this into an exact-cover
instance with 19,136 admissible outside edges and 6,272 exact-one equations.

The unrestricted instance is currently **UNKNOWN**: Z3, native Kissat,
HiGHS MILP, and OR-Tools CP-SAT did not return a verdict in bounded runs
(120--240 seconds).  CP-SAT's native presolve detected 268 large variable
orbits and explored millions of branches with no feasible solution, but did
not prove infeasibility.  Symmetry-restricted versions invariant under the
explicit
trace graph's order-39 rotation, its order-13 subgroup, or its order-3
subgroup are all UNSAT; thus any completion would have to break every visible
cyclic symmetry.  The exact-cover equations are verified consistent modulo
2, 3, and 5; the real LP is UNKNOWN (HiGHS found neither a primal point nor
an infeasibility proof in 120 seconds).  These are exploratory solver results,
not certificates and not a nonexistence claim.  The exact-cover equation is
the next honest falsifier for the reduced desynchronization witness.

The first omitted exterior C4-free layer has also been tested explicitly.
For every pair of outside traces sharing a component endpoint, forbid a
K-common-neighbor, since that endpoint is already their unique A-common-
neighbor.  This adds 429,624 binary incompatibilities to the 6,272 exact-one
equations.  Native CP-SAT still returned UNKNOWN after 180 seconds (219,182
branches, no incumbent).  Codegree-at-most-one for disjoint trace pairs has
not yet been added.  Thus even the intersecting-trace C4 layer has no bounded
solver verdict; no SAT or UNSAT claim is made.

## Verdict

Cycle synchronization does not follow from the complete component-side
selector degree, uniqueness, and internal-codegree laws, even at a relevant
parameter `q=2^4`.  This is a reduced countermodel, not a full regular
C4-free graph on `q^2` vertices, so it does not disprove the all-or-nothing
lemma itself.  It identifies the missing currency precisely: a proof must
couple traces belonging to different outside defect components, or enforce
the remaining outside-outside regularity and D-component placement.  Even
the simultaneous outside common-neighbor matchings and their induced even
degree split do not synchronize the cycles.  Further parity or packing
inside the single weight-two component cannot establish the lemma.
