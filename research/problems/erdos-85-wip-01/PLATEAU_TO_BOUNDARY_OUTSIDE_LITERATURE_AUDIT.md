# Plateau-to-boundary: outside-literature audit

Node: Goal #7, plateau-to-boundary localization.

Status: negative routing audit, 25 August 2026.  This does not close the
node.

## Exact repository interface

A `C4PlateauCore m d` is a `C4`-free graph on `m` vertices with minimum
degree `d`, whose degree-`d` vertices cover every edge, and for which no
`C4`-free graph on `m+1` vertices has minimum degree at least `d`.
`C4PlateauCore.conflict_indepNum_lt` says that its common-neighbour conflict
graph has independence number less than `d`.  Thus the direct one-vertex
extension problem is exactly:

> find `d` vertices no two of which already have a common neighbour.

The component bridge is already sharp at the level of bare order data.  A
component below `d^2` is regular and has order
`d(d-1)+3+e`, `0 <= e <= d-4`.  A proper component is itself one-step
nonextendable.  Therefore an outside result is useful only if it either
supports a multi-vertex repair, compresses a nonextendable component to
smaller excess, or classifies the whole positive-excess band.

There is an important exact warning in this regular band.  For a vertex
`x`, the `d` sets `N(z) \ {x}`, `z in N(x)`, are pairwise disjoint by
`C4`-freeness.  Hence `x` has exactly `d(d-1)` neighbours in the conflict
graph.  Its complement is therefore `(e+2)`-regular.  A safe `d`-set would
be a `K_d` in that complement, but `e+2 <= d-2`; such a clique is
impossible.  Thus the canonical add-one-vertex attachment cannot work in
the positive-excess band for a purely numerical reason.  The strict
conflict-independence bound of a plateau core is automatic there, not a
promising terminal.

This warning was already formalized before this audit:
`degree_commonNeighborConflict_of_regular_c4Free` and
`indepNum_commonNeighborConflict_le_excess` are in
`Erdos85ConflictRegular.lean`, while
`commonNeighborIndependent_card_lt_degree_of_excess_band` in
`Erdos85ConflictDefectDuality.lean` is the exact positive-excess-band
consumer.  It should be reused, not re-proved as a new endpoint.

## Closest literature

The closest exact match found is the attachment parameter used by the
modern regularity/container theory of `C4`-free graphs.  Conlon, Fox,
Sudakov and Zhao define `g_n(d)` as the maximum number of ways to attach a
new degree-`d` vertex to an `n`-vertex `C4`-free graph of minimum degree at
least `d-1` while preserving `C4`-freeness.  Their proof passes to the graph
in which two old vertices are adjacent when they have a common neighbour.
Consequently their admissible attachment sets are exactly independent sets
in our `commonNeighborConflict G`.

This is a genuine dictionary, but the direction is wrong for Goal #7.  The
published result bounds the **number** of admissible attachments from above
(`g_n(d) <= exp(O(sqrt n))`, with a sharper asymptotic in the sparse regime).
A plateau core asserts that this number is zero.  An upper bound cannot
prove the required nonemptiness, and the container proof has no stability
conclusion distinguishing zero from a small positive number.  Its auxiliary
edge lower bound is the same Moore-scale counting already present in the
repository.

Reference: D. Conlon, J. Fox, B. Sudakov and Y. Zhao, *The regularity method
for graphs with few 4-cycles*, Appendix C, especially Lemmas C.4--C.5:
https://people.math.ethz.ch/~sudakovb/sparse-regularity.pdf

The classical `C4`--star Ramsey literature is also adjacent but does not
supply localization.  The known comparison
`R(C4,K_{1,n+1}) <= R(C4,K_{1,n})+2` controls threshold movement by two; it
does not give the one-step monotonicity or an order-compression operation on
critical graphs.  Star-critical Ramsey numbers concern deleting a star from
the complete host at a fixed Ramsey threshold, whereas the present surgery
must add a vertex to the `C4`-free color while maintaining a minimum-degree
constraint.

Reference: Y. Chen, *A result on C4-star Ramsey numbers*, Discrete
Mathematics 163 (1997), 121--125,
https://doi.org/10.1016/0012-365X(95)00340-3

The Moore-excess/cage literature is not directly applicable.  It assumes
girth at least five, hence forbids triangles as well as `C4`; plateau cores
may contain triangles.  Its polynomial identities arise from unique short
paths and fail once adjacent vertices may have common neighbours.  Results
on cyclic excess therefore apply only after an additional triangle-free or
uniform-defect reduction, neither of which is banked for Goal #7.

Reference: M. A. Fiol, J. Gimbert and M. Miller, *On graphs with cyclic
defect or excess*, Electronic Journal of Combinatorics 18 (2011), P161,
https://arxiv.org/abs/1010.5841

## The closest multi-edge excision

A second, target-corrected search found a much closer operation after the
direct attachment route was cut.  Exoo, Jajcay and Raiman systematically
decrease the order of regular girth graphs by excision.  For even degree,
their Construction 2.4 deletes one vertex, pairs its former neighbours, and
adds the pairing edges.  A distance/cycle condition on every pair guarantees
that regularity and girth are preserved.  For odd degree, Construction 2.1
deletes an adjacent pair and repairs the two resulting even neighbour sets.
These are genuine multi-edge versions of the surgery needed here, not
one-vertex attachments.

Reference: G. Exoo, R. Jajcay and T. Raiman, *On decreasing the orders of
`(k,g)`-graphs*, Journal of Combinatorial Optimization 46 (2023), article
26, Constructions 2.1 and 2.4:
https://doi.org/10.1007/s10878-023-01092-9

The match is structural but not yet a theorem for this project.  Their
graphs have girth at least five, whereas a `C4`-free plateau core may have
triangles.  In the present setting, after deleting `u`, adding one repair
edge `ab` is safe only if there is no length-three `a`--`b` path; adding a
whole matching also needs simultaneous mixed-cycle compatibility among the
new edges.  The paper assumes a cycle-distance condition designed for the
girth setting and does not prove that the required pairing exists in every
non-cage; indeed it explicitly records graphs above cage order on which the
excision cannot be applied.  Thus it supplies the right operation and the
right compatibility question, but no universal existence theorem.

There is also a decisive terminal mismatch.  Excision deletes vertices and
adds edges, so its output has order `m-1` (or smaller).  A plateau core only
forbids a degree-`d` witness at order `m+1`; an order-decreased witness does
not contradict that hypothesis.  Nor does it contradict
`OrderMinimalC4PlateauCore`: minimality there ranges over smaller *plateau
cores*, while the excised graph is merely a witness.  In fact the original
order-`m` witness prevents the order-`m-1` witness from being a one-step
plateau.  Excision would reach a terminal only with an additional invariant
that permits iteration below the Moore bound, or transports nonextension to
the smaller order.  Neither is supplied by the paper, and cage examples show
that universal iteration is false.

Consequently neighbour-pairing is not a specialization of the repository's
delete-`k`/add-`k+1` gadget interface: that interface deletes `k` old vertices
and adds `k+1` new vertices, producing the required order-`m+1` witness.
Excision remains useful literature context for simultaneous `C4`-safe edge
repair, but it is not a surviving Goal #7 mechanism by itself.

## Verdict and surviving target

No outside theorem found supplies the missing plateau-to-boundary arrow.
The attachment literature provides an exact dictionary but, after the
degree calculation above, also confirms that the direct attachment route is
the wrong target.  A useful new theorem must instead produce the compatible
selectors for a delete-`k`/add-`k+1` repair, or force a specific reducible
configuration/order compression.  Generic container estimates, ordinary
`C4` saturation, star-critical Ramsey theory, and girth-five excess
classification do not do this.  The Exoo--Jajcay--Raiman excision is the
closest order-decreasing analogue, but it is terminal-disconnected even
before its universal pairing/existence step and its adaptation in the
presence of triangles are considered.  The surviving construction target
remains the genuinely order-increasing delete-`k`/add-`k+1` compatible-selector
theorem already isolated in the repository.

No Lean wrapper is recommended from this audit.

## Global selector allocation as hypergraph edge coloring

The growing-deletion-set regime has an exact coloring dictionary that is
different from the raw Hajnal--Szemeredi conflict-graph gate. For each old
survivor vertex `v`, let `l(v)` be the number of degree-loss occurrences
that must be assigned to new selectors. Make a ground point `p_v` and one
ground point for every survivor vertex `w`. Replace each of the `l(v)`
occurrences by a hyperedge

    E_(v,i) = {p_v} union N_survivor(v).

Two occurrence hyperedges intersect exactly when they come from the same
old vertex or their old vertices have a common survivor neighbor. Thus a
proper edge coloring of this multihypergraph is precisely a compatible
selector allocation; the required surgery asks for exactly `k+1` colors,
each containing exactly `d` occurrences.

The closest theorem is Pippenger--Spencer's asymptotic chromatic-index
theorem for uniform, almost-regular hypergraphs with maximum pair-codegree
`o(Delta)`:

N. Pippenger and J. H. Spencer, *Asymptotic behavior of the chromatic
index for hypergraphs*, Journal of Combinatorial Theory A 51 (1989),
24--42, https://doi.org/10.1016/0097-3165(89)90074-5.

This does not supply Goal #7. The occurrence hypergraph is generally
nonuniform because `|E_(v,i)|=1+deg_survivor(v)`. More importantly,
the `l(v)` copies are identical. For two distinct points
`w_1,w_2 in N_survivor(v)`, C4-freeness makes `v` their unique possible
common old neighbor, but their pair-codegree is still exactly `l(v)`.
The plateau interface does not bound `max_v l(v)=o(k)` in the required
growing regime `k` comparable to `d`; a survivor may be adjacent to many
deleted roots. Hence the small-codegree hypothesis is not available.
Near-regularity of the ground-point degrees is also absent.

Even after imposing extra hypotheses to enter an asymptotic regime, the
conclusion `chi' = Delta+o(Delta)` has an uncontrolled surplus. The
surgery needs exactly `k+1` colors and exact class size `d`; one additional
color changes the number of new vertices and loses the order-`m+1`
terminal. Pippenger--Spencer partitions almost all classes almost
perfectly, not all `d(k+1)` occurrences into exact `d`-sets.

Therefore hypergraph edge coloring is a faithful global reformulation but
not an outside theorem closing the bridge. A useful theorem would have to
exploit the special C4-linear neighborhood hyperedges and prove an exact
equitable `k+1` edge coloring despite repeated edges, or first construct a
deletion set with uniform loss and `o(k)` multiplicities. Neither property
is part of the current plateau-core interface.
