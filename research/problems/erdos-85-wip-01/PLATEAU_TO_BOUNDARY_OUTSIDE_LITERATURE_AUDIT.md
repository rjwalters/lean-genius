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

### Exact-Delta coloring via balanced hypergraphs is also unavailable

Balanced hypergraphs have the exact edge-coloring property
`chi'(H)=Delta(H)`, so at first sight they avoid the asymptotic color
surplus above (Berge--Las Vergnas, *Sur un théorème du type König pour
hypergraphes*, 1970,
https://doi.org/10.1111/j.1749-6632.1970.tb56451.x). The occurrence
hypergraph is not forced to be balanced.
If the survivor graph contains an induced six-cycle

    v_1-w_12-v_2-w_23-v_3-w_31-v_1,

then the three occurrence hyperedges based at `v_1,v_2,v_3` form a strong
odd Berge cycle through the ground points `w_12,w_23,w_31`: consecutive
hyperedges meet at the displayed point, and inducedness ensures none of
the three contains all three cycle points. This is precisely a forbidden
balanced-hypergraph submatrix. `C4`-freeness does not forbid induced
six-cycles (the cycle `C6` itself is the smallest control), so balancedness
cannot be derived from the plateau interface.

Moreover `chi'=k+1`, even if available, supplies `k+1` matchings but does
not by itself force every color class to contain exactly `d` occurrences.
The total average is `d`, yet a proper edge coloring may have unequal
class sizes. The compensated surgery needs exact equality because each
new edgeless-gadget vertex must have degree `d`. Thus this route would
still need an equitable recoloring theorem after balancedness.

The balanced-hypergraph theorem therefore identifies another possible
extra hypothesis—absence of strong odd neighborhood cycles—but neither
that hypothesis nor exact equitability is currently forced.

## Square-order candidates necessarily have too many 5-cycles for sparse removal

2026-09-08, sol-1; follow-up to divergence 111. This is a prose
source-transfer audit, not a new A-REG exclusion or Lean theorem.

Conlon--Fox--Sudakov--Zhao, [Theorems 1.1--1.2](https://arxiv.org/html/2004.10180),
require `o(n^(5/2))` copies of C5. Their hypergraph girth consequence
requires girth strictly greater than five, whereas the mixed triangle/edge
system in the current candidate only forbids Berge cycles of lengths
three and four. More decisively, the graph removal hypothesis cannot hold
for an unbounded family of square-order regular candidates.

Let A be a q-regular C4-free adjacency matrix on n=q² vertices, q>=3.
The banked identity `A²=(q-1)I+J-D`, with D (q-1)-regular, implies
`|lambda|<=sqrt(2(q-1))` for every eigenvalue on the orthogonal complement
of the all-one vector. This also excludes a second principal eigenvector.
Consequently

    |tr(A^5)-q^5| <= (q²-1)[2(q-1)]^(5/2).

Let t be the number of triangles and c5 the number of unoriented simple
5-cycles. The exact closed-walk identity is

    tr(A^5) = 10c5 + 30(q-1)t
            = 10c5 + 5(q-1)tr(A^3).

For completeness, a nonsimple closed walk of length five has a triangle
as its only cyclic support. There are 30 such walks supported on each
triangle alone. Each of the 3(q-2) edges leaving that triangle supplies
10 walks using that edge as a backtrack. No exterior vertex meets two
triangle vertices, by C4-freeness. These contributions give 30(q-1)t;
each simple 5-cycle contributes its ten rooted oriented walks.

Every neighborhood is a matching, so `tr(A^3)=6t<=q³`. Hence

    |10c5-q^5| <= (q²-1)[2(q-1)]^(5/2) + 5(q-1)q³,
    c5 = q^5/10 + O(q^(9/2)) ~ n^(5/2)/10.

Thus the required little-o hypothesis is false for any such unbounded
family. This does not contradict the source theorem or exclude candidate
graphs; it prevents using that theorem directly as the missing structural
step. Stronger hypotheses on particular subsets would need a separate
argument.

Independent finite calibration: exact matrix powers and direct simple
cycle enumeration on the stored q4 graph give `(tr A³,tr A⁵,c5)=(48,960,24)`;
on Boza H36 they give `(192,7680,288)`. Both satisfy the exact identity.
These checks calibrate the walk formula, not its asymptotic conclusion.

There is also a finite-threshold check for the saturated case
`d_u in {0,2}` (sol-3, independently checked by Claude and sol-1).
Its triangle hypergraph is linear, has Berge-girth at least five, and
has minimum degree `r=q/2-1`. If it had no Berge 5-cycle, an edge-rooted
breadth-first count would give three root vertices, at least `6(r-1)`
vertices in the next layer, and at least `12(r-1)²` in the following
layer. A collision would create a Berge cycle of length at most five.
Therefore

    q² >= 3[1+2(r-1)+4(r-1)²] = 3q²-21q+39.

This fails for q>=9, hence for binary q>=16. The triangle hypergraph must
then contain a Berge 5-cycle. At q=8 the bound is only 63<=64 and gives
no exclusion. Thus the source's girth-greater-than-five hypothesis also
fails in this case; this is not an exclusion of the saturated candidate.

### Biregular girth-ten cages: exact hypotheses still missing (2026-09-08)

Primary sources checked:

- Araujo-Pardo, Ramos-Rivera and Jajcay,
  [Bipartite Biregular Cages and Block Designs](https://arxiv.org/html/1907.11568),
  introduction and generalized-polygon correspondence.
- Araujo-Pardo, Kiss and Szőnyi,
  [A little more about bipartite biregular cages, block designs and generalized polygons](https://arxiv.org/html/2310.12137),
  Definition 1 and Section 2.

These bounds require constant degree on each side of the incidence graph.
The first paper also reports the earlier small-excess exclusion for
unequal degrees at least three, girth at least ten not divisible by four,
and excess at most four. The second develops divisibility improvements
under the same biregularity requirement. This is not a theorem about a
mixed-rank incidence graph or an almost-regular point side.

For the saturated candidate `d_x ∈ {0,2}`, put `r=q/2`. Keeping all
triangle blocks and triangle-free edges gives block degrees 3 and 2, and
point degrees `r+d_x/2`. Dropping the size-two blocks instead gives block
degree 3 but point degrees `r-d_x/2 ∈ {r,r-1}`. Neither construction is
known to meet the sources' biregularity hypotheses. All `d_x=0` is already
impossible for binary q by the triangle-incidence divisibility `3 ∣ q³/2`.
All `d_x=2` would give a biregular graph of degrees `(3,s)`, `s=r-1`.
Even that special case lies outside the reported small-excess result:
the source's edge-rooted Moore expression at girth ten is
`B(3,s;10)=10s²-11s+5`, whereas the incidence graph would have
`q²(1+s/3)` vertices. Its excess over that bound would be
`(4s³-10s²+61s-3)/3`, at least 66 for `s>=3`, not at most four.
At q=8 the degrees are equal, also outside the unequal-degree result.
The first source's stronger bounds do not change which Moore expression
defines the small-excess theorem being cited.

Our elementary bound that does survive this loss of regularity is too
weak: a linear triple system of Berge girth at least five and minimum
point degree `s` has at least

    1 + 2s + 4s(s-1) = 4s²-2s+1

points, by counting the first two triangle layers at a point. At
`s=r-1` this is `q²-5q+7`, below the candidate order `q²`.
The source's stronger regular conclusions cannot be substituted for this
bound without a new transfer theorem. The general A-REG candidate need
not even satisfy the saturated hypothesis. This bounded source check
therefore supplies no uniform exclusion and no new Lean obligation.


### Hoory's irregular bipartite bound falls short for every candidate (2026-09-08)

The constant-degree restriction above can be avoided using Hoory's bound,
as stated and proved in Babu and Radhakrishnan,
[An entropy based proof of the Moore bound for irregular graphs](https://arxiv.org/html/1011.1058),
Theorem 2 and Section 4.1. It assumes minimum degree at least two and uses
separate average degrees on the two sides. Thus it applies to the mixed
incidence graph formed by the triangles and triangle-free edges of a
q-regular C4-free graph on q² points, q>=8. Nevertheless, neither of its
girth-ten side bounds gives a contradiction. This conclusion does not
require saturation.

Every vertex lies in at least one triangle: otherwise its first two graph
distance layers would contain 1+q+q(q-1)=q²+1 distinct points. If d_x is
its triangle-free degree and t_x its triangle degree, then 2t_x+d_x=q,
so 0<=d_x<=q-2. Write delta for the mean of d_x. The mixed incidence graph
has girth at least ten: linearity excludes incidence 4-cycles, a Berge
3-cycle would give a graph triangle whose edges cannot belong to distinct
blocks, and a Berge 4-cycle would give a graph C4. All incidence degrees
are at least two.

The point and block counts and average incidence degrees are

    n_L = q²,                  n_R = q²(q+2delta)/6,
    d_L = (q+delta)/2,         d_R = 3(q+delta)/(q+2delta),
    0 <= delta <= q-2.

Indeed, the counts of triangle-free edges and triangles are respectively
q²delta/2 and q²(q-delta)/6. Put

    x = d_L-1 = (q+delta-2)/2,
    y = d_R-1 = (2q+delta)/(q+2delta).

Hoory's two girth-ten right-hand sides are

    H_L = 1+y+xy+xy²+x²y²,
    H_R = 1+x+xy+x²y+x²y².

They assert n_L>=H_L and n_R>=H_R. Both are strictly satisfied by the
candidate counts for every delta in the permitted interval.

For the point side, set z=delta/(q-2). The exact polynomial
P=4(q+2delta)²(q²-H_L), after substituting delta=(q-2)z, has the degree-four
Bernstein representation P=sum_{i=0}^4 b_i binom(4,i) z^i (1-z)^(4-i), with

    b_0 = 4q²(q-1),
    b_1 = q(2q³+5q²-18q+16)/2,
    b_2 = (3q-2)(5q³-24q+32)/6,
    b_3 = 3q⁴-28q²+54q-28,
    b_4 = 8(q-1)(3q²-9q+8).

Each coefficient is positive for q>=4. For example, the potentially
negative terms pair as q(5q-18), q(5q²-24), q²(3q²-28), and 3q(q-3)
in b_1 through b_4. The Bernstein weights are nonnegative and sum to one
on 0<=z<=1. Hence P>0 and H_L<q² throughout the entire interval.
Sol1 derived this certificate; Sol3 independently expanded the rational
expression and recovered all five coefficients exactly with SymPy.

For the block side, xy<=q-1, since

    2(q-1)(q+2delta) - (q+delta-2)(2q+delta)
      = 2q + delta(q-2-delta) > 0.

As x,y are nonnegative,

    H_R = 1+x+xy(1+x+xy) <= q*x+q²-q+1.

Six times the difference between n_R and this upper bound is

    q³-9q²+12q-6 + delta*q*(2q-3).

The delta term is nonnegative. Setting q=8+u, u>=0, expands the remaining
polynomial as 26+60u+15u²+u³, which is positive. Thus H_R<n_R as well.

This is an algebraic comparison of necessary bounds, not an existence
claim for any degree distribution. It closes the direct average-degree
Hoory-bound transfer at girth ten for the whole q>=8 square-order regular
candidate class. It does not address stronger inequalities using incidence
correlations or permit promoting any A-REG node to an exclusion theorem.
