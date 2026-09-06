# Forced triangle transitions admit C4-free partial extensions

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: the forced incident-selector triangle transitions are feasible
together with C4-freeness for all sufficiently large even q. This uses an
external Euler-tour theorem, not a Lean proof. The partial graph has the
correct degree q on C, but exterior degrees only 2 or 4. It is not a
regular ambient witness or a completion of the cross block.

## The forced transition system

Use the cyclic carrier from `NONBIP_MIXED_SIZE_TWO_TRIPLE_COMPANION_AUDIT.md`:
`C=Z/(2q)`, `H` has steps `±1`, `D` has all odd steps except `±1` plus
the antipode q, and `L` is the complement of D and the steps `±2`.
Exterior labels `F=E(L)` are their two-point selectors.

Let P be either parity class of C. The graph `R=L[P]` is `(q-4)`-regular
on q points: it is `K_q` minus the cycle of steps `±2` and the antipodal
matching. Opposite-parity L-edges are exactly the H-cycle edges.

Suppose a genuine integral reciprocal cross-block completion T exists.
For a same-parity selector `e={a,b}`, evaluate `HB+BT=J` at `(a,e)`.
Since `H(a,b)=0`, exactly one T-neighbor f of e contains a. The other
endpoint of f must lie in P. Otherwise f would be an H-cycle edge,
and the reciprocal equation at `(a,f)` would forbid its neighbor e.
The same reasoning at b gives one different T-neighbor through b.

Thus the T-edges between incident selectors in `E(R)` form a 2-factor J.
At each point a, they pair the `q-4` incident R-edges. This is a transition
system of the Eulerian graph R: its J-cycles are closed trails of R.

Full C4-freeness requires more than long J-cycles. If three consecutive
R-edges in a transition trail form a triangle, its first and last edges
share a C-point and also share the middle edge as a T-neighbor. This gives
a four-cycle. Therefore no such triangle segment is allowed. A J-cycle
of length four is also forbidden.

## A primary theorem resolves this local requirement asymptotically

Tien-Nam Le, [*Locally self-avoiding eulerian tours*, Theorem 1.3](https://arxiv.org/pdf/1611.07486),
proves that for each fixed positive integer ell, a sufficiently large
minimum degree guarantees an Euler tour in a simple Eulerian graph whose
segments of length at most ell are paths. The paper appeared in *Journal
of Combinatorial Theory, Series B* 135 (2019), 279--294,
[doi:10.1016/j.jctb.2018.08.008](https://doi.org/10.1016/j.jctb.2018.08.008).

Apply its ell=3 case to R. For even `q>=8`, R is connected: a component
has at least `q-3` vertices, and two such components would exceed q.
Its degree `q-4` is even. Consequently the theorem applies for every
sufficiently large even q, including all sufficiently large binary q.

List the R-edges in the resulting cyclic Euler order and join successive
edge labels to form J. This is a single cycle of length `q(q-4)/2`, hence
not a four-cycle, and it has no triangle segment in R. Choose such an
Euler tour independently for each parity class.

This invocation uses the theorem proved in the cited paper, without
assuming an explicit numerical minimum-degree threshold. The separate
finite example below does not purport to identify that threshold.

## A C4-free partial graph on all q-squared labels

Construct G0 on the disjoint union `C union F` with:

- H-cycle edges inside C;
- all incidence edges B between a point and its selector labels;
- the two J-cycles on same-parity exterior selectors;
- no other exterior edges.

The order is `2q+q(q-2)=q^2`. Its degrees are

```text
q at every C-point,
4 at every same-parity exterior selector,
2 at every opposite-parity exterior selector.                 (1)
```

It is C4-free. Classify a putative four-cycle by its number of C-points:

- Four C-points would give a four-cycle in H, whose length is `2q>4`.
- Three C-points and one exterior label would require an L-edge joining
  the ends of a two-edge H-path. Its endpoints are distinct, so their
  difference is `±2`, excluded from L by the K relation.
- Two C-points alternating with two exterior labels would require two
  distinct selectors with the same two endpoints. With the C-points
  consecutive instead, their H-edge changes parity, whereas an exterior
  J-edge preserves the parity of both its selectors. That is impossible.
- One C-point and three exterior labels would give two successive J-edges
  whose end selectors share that point. The corresponding three R-edges
  would close a triangle segment of the Euler tour, which was excluded.
- No C-points would require a four-cycle in one of the two long J-cycles.

The C-shore Gram identity remains exact because no C-neighborhood changed:

```text
H^2+BB^T=(q-1)I+J-D.                                      (2)
```

Thus the whole forced incident-selector transition layer can be placed
without any four-cycle, not merely without a four-cycle inside J.

## Concrete binary check and remaining gap

`check_size_two_euler_partial_graph.py` supplies a 96-edge cyclic Euler
tour for `K_16` minus its cycle and antipodal matching. It checks every
cyclic segment of length at most three, builds both parity copies and
the complete 256-vertex G0, and tests the common-neighbor bound on every
pair of vertices. It also checks (2) entrywise and obtains the degree
histogram

```text
32 vertices of degree 16; 192 of degree 4; 32 of degree 2.
```

Discovery of that finite tour used reversals of closed subtrails; the
saved sequence is verified directly without search or dependencies.

The missing edges are substantial: same-parity exterior labels still
need `q-4` neighbors each, and opposite-parity labels need `q-2` each.
They must be added as disjoint-selector edges, preserve C4-freeness,
and complete all entries of `HB+BT=J`. The zero-common-neighbor graph of
G0 is not asserted to have C as a connected component: that too needs
the completed cross block.

Cut a proposed exclusion based only on the forced triangle transitions
and C4-freeness of this partial layer. Retain the simultaneous placement
of the missing disjoint-selector edges as the actual unsolved problem.

## Every individual exterior star can also be completed at q=16

The saved binary partial graph passes a stronger local test. For each of
its 224 exterior labels e, separately, there is an explicit set of new
edges incident to e that raises its degree to 16 and leaves the entire
256-vertex graph C4-free. Every C-point keeps degree16, and all other
exterior vertices remain below16. The completed column at e is an actual
perfect matching on its required C-support.

`size_two_euler_star_completions_q16.json` stores all 224 choices as lists
of selector labels. `check_size_two_euler_star_completions.py` rebuilds the
same Euler baseline for every choice and verifies all 32,640 unordered
vertex pairs in each resulting graph: 7,311,360 common-neighbor checks in
total. It also verifies degree16 at e and every C-point, degree at most16
everywhere, and the exact completed matching column. The verifier uses
only the standard library and the saved Euler tour; it needs no optimizer.

Discovery used bounded binary linear feasibility problems, one per e.
Candidate edges were individually C4-safe. The selected neighbors cover
the remaining C-points exactly once, and pairs of selected new neighbors
with an old common neighbor were forbidden. These pair constraints matter:
several individually safe additions can create a four-cycle together.
The independent verifier checks the resulting whole graphs directly,
without trusting these discovery constraints or numerical solver output.

These are **224 separate completions of the same baseline**, not one
common completion. Superimposing the stars is neither verified nor
asserted to work. The result rules out a one-vertex obstruction for this
particular q=16 partial graph; it is not uniform in q and does not rule
out conflicts among completions at different vertices. Stop this local
star probe here and retain that simultaneous compatibility problem.
