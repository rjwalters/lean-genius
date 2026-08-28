# NONBIP-MIXED divergence 94 audit

Node: the neglected sibling of `SIZE-TWO-EIGENLINE(q)` under
`A-REG-NONBIP / NONBIP-MIXED`: size-two components without the alternating
line, and proper components of normalized size `m >= 3`.

This records the two bounded probes selected after divergence round 94.  It
is a stop report, not a proof of `A-REG`.

## 1. A proper component is a regular packing with prescribed leave

Let `C` be a defect component of order `v = qm`, and let `N_C` be the
`q^2 by qm` zero-one matrix

`N_C(x,y) = 1` iff `G.Adj x y`, for `y in C`.

Every row has sum `m`, every column has sum `q`, and C4-freeness makes two
columns occur together in at most one row.  Restricting

`A^2 = (q-1)I + J - D`

to `C` gives the exact Gram identity

`N_C^T N_C = L(D[C]) + J`.

Thus the ambient neighborhoods form a `1-(qm,m,q)` linear packing whose
leave is exactly the connected `(q-1)`-regular graph `D[C]`.  Since `D[C]`
is connected, the matrix-tree theorem gives

`det(N_C^T N_C) = (qm)^2 tau(D[C])`.

This is a useful q-generic reformulation, but plain parity is nonterminal.
The exact q=4 `[2,2]` control was evaluated for both components.  In each
case:

```text
Smith(N_C)       = diag(1,1,1,1,1,1,1,2),
rank_F2(N_C)     = 7,
tau(D[C])        = 392,              v2(tau) = 3,
det(N_C^T N_C)   = 25088 = 8^2*392, v2(det) = 9,
D[C]             is connected and nonbipartite.
```

So mod-two singularity, odd-regular connectedness, and nonbipartiteness are
fully compatible.  A surviving Smith route would need a genuinely
`q=2^k`, `k>=3`, theorem about higher elementary divisors of this particular
regular packing.  Row/column sums alone do not provide one: the q=4 matrix's
only even invariant factor is `2`, not `q=4`.

The outside literature located on Smith forms concerns graph incidence
matrices, complete designs, or highly symmetric point-subspace designs; no
general theorem found supplies the required higher-2-adic obstruction for
an arbitrary regular uniform packing with a prescribed leave.

### The canonical Hoffman cocliques are real but nonterminal

The post-reveal Hoffman candidate does have its proposed equality witness.
If `x` lies outside `C`, then the `q` blocks

`{N_A(y) intersect C : y in N_A(x)}`

are pairwise disjoint: an intersection point would be a second common
neighbor of two vertices already sharing `x`.  Their total size is `qm`, so
they partition `C`.  Equivalently `N_A(x)` is a `q`-coclique in the proper
owner graph, attaining its Hoffman bound.  Moreover every block belongs to
exactly `q-m` such exterior parallel classes.

This does not manufacture a global q-coloring of the owner graph.  The
parallel classes reuse blocks, and two classes meet in zero or one block
according to the original common-neighbor relation between their indexing
vertices.  In other words their intersection graph reconstructs the same
ambient `A^2`/defect relation; it does not force the leave to split into
cliques or become disconnected.  The literature on resolvable packings
contains abundant constructions with prescribed regular leaves, so Hoffman
equality plus resolvability is not itself an obstruction.  A terminal would
need an additional incompatibility among these multiply-used parallel
classes.

## 2. Bottom-eigenspace fusion is coordinate rank-nullity

For the proper owner

`O_C = A P_C A - mI`,

positive semidefiniteness gives the exact equivalence over `R`

`O_C x = -m x  <->  P_C A x = 0`.

Indeed `x^T A P_C A x = ||P_C A x||^2`.  For any set `S` of components,

`intersection_(C in S) E_{-m_C}(O_C) = ker(P_(union S) A)`.

In particular, fusing all bottom eigenspaces returns `ker A`.  All dimension
inequalities from this observation are ordinary rank-nullity for coordinate
restrictions of the single map `A`; edge-disjointness of the owners does not
turn them into a mixed trace contradiction.  The candidate is stopped until
some non-coordinate constraint on these kernels is named.

## 3. No-eigenline cyclotomic moment transport has the wrong scale

The proposed route was: in the absence of an alternating joint eigenline,
transport every internal cycle mode to the exterior; Galois closure then
forces whole cyclotomic packets, which might overflow an exterior fourth- or
sixth-moment budget.

The q=16 `C6 disjoint-union C26` control gives the quickest scale check.  Its
internal space has only `2q=32` modes, whereas the exterior has
`q(q-2)=224` dimensions.  Even transporting every internal mode once leaves
192 exterior dimensions free.  Since every cycle eigenvalue has absolute
value at most 2, the transported packets contribute at most

```text
32 * 2^4 = 512       to a fourth moment,
32 * 2^6 = 2048      to a sixth moment.
```

By comparison, a C4-free 14-regular graph on 224 exterior vertices already
has fourth closed-walk count

`224 * 14 * (2*14-1) = 84672`.

Thus packet closure with multiplicity one cannot exhaust the exterior moment
budget; it is smaller by orders of magnitude.  The reduced q=16 witness does
carry the alternating line, so it is a scale control rather than a literal
countermodel to the no-eigenline branch.  To reopen the route one must first
prove a multiplicity amplifier (roughly order `q` per internal packet), not
merely Galois closure.

## Disposition

The packing/leave dictionary is retained as the only positive structural
reframe from the round.  The tested consumers are cut:

- F2 rank or spanning-tree parity alone;
- Hoffman equality / existence of exterior parallel classes alone;
- bottom-eigenspace dimension fusion;
- multiplicity-one cyclotomic fourth/sixth moments.

Do not open Lean wrappers for these consequences without, respectively, a
higher-2-adic packing theorem, a non-coordinate kernel constraint, or a
packet multiplicity amplifier with a complete chain to `A-REG`.
