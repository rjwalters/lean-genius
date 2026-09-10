# H7 support-class edge ledger — 2026-09-10

Owner: codex-sol-3. Paper and arithmetic independently reviewed PASS1634.

Every graph in the designated H7/T0 sector has a single integer a in
{6,7,8,9} controlling all six edge counts between low support classes.
This is independent of any proposed residual characteristic polynomial.
It is a necessary condition, not a sector exclusion or graph construction.

The local support laws and the one-parameter ledger already have actual-
graph Lean proofs in `Erdos85OrderFortyNineSevenHighT0LocalQuotientCapacity`,
`Erdos85OrderFortyNineSevenHighT0GlobalQuotientBridge`, and
`Erdos85OrderFortyNineSevenHighT0GlobalQuotientParity`. In particular,
`sevenHigh_t0_internalEmptyEdge_parameter_bounds` gives6<=a<=10.
The new step here is excluding a=10; the rest restates those existing
constraints in undirected edge notation.

Write L_i for lows having i high neighbors. Their sizes are7,14,21 for
i=0,1,2. Let e_ij count C-edges between L_i and L_j, counting internal
edges once, and set a=e_00. Then:

| a | e00 | e01 | e02 | e11 | e12 | e22 |
|---|---|---|---|---|---|---|
| 6 | 6 | 25 | 12 | 10 | 39 | 27 |
| 7 | 7 | 21 | 14 | 14 | 35 | 28 |
| 8 | 8 | 17 | 16 | 18 | 31 | 29 |
| 9 | 9 | 13 | 18 | 22 | 27 | 30 |

## Local support counts

Use the reviewed actual-graph identities C1=7*1-t and Ct=7*1.
For a vertex v with t_v=i, let n_j(v) count its C-neighbors in L_j.
Thus

    n0+n1+n2=7-i, n1+2*n2=7,
    n2=n0+i, n1=7-2*n0-2*i.

Nonnegativity gives n2<=3 and n0<=3-i. In particular, C[L0] has maximum
degree3, every single-support vertex has at most two empty neighbors,
and every pair-support vertex has at most one empty neighbor.

Summing n2=n0+i separately over each class and then using the class
degree sums gives

    e02=2a,
    e01=49-4a,
    e12=e01+14=63-4a,
    e11=4a-14,
    e22=a+21.

Since e01<=2*14, a>=6. Since e02<=21, a<=10.

## Why a=10 is impossible

A simple graph on seven vertices of maximum degree3 with ten edges has
six degree3 vertices and a unique degree2 vertex u: its degree deficit
from the all-degree3 sequence totals one. Some degree3 vertex v is not
adjacent to u, since u has only two neighbors. All three neighbors of v
then have degree3.

In a C4-free graph, the graph induced on N(v) is a matching. There are
therefore at most one internal edge and at most two incidences used up
by that edge. The neighbors of v have six incidences besides their
three edges to v, leaving at least four incidences to vertices outside
{v} union N(v). Those outside endpoints must be distinct: any shared
endpoint gives a four-cycle through v. The graph consequently has at
least1+3+4=8 vertices, a contradiction. This proves a<=9.

The companion Python verifier checks the finite degree-deficit cases and
count arithmetic, plus explicit small graphs illustrating the scope. The
graph argument is separately formalized: the independently reviewed
`Erdos85SevenVertexSubcubicBound` (PASS1635) proves the generic upper9
bound. `Erdos85OrderFortyNineSevenHighT0EmptyEdgeNine` transfers the actual
empty-neighbor capacity to the induced graph and proves
`sevenHigh_t0_internalEmptyEdge_parameter_bounds_nine`, under the original
Fin49/C4-free/minimum-degree7/seven-high/no-triple assumptions. Its public
build passes, both exported lemmas use only `propext`, `Classical.choice`,
and `Quot.sound`. Independent wrapper review1636 passed.

## Exact checks and scope

The verifier reconstructs all possible local count triples for each
support class, checks the table against all class degree and support
equations, and verifies the maximum-degree and deficit counts used above.
It also checks explicit C4-free subcubic graphs on seven vertices with
6,7,8,9 edges. These witnesses show that the induced-empty-graph edge range
alone cannot be narrowed. They do not realize the rest of the H7 graph or
any of the six-count tables jointly.

For the fixed H7 polynomial, an alternative spectral argument using the
empty-class indicator and rational residual-root interval[-16/5,14/5]
also rejects a=10. It is redundant with the universal argument above and
is not an additional polynomial exclusion. No spectral assumption is
used in the retained edge ledger.

Run `python3 verify_q7_h7_support_edge_ledger.py`.
