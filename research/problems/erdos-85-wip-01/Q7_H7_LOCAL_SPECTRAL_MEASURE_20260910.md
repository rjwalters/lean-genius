# H7 local spectral measures — 2026-09-10

Owner: codex-sol-3. Passed independent paper/arithmetic review1608 by codex-sol-2. This is an
exact non-obstruction for a stronger relaxation of the reviewed H7 rational
moment measure. It is not an integral spectrum, matrix, or graph witness.

## Local diagonal constraints

For H7/T0 let U have columns 1,t. The reviewed block identities give

    G = U^T U = [[42,56],[56,98]],
    C U = U A,  A = [[7,7],[-1,0]],
    D U = U(A-I).

The zero eigenspace of C is B^T(1^perp). Its orthogonal projector has diagonal
 t(7-t)/49: use BB^T=7I+J and subtract the projector onto B^T1=t.
The complementary two-dimensional fixed space is span(1,t); hence at a
vertex of support t its contribution to the k-th C moment is

    q_k(t) = [1,t] A^k G^-1 [1,t]^T.

The residual projector has diagonal 1-t(7-t)/49-q_0(t). For k>0 subtract
q_k from (C^k)_vv. Simplicity and C4-freeness give

    C_vv=0, (C²)_vv=7-t, (C³)_vv=2 tau,
    (C⁴)_vv=(7-t)²+6(7-t)-7.

For the last identity, expand the fourth closed walks as d_v² plus
sum over C-neighbors w of (d_w-1), using Ct=7 and absence of C4.
Thus the local residual moments are:

| t | m0 | m1 | m2 | m3 | m4 |
| --- | --- | --- | --- | --- | --- |
| 0 | 9/10 | -3/10 | 28/5 | 2tau-77/10 | 399/10 |
| 1 | 208/245 | -11/70 | 51/10 | 2tau-26/5 | 349/10 |
| 2 | 369/490 | -9/70 | 22/5 | 2tau-33/10 | 291/10 |

On the residual space, CD²=C⁵-12C³+36C. On the fixed space its diagonal
is [1,t] A(A-I)² G^-1 [1,t]^T. Therefore the actual local overlap is

    (CD²)_vv = m5 + c_t - 24 tau,
    (c_0,c_1,c_2)=(434/5,603/10,186/5).

The [reviewed isolation bound](Q7_LOCAL_DEFECT_OVERLAP_BOUND_20260910.md)
imposes 0 <= (CD²)_vv <= 2 ex(C4,t+2tau-1), where the ex table for orders
0..5 is (0,0,1,3,4,6). The allowed tau ranges are 1..3,0..2,0..1.
These identities are paper derivations; no new graph theorem is claimed Lean.

## Exact compatibility of the fixed seven-node measure

The attached rational weights split the [reviewed global measure](Q7_H7_FIFTH_MOMENT_RELAXATION_20260910.md)
into the following local types. A group's weights sum the spectral measures
of all vertices of that type, so its target moments are count times the
local row above.

| t | tau | number of vertices | overlap at each vertex | aggregate overlap |
| --- | --- | --- | --- | --- |
| 0 | 2 | 1 | 4 | 4 |
| 0 | 3 | 6 | 12 | 72 |
| 1 | 0 | 4 | 0 | 0 |
| 1 | 1 | 10 | 2 | 20 |
| 2 | 0 | 21 | 0 | 0 |

Other allowed types have count zero. Counts sum to the required census
(7,14,21), and triangle incidences sum to30, so T=10. All weights are
nonnegative, every group's moments0..4 agree exactly, each local overlap
is an even integer satisfying its upper bound, and the overlap totals96. Column sums
recover the original seven-node measure, preserving its global moments
through5 and strict residual intervals.

The Fraction-only verifier checks these assertions without an optimizer.
Discovery used a bounded linear feasibility problem followed by integer
local-type counts, with local overlap further split into its allowed even
values. This gives25 local types on the fixed seven nodes. An exact rational
reconstruction verifies the result; no numerical infeasibility is asserted.
No graph or full-spectrum search was performed. The integer counts do not
make the spectral weights integer. Dividing group weights by its count
gives a nonnegative local measure with the required moments at each vertex
in that group, including its even integer overlap. Off-diagonal projector
compatibility, orthogonality, and a common 0/1 adjacency matrix remain
unimposed. The rational noninteger nodes are not an integral spectrum.

This closes only the tested local-moment relaxation as an exclusion of the
fixed continuous measure. It supplies no surviving actual graph and no
reason to extend scalar moments without an additional structural condition.
