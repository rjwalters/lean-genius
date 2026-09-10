# Exact H5 local measures respecting quadratic conjugation — 2026-09-10

Owner: codex-sol-2. Base moments0..6 independently reviewed PASS1625. Pure-C degree10 extension independently reviewed PASS1628. Mixed-moment extension and rank-one boundary review pending.

The fixed H5 polynomial from the independently reviewed
[integer controls](Q7_H5_H7_INTEGER_SPECTRAL_CONTROLS_20260910.md) admits the
local measures below for each of its three support censuses. The retained
verifier uses exact rational arithmetic, without an optimizer. This checks
local moments and global multiplicities, not a graph or a common matrix.

The polynomial is

    (x-3)^2(x+3)^2(x²-6)^8(x²-3)^2
    (x²+x-7)^4(x²+x-4)^2(x²+x-3).

It has T=19 all-low triangles, mixed overlap R=16 and tr(D³)=18. Consequently
the local triangle-incidence, overlap and defect-triangle-incidence totals
are respectively57,16,9. There are8,8,10 groups in the witnesses for triple
support count0,1,2. Their support censuses are

    (14,20,10,0), (13,23,7,1), (12,26,4,2).

## Exact local targets

Write t for high support size, tau for the all-low local triangle count,
r for the local mixed overlap (CD²)vv, and delta for the number of defect
triangles through the vertex, so (D³)vv=2delta. On the two-dimensional
quotient U=[1,t], set

    Q=[[7,5],[-1,0]], G=U' U=[[44,40],[40,60]],
    qk=[1,t] Q^k G^-1 [1,t]', z=t(5-t)/35.

Here z is the diagonal of the zero-C projector coming from high differences.
The residual moments m0,...,m6 are

    m0=1-q0-z, m1=-q1, m2=7-t-q2,
    m3=2tau-q3, m4=(7-t)(13-t)-5-q4,
    m5=r+12m3-36m1-q3+2q2-q1,
    m6=216m0-108m2+18m4+q3-3q2+3q1-q0-z-2delta.

The fourth moment uses C4-freeness of C: its diagonal is d² plus the sum
of neighbor degrees minus d, with d=7-t and Ct=5. The fifth and sixth
identities use D=6I-C² on the residual space, D=C-I on U, and D=-I on the
zero-C space. Thus the sixth target includes the zero-mode term -z.

Each group meets the local conditions

    indicator(t=0)<=tau<=3-t,
    r even, 0<=r<=2 ex(C4,t+2tau-1),
    0<=delta<=choose(6-t,2),

where the already reviewed small extremal table is0,0,1,3,4,6 for orders0..5.
The verifier checks every moment0..6, integer census, and all three totals.
These formulas remain paper-level graph identifications; this artifact is
an exact arithmetic measure verification, not a Lean formalization.

## Conjugate weights rather than independent irrational nodes

For a quadratic x²+b x+c, let Delta=b²-4c and lambda±=(-b±sqrt(Delta))/2.
Choose a positive rational rho with rho²<Delta. The witness gives two
nonnegative rational coefficients u,v, interpreted as masses on two
rational moment columns

    column±(k)=(lambda+^k+lambda-^k
                 ±rho*(lambda+^k-lambda-^k)/sqrt(Delta))/2.

The actual eigenvalue weights are

    w+ = (u+v)/2 + rho*(v-u)/(2sqrt(Delta)),
    w- = (u+v)/2 - rho*(v-u)/(2sqrt(Delta)).

They are conjugate in Q(sqrt(Delta)) and nonnegative. If u+v>0, both are
strictly positive, since rho<sqrt(Delta). Thus one conjugate weight cannot
vanish alone. All column moments are rational, obtained by the quadratic
recurrence; the verifier never relies on numerical roots. The two columns
for a factor of multiplicity m each have total coefficient m across the
44 low vertices. This makes each actual eigenvalue's global weight exactly
m. Linear-factor columns have their specified integral eigenvalues.

Weights in the JSON are group totals. Dividing by the positive group count
assigns a measure to each vertex of that type. No individual label or edge
is assigned by doing this.

## Scope and bounded discovery

A numerical screen examined243 possible local types;111 passed. Three
bounded integer allocation calls (three-second limits) found allocations
with the scalar totals, and three more checked global multiplicities.
Replacing each quadratic pair by the rational columns above gave three
further bounded calls. For their positive-count groups, an LP support was
reconstructed by exact rational Gaussian elimination; all equalities and
nonnegativity were verified exactly. The retained verifier checks only the
three fixed witnesses and has no SciPy dependency or search step.

These witnesses show that the specified diagonal tests, even with quadratic
conjugation and exact global multiplicities, do not reject this fixed H5
polynomial in any support profile. They do not construct off-diagonal
projectors, rank or orthogonality of projector matrices, a common symmetric
integer C/D representation, the residual lattice, 0/1 entries, or the
actual support-edge incidences. The finite mixed-moment tests and the rank-one limitation added below do
not constitute a joint matrix construction. In particular the simple
quadratic factor has not been realized as two rank-one projectors.
No graph existence or complete H5 profile exclusion follows.


## Degree10 diagonal integrality extension

The saved weights have been replaced by exact rational solutions that also
make every individual vertex's full-C diagonal moments0..10 nonnegative
integers. For k>0 odd, the diagonal is even. For k=2j it has parity
(C^j 1)v=[1,t] Q^j [1,0]'. This follows from the characteristic-two diagonal
identities for symmetric adjacency matrices. The verifier checks these
conditions directly, dividing group weights by their integer count. It
retains all earlier moment targets, census totals and global multiplicities.

The original degree6 witnesses failed higher integrality; they were only
claimed at degree6. Three bounded calls with degree7/8 conditions and three
with degree7..10 conditions produced new supports, each reconstructed and
verified exactly. A further three bounded calls through degree14 reported
numerical infeasibility for the fixed group counts and inner cones. That
restricted, uncertified result is not a polynomial or graph exclusion.
No claim is made about diagonal integrality beyond10 in the saved witness.


## Mixed-moment extension and a rank-one boundary

The n3=2 allocation and its weights have been replaced again, removing a
negative D5 diagonal of the previous pure-C witness. Profiles0/1 retain
their weights. All three now pass exact nonnegative integral diagonals
C^i D^j for i+2j<=10 (36 pairs). Opposite-parity i,j give even diagonals.
The verifier also checks D4>=61-16t+t², from defect degree6-t and Dt=5-t.
The new n3=2 witness has10 groups; profiles0/1 still have8 each.

These particular assignments nevertheless fail a necessary joint-projector
condition. The factor x²+x-3 is simple, so each conjugate eigenprojector
would have rank one. For an integer symmetric C, an eigenvector for this
factor can be chosen over K=Q(sqrt13). Its nonzero diagonal projector
weights are y_v²/(sum y_u²); hence ratios of nonzero weights must be squares
in K. Taking field norms, their rational norm ratios must be squares in Q.

For the last two cone coefficients u0,u1 of a group of count n, put

    A=(u0+u1)/(2n), B=rho*(u1-u0)/(26n).

The plus eigenvalue weight is A+B sqrt13, with rational norm A²-13B².
The verifier finds a nonsquare positive rational ratio of these norms in
each profile, using integer square roots of numerator and denominator.
This exactly rules out rank-one projector realization of each saved
assignment. It does not rule out other weights, the polynomial, or H5.
Thus the artifact records both compatibility with the listed local tests
and a demonstrated limitation when those data must share projectors.
