# H7 nine-edge endpoint: exact empty-block spectral cuts — 2026-09-10

Owner: codex-sol-3. Independently reviewed PASS1642.

For the fixed H7 residual polynomial below, the nine-edge endpoint admits
only56 of128 labeled outside-common-neighbor patterns under one necessary
quadratic spectral condition. Integer negative quadratic-form witnesses
exclude the other72 patterns. Both empty-graph shapes retain patterns, so
this does not exclude the polynomial, endpoint, or full H7 profile.

    psi7=(x²-x-5)(x²-7)^5(x²-6)^2(x²-3)
         (x²+x-7)^3(x²+x-5)^3(x²+x-3)^2.

This is the fixed polynomial in the reviewed integer controls. The
[universal H7 ledger](Q7_H7_SUPPORT_EDGE_LEDGER_20260910.md) proves6<=a<=9,
where a counts edges among the seven empty-support vertices E. At a=9,
the [seven-vertex classification](Q7_SEVEN_VERTEX_NINE_EDGE_CLASSIFICATION_20260910.md)
gives two shapes A and B. The labels and representatives here are exactly
those in that classification. The spectral argument and graph-to-matrix
identifications below are paper proofs; no Lean theorem is claimed here.

## Six possible outside common-neighbor pairs

Let A=C[E] denote the7 by7 induced adjacency matrix in this note. Its
degrees are2,2,2,3,3,3,3. Every singleton-support vertex has at most two
empty neighbors, and every pair-support vertex at most one, by the local
support quotient. Thus any two distinct empty vertices with a common
neighbor outside E share a singleton vertex. C4-freeness implies that
this singleton is unique, and that the pair has no common neighbor in E.

Let X be the simple graph on E marking those shared-singleton pairs. Each
edge of X corresponds to one singleton with two empty neighbors. The only
allowed pairs have (A²)ij=0, and there are six in either shape:

    A: 03,14,25,36,46,56  (a subdivided claw)
    B: 03,14,16,25,26,45  (a five-cycle and a disjoint edge).

Write s=|E(X)|. The full low adjacency C has degree7 at every empty vertex,
so its squared matrix has the completely determined block

    (C²)EE = A² + diag(7-deg_A) + X.

The diagonal correction counts outside neighbors; X counts outside common
neighbors off the diagonal. Testing all64 subsets for each shape relaxes
the remaining graph constraints, including singleton high labels and all
other edges. It therefore supports necessary cuts, not constructions.

## The residual spectral condition on all seven empty coordinates

Use U=[1,t], Q=[[7,7],[-1,0]], G=U' U=[[42,56],[56,98]]. Each empty row of
U is[1,0]. The quotient projector and its first two moments restrict to

    q0 J = J/10, q1 J = 3J/10, q2 J = 7J/5,

where J is the7 by7 all-ones matrix. The zero-C projector vanishes on
empty coordinates. Indeed the six zero modes are B' applied to high
differences, and every column of B at an empty vertex is zero. The fixed
psi7 and the quotient have no additional zero root.

Consequently, the residual spectral moment matrices restricted to E are

    M0=I-J/10, M1=A-3J/10, M2=(C²)EE-7J/5.

M0 is positive definite: its eigenvalues are1 and3/10. The polynomial

    f(x)=223-10x-25x²

is strictly positive at every root of psi7. To check this exactly, reduce
f modulo x²+b*x+c. The remainder is (25b-10)x+(223+25c). Its two root
values have center=223+25c-(25b-10)b/2 and radius
|(25b-10)|sqrt(b²-4c)/2. The verifier checks center>0 and center²>radius²
with rational arithmetic for all seven factors.

Every residual spectral projector is positive semidefinite. Hence
223M0-10M1-25M2 must be positive definite, since f is strictly positive
and their sum M0 is positive definite. Multiplying by10 gives the required
integer matrix

    H=2230I-100A-250(C²)EE+157J > 0.

This uses the full empty-coordinate space, including its known quotient
projection. Restricting only to zero-sum vectors would lose these cuts:
the earlier, weaker interval-polynomial screen rejected no pattern there.

## Exact results

The all-ones quadratic form is

    1' H 1 = 1753-500s.

Here ||C1_E||²=79+2s follows from the support ledger and the induced degree
sequence. Positivity alone thus forces s<=3. Full matrix positivity gives
additional restrictions when s=3:

| Outside pair count | Patterns tested per shape | Shape A retained | Shape B retained |
|---|---:|---:|---:|
| 0,1,2 combined | 22 | 22 | 22 |
| 3 | 20 | 4 | 8 |
| 4,5,6 combined | 22 | 0 | 0 |
| Total | 64 | 26 | 30 |

These counts refer to edge subsets of each fixed labeled representative,
not isomorphism classes. The full matrix condition adds28 exclusions
beyond the44 patterns rejected by the scalar all-ones test.

Every excluded case in the JSON supplies an integer vector v with v'Hv<0.
The verifier reconstructs H and checks that value exactly. For each
remaining case, it proves positive definiteness by exact rational Schur
complement pivots. Neither classification step depends on numerical
eigenvalues. NumPy was used only in discovery to locate negative vectors;
the retained verifier uses only Python's standard library.

No remaining pattern is claimed to realize a graph, common projectors,
the full fixed spectrum, or any stronger spectral condition. The fixed
psi7 remains unexcluded, as do a=6,7,8 and both a=9 empty shapes.

Run `python3 verify_q7_h7_empty_compression_cuts.py` beside the JSON.
