# H7 nine-edge endpoint: missing-pair high-label ledger

Owner: codex-sol-2. Independent review #1647: PASS (codex-sol-1).

At the H7/T0 endpoint a=9, the three pair-support vertices with no empty
neighbor determine a three-edge graph U on the seven high labels. The two
singleton vertices at label i have a total of exactly 1+degree_U(i) empty
neighbors. This gives a small label constraint that can be combined with
the reviewed fixed-spectrum empty-pair capacity refinement.

The label identity and local table below are universal H7/T0 necessary
conditions. Only the final restrictions using shape A's s<=2 or shape B's
s<=3 assume the fixed psi7 from the compression note. No full profile or
shape is excluded, and no compatible label assignment is constructed here.

## Graph-to-label identity

The H7/T0 high supports consist of one pair vertex for each of the 21 pairs
of high labels, two singleton vertices for each high label, and seven empty
vertices E. High vertices are independent, and each two distinct high
vertices have exactly one common low neighbor. These are the established
H7 support quotient facts; the actual singleton copies and their capacities
are formalized in `Erdos85OrderFortyNineSevenHighT0SingletonCopies.lean` and
`Erdos85OrderFortyNineSevenHighT0SingletonCopyCapacity.lean`.

The universal edge ledger gives 18 edges from E to pair-support vertices
at a=9. A pair-support vertex has at most one empty neighbor. Thus exactly
18 of the 21 pair vertices have one empty neighbor and three have none.
Let U contain precisely the three high-label pairs corresponding to the
latter vertices.

Every empty vertex has exactly one common neighbor with each high vertex
(the relevant entry of BC=J). Summing this cover over seven empty vertices,
for a fixed label i, gives seven incidences. Of the six pair vertices
containing i, exactly 6-degree_U(i) contribute one incidence. Therefore,
if a_i and b_i are the numbers of empty neighbors of the two singleton
vertices at label i,

    a_i + b_i = 7 - (6-degree_U(i)) = 1+degree_U(i).

The copywise capacity gives 0<=a_i,b_i<=2, hence degree_U(i)<=3.
Their total incidence is sum_i(1+degree_U(i))=7+6=13, agreeing with the
E-to-singleton edge ledger. This is a count of actual singleton vertices;
the two copies with the same label are not identified.

Let k_i count the singleton vertices at label i having two empty neighbors.
Each such singleton supplies one edge of the outside-common-neighbor graph
X on E. C4-freeness makes these edges distinct. Thus s=|E(X)|=sum_i k_i,
and the complete local arithmetic table is

| degree_U(i) | Possible (a_i,b_i), up to order | k_i |
|---|---|---|
| 0 | (0,1) | 0 |
| 1 | (0,2), (1,1) | 1 or 0 |
| 2 | (1,2) | 1 |
| 3 | (2,2) | 2 |

Edges of X inherit their singleton's high label. Two edges of X with the
same label have disjoint endpoints: otherwise an empty vertex would have
two common neighbors with that high vertex. This is a further necessary
color constraint, not imposed in the scalar table below.

## Five missing-pair shapes and conditional consequences

A simple graph with three edges has exactly five possible nontrivial
shapes, with isolated vertices added to reach seven vertices. A cycle must
be a triangle; an acyclic connected three-edge component is P4 or K1,3;
the remaining edge-component splits are P3+K2 and 3K2. Their degree
sequences distinguish these five shapes.

| U shape | Scalar possibilities for s | With shape A and fixed psi7 | With shape B and fixed psi7 |
|---|---|---|---|
| 3K2 | 0..6 | 0..2 | 0..3 |
| P3+K2 | 1..5 | 1..2 | 1..3 |
| P4 | 2..4 | 2 | 2..3 |
| K1,3 | 2..5 | 2 | 2..3 |
| K3 | 3 | impossible | 3 |

The last two columns intersect only the scalar s ranges proved in
`Q7_H7_EMPTY_PAIR_CAPACITY_20260910.md` (review #1645). They do not assert
that every listed combination has compatible colored edges, projectors,
or a full graph realization. In particular, shape A with the fixed psi7
cannot have U=K3. If U=K1,3 in that shape, the two X edges come from the
two singleton copies at the star center and must be disjoint.

The verifier checks all choose(21,3)=1330 labeled three-edge graphs and all
local choices a_i,b_i in {0,1,2}. The five labeled counts are 105,630,420,
140,35 for 3K2,P3+K2,P4,K1,3,K3 respectively. It verifies only the small
label degree arithmetic and scalar intersections, not full assignments.

Run `python3 verify_q7_h7_missing_pair_label_ledger.py`. It uses only the
standard library. This ledger does not address a=6,7,8.
