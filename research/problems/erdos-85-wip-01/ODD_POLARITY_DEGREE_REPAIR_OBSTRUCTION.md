# A uniform obstruction to one odd-polarity degree repair

2026-09-08, codex-sol-1, divergence 110. Prose proof, not Lean.
This rules out a specified construction template, not arbitrary odd-degree
regular graphs and not an Erdős-85 branch.

## Root motivation and exact scope

An odd-q regular C4-free graph on an even order N<=q²-3 would give a drop
at N+1. Indeed, a C4-free graph on M<=q²-1 vertices with minimum degree q
has q*deg(v)<=M-1+deg(v) for every vertex, since each neighborhood induces
a matching. Thus deg(v)<=q and the graph is regular. At odd M=N+1 this
contradicts the handshake lemma. A cofinal family of the proposed even-N
witnesses would therefore suffice for the Erdős-85 negation route.

The host tested here is the induced graph on nonisotropic points of the
orthogonal polarity of PG(2,q), q odd. It has q² vertices. Its degrees are
q-1 on a set L and q+1 on a set H. The polarity construction is described
in [Lazebnik–Verstraëte, pp. 7–8](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v10i1r25/pdf/).
The proposed repair deletes vertices, removes H-H edges to lower high
degrees, and adds edges to raise low degrees. Labels L,H refer to the
original host throughout. Every original edge not of type H-H is preserved
unless one of its endpoints is deleted.

**Claim.** After any d>=1 vertex deletions and any removals of H-H edges,
no surviving original nonedge incident with L can be added safely when
q>=2d+9. Every such addition creates a C4. In particular the proposed
repair fails after three deletions for every odd prime power q>=17.
It cannot attain degree q: surviving L vertices still have degree at most
q-1 and cannot receive a permitted new edge. Their original number is
q(q+1)/2, greater than d in the stated range.

Other edge removals or different hosts are outside this statement.

## Field and neighborhood facts

Let B be the full polarity incidence matrix, retaining loops exactly at
isotropic points. Projective-plane incidence gives

    B²=qI+J,  B1=(q+1)1,  B³=qB+(q+1)J.

A nonisotropic point x has zero or two isotropic neighbors: its orthogonal
plane is respectively anisotropic or hyperbolic. Hence the induced
nonisotropic degree is q+1 or q-1.

For x in L, its orthogonal plane is hyperbolic. In an isotropic basis,
the q-1 nonisotropic projective points have representatives (1,t), t!=0,
and norm c*t for a fixed nonzero c. Exactly half have each square class.
The type L/H of a nonisotropic point u depends only on the square class
of its norm: the orthogonal plane to u is isotropic exactly when
-Delta/Q(u) is square, where Delta is the ambient determinant square
class. Consequently x has exactly (q-1)/2 neighbors in H. This argument
works in every odd finite field, not only prime fields.

## Count surviving paths

Fix nonadjacent x,y in L. Since B_xy=0, there are q+1 length-three
incidence walks from x to y in B.

Deleting all isotropic vertices destroys at most four walks. There are
two isotropic neighbors of each endpoint; fixing the first internal
vertex gives at most one second vertex, by the unique-common-neighbor
identity B²=qI+J. The same argument applies to the last internal vertex.
Double counting destroyed walks only weakens this upper bound.

Now delete *all* H-H edges, which is stronger than any allowed H-H edge
removal. Such an edge can occur only as the middle edge of a path from
L to L. There are at most (q-1)/2 walks of this kind, one for each H
neighbor of x, again using uniqueness of the second internal vertex.
The surviving loopless walks are simple because x,y are nonadjacent.
Their number is therefore at least

    q+1-4-(q-1)/2 = (q-5)/2.

For a fixed nonadjacent endpoint pair in a C4-free graph, each other
vertex lies on at most two simple length-three paths: at most one in
each internal position. A vertex appearing in both positions belongs to
N(x) intersect N(y), which has size at most one. Thus d>=1 deletions
destroy at most d+1 paths (the sum of internal appearances bounds the
number destroyed). This sharpening is due to codex-sol-3. The number left
is at least

    (q-5)/2-d-1 >= 1    when q>=2d+9.

Adding the edge xy closes any surviving path to a C4. Simultaneous
permitted additions cannot remove this existing obstruction.

## Cross-type additions are obstructed too

For nonadjacent x in L and y in H, the same incidence identity gives q+1
walks. Removing absolute points destroys at most two: y has no absolute
neighbors. The anisotropic plane y-perp contains (q+1)/2 points of each
norm square class, hence y has exactly (q+1)/2 H neighbors. To see the
class count, identify the anisotropic form with a nonzero scalar times
the norm from F_(q²) to F_q. Half the nonzero vectors have norm in each
square class, since the norm is surjective with fibers of size q+1;
quotienting by nonzero F_q scalars preserves norm square class and divides
both counts by q-1.

Every walk destroyed by removing H-H edges has its last internal vertex
in H: this is true for an H-H middle edge as well as an H-H final edge.
Each such last vertex determines at most one first internal vertex.
At least (q-3)/2 paths therefore survive, and d deletions destroy at most
d+1 of them. This leaves a path for q>=2d+7, in particular throughout the
main claim's range q>=2d+9. This extension was proposed by codex-sol-3
and independently checked by sol-1. Together with the L-L case, it blocks
every new edge incident with a surviving L vertex, even if arbitrary
edge additions are allowed. Adding H-H edges cannot remedy its deficit.

## Executable calibration and limits

`verify_odd_polarity_degree_repair.py` independently builds prime-field
hosts, checks all pair codegrees, low/high degrees and the low-to-high
neighbor count, then counts paths after removing all H-H edges. At q=19,
all 17,100 low-low nonedges retain at least ten paths, more than the
uniform lower bound seven. The path-incidence bound is checked explicitly,
including that at most one vertex appears twice; deletion of any three
vertices leaves a path without enumerating all three-vertex subsets.

Finite prime-field checks calibrate the implementation. The field and
path-count arguments above establish the uniform prime-power statement.
This stops this construction template; no graph-existence or A-REG
nonexistence claim is promoted.

## Two fixed degree-seven hosts: deletion-only repair also fails

The separate verifier `verify_48_pair_deletion_repair.py` checks the Boza
48-vertex witness and graph index 9 in the Afzaly–McKay archive, with both
input files pinned by SHA-256. Each host has degree seven and pair
codegrees at most one. For each of the 1,128 deleted vertex pairs in each
host, every surviving nonedge between vertices of degree below seven has
an explicit simple length-three path. Thus none can be added without a C4.

An addition-only restoration to degree seven could only join such deficit
vertices, so these two hosts cannot yield a 46-vertex witness by two
vertex deletions and edge additions alone. There are 168 deletions with
total degree deficit 12 and 960 with deficit 14 in each host. Sol-1 read
and independently executed the verifier; directed review #1485 passed.
The verifier is banked in commit `e1fa23d235`.
Further edge deletions and other hosts remain outside this finite audit.
