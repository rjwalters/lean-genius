# A-REG Baer involution coupling audit

Status: q-generic structural audit under `A-REG-NONBIP`, 22 August 2026;
exact transport laws banked, no terminal contradiction.

## Exact partial involution

Let `A` be the symmetric incidence matrix of a self-polar `(q^2_q)`
configuration and assume first that it has no absolute points, so `A` is the
adjacency matrix of a simple graph `G`.  Put

```text
D = secondOrderDefectGraph G,
T = A ∩ D = triangleFreeEdgeGraph G.
```

Fix a point `P` and its polar line `p = N_A(P)`.  For `X in p`, the two
polar lines `p` and `pi(X)` both contain a point exactly when `P,X` have a
common neighbor.  C4-freeness makes that point unique.  Hence

```text
iota_P(X) = the unique point in p ∩ pi(X)
```

is defined precisely on

```text
N_A(P) \ N_T(P).
```

It is an involution: if `iota_P(X)=Y`, uniqueness also gives
`iota_P(Y)=X`.  With no absolute points it has no fixed point.  Therefore

```text
q - deg_T(P) is even.                                  (1)
```

For binary `q`, (1) says that every degree of `T` is even.  This is exactly
the content already proved, without polarity language, by
`binarySquare_regular_triangleFree_degree_even`.  Thus the naive Baer
involution supplies no new consequence to A-REG.

With absolute points allowed, the fixed points of `iota_P` are exactly the
absolute points on `p`, while `T`-neighbors are never absolute.  The general
residue is only

```text
# absolute points on pi(P) ≡ q - deg_T(P)  (mod 2).     (2)
```

## Why defect connectivity does not yet couple

The involutions see only `T=A∩D`; the hypothesis in the proposed Baer-type
theorem is connectivity of all of `D`.  A path witnessing connectivity may
use only edges of `D\T`, and such an edge never occurs in the domain or the
broken set of any `iota_P`.  Consequently

```text
D connected + T Eulerian
```

has no contradiction.  At the reduced level, take any connected
nonbipartite `(q-1)`-regular graph `D` on `q^2` vertices (for example the
circulant controls in `generic_connected_defect_spectral_countermodel.py`)
and set `T` empty.  Every local involution output (1), every `T` cut parity,
and connectivity of `D` hold simultaneously.  This is deliberately not an
ambient incidence realization; it proves that a port cannot use connectivity
and the local involution conclusions as black boxes.

The missing bridge must force `T` to detect a `D`-cut or `D`-path.  A useful
statement would have to resemble one of:

- every nontrivial involution-orbit cut of `D` contains a `T` edge;
- some canonically defined `D` cut contains an odd number of `T` edges; or
- `D\T` cannot connect all partial-involution orbits.

The second form would immediately contradict the Eulerian cut law, but none
of these statements follows from the current APIs.  They are the exact
design-level input a successful Baer port still needs.

## Matching-repair control

The affine-polarity control has `q` absolute points and disconnected
`D=q K_q`.  The most direct fixed-point-free repair deletes its `q` diagonal
incidences and replaces them by a perfect matching on the absolute points.
This preserves symmetry and q-regularity and makes the resulting defect
graph connected, but it destroys C4-freeness.

`affine_polarity_matching_repair.py` exhausts every perfect matching at
`q=4` and `q=8`.  For every matching it finds exactly

```text
q(q-1)
```

unordered point pairs with two common neighbors.  Thus this natural repair
crosses from the classical disconnected/absolute model to a connected,
fixed-point-free object only by violating the unique-intersection axiom in a
uniformly large family.  It is not a counterexample to A-REG; it is a control
showing that the missing coupling is precisely nonlinear incidence
compatibility, not parity or connectivity alone.

## Exact affine-completion criterion

The classical Baer proof pinpoints the missing axiom.  On a non-absolute
line of a projective plane, every point is sent to the intersection of that
line with its polar line.  Unique line intersection makes this a total
involution, and the odd line size in even order forces a fixed point.  In
the present `(q^2_q)` configuration the line has even size q and the map is
undefined exactly at the T-neighbors.  One cannot repair this by formally
adding the omitted intersections unless the whole configuration is already
affine-completable.

Here is the exact criterion.  Regard the q-subsets `N_A(x)` as the current
lines.  A family `L_infinity` of q further q-subsets completes them to a
`2-(q^2,q,1)` affine plane precisely when

```text
L_infinity is a partition of V into q sets,
and each set is a q-clique of D.                         (3)
```

Indeed, two points lie on a current line exactly when they have a common
A-neighbor, equivalently when they are not adjacent in D.  Thus every pair
on a new line must be a D-edge.  Each point is short of exactly one line,
so the q new lines must partition the q^2 points.  Conversely, a partition
into q D-cliques supplies the unique missing line for every D-pair, while
the current C4-free incidence supplies the unique line for every non-D
pair; the standard affine-plane parameters then follow.

But a q-clique of D is a whole D-component by the already proved clique
isolation theorem.  Consequently

```text
the configuration is affine-completable
  iff D is the disjoint union of q copies of K_q.          (4)
```

The affine-polarity control realizes exactly this case.  A connected D on
q^2>q vertices admits no such completion.  Therefore the projective-plane
Baer proof cannot be ported by adjoining an ideal parallel class: the
connectivity hypothesis destroys precisely the completion needed to make
the local involutions total.

This also identifies the strongest plausible Baer-type rigidity statement:

> For `q=2^k`, `k>=3`, every fixed-point-free self-polar `(q^2_q)` linear
> configuration is affine-completable (equivalently, `D=q K_q`).

That statement would immediately prove `NONBIP-CONNECTED`, and the exact
q=4 control shows why the `k>=3` hypothesis is indispensable.  It remains
unproved; (3)--(4) reduce it to a concrete missing-line partition theorem
rather than an analogy with projective planes.

## A canonical odd-degree overlap graph

The failed parallel-class completion nevertheless leaves a global parity
object that is stronger than the vertexwise statement (1).  Retain the
incidence-bottleneck matrix

```text
E = AD - (J-A) = A 1_{N_D[.] } - 1.
```

For distinct points `P,Y`, put an edge `PY` in `Omega` when `E(P,Y)` is odd.
This is a simple graph because `E` is symmetric.  Its entries have the direct
almost-parallel-class interpretation

```text
E(P,Y) = 0                                      if Y in N_A(P),
E(P,Y) = |N_A(Y) intersect N_D(P)| - 1          otherwise.       (5)
```

Indeed, the `q-1` lines `N_A(X)`, for `X in N_D(P)`, all avoid the polar line
`N_A(P)`.  They have `q(q-1)` incidences in total, exactly the size of its
complement.  Thus (5) records occupancy minus one: holes have value `-1`,
single covers value zero, and multiple covers positive value.  Commutation
`AD=DA` is precisely the reciprocity of these occupancies in `P,Y`.

The diagonal is

```text
E(P,P) = deg_T(P) - 1,                           (6)
```

because `N_A(P) intersect N_D(P)` is the set of `T`-neighbors of `P`.
For binary `q`, the partial Baer involution makes `deg_T(P)` even, so every
diagonal entry of `E` is odd.  On the other hand every row of `E` sums to
zero.  Reducing a row modulo two therefore proves the new global law

```text
deg_Omega(P) is odd for every P.                 (7)
```

Equivalently, for every vertex set `S`,

```text
|delta_Omega(S)| = |S|  (mod 2).                 (8)
```

There is also an exact vertexwise coupling to `D`.  Let `M_Omega` be the
zero-diagonal adjacency matrix of `Omega`, reduced over `F_2`.  Since `q` is
even, the defining identities for `D` and `E` give

```text
D       = A^2 + J + I,
M_Omega = E + I = A^3 + J + I,
M_Omega + D = A^2(A+I)                         over F_2.          (9)
```

The matrix `A` is alternating over `F_2`, and `A 1=0`.  Its rank, hence its
nullity (the order `q^2` is even), is even.  Therefore its kernel has
dimension at least two and contains a vector `u` outside the constant line.
For the nonempty proper shore `S=supp(u)`, (9) yields

```text
A 1_S = 0,
M_Omega 1_S = D 1_S.                           over F_2           (10)
```

Thus every vertex has an even number of A-neighbors in `S`, and, vertex by
vertex, its number of `Omega`-neighbors in `S` has the same parity as its
number of D-neighbors in `S`.  This is stronger than the aggregate cut law
(8): it is a nontrivial shore on which the overlap graph and the connected
defect graph have identical incidence parity.

The square relation gives the common parity explicitly:

```text
M_Omega 1_S = D 1_S = |S| 1 + 1_S.             over F_2           (11)
```

Thus if `|S|` is even, every point of `S` has odd internal D- and
`Omega`-degree while every outside point has even incidence into `S`; if
`|S|` is odd, these parities are reversed.  The defect half of (11) is the
previously banked odd-defect-set law.  Its simultaneous `Omega` realization
is the new information here.

Binary incidence also forces this shore away from the trivial size range.
More generally, let `0 != u in ker_F2(A)` and choose `P in supp(u)`.  Each of
the q lines through P has even intersection with `supp(u)`, so each contains
a second support point.  Distinct lines through P cannot share that second
point by C4-freeness.  Every chosen point is a non-D partner of P, giving the
pointwise strengthening

```text
deg_{D[supp(u)]}(P) <= |supp(u)| - q - 1.                       (12)
```

In particular,

```text
0 != u in ker_F2(A)  implies  |supp(u)| >= q+1.                 (13)
```

Applying (13) also to `u+1`, for the nonconstant vector chosen above, yields

```text
q+1 <= |S| <= q^2-q-1.
```

The two bottom equality cases are rigid.  If `|S|=q+1`, (12) makes `D[S]`
empty.  If `|S|` is even, then (11) makes every internal D-degree odd, so the
lower bound rounds up to `q+2`; at equality (12) makes every internal degree
exactly one and `D[S]` is a perfect matching.  In the odd branch, (11) also
says every one of the `q^2-|S|` outside vertices sends an odd, and hence
nonzero, number of D-edges into `S`.

### The binary edge congruence

The kernel shore exposes a k-dependent specialization of the edge residue.
Write

```text
r_X = |N_A(X) intersect S| = 2 a_X.
```

Every unordered non-D pair in `S` has a unique common A-neighbor, so it is
counted on exactly one current line.  Consequently

```text
C(|S|,2) - e_D(S) = sum_X C(2 a_X,2).                         (14)
```

Also `sum_X 2a_X=q|S|`, hence `sum_X a_X=q|S|/2`.  If `k>=3`, so
`8 | q`, this last sum is divisible by four.  Since

```text
C(2a,2) = 2a^2-a
```

and `sum a_X^2 = sum a_X (mod 2)`, the right side of (14) is divisible by
four.  Therefore at `k>=3` every binary kernel shore satisfies

```text
e_D(S) = C(|S|,2)                 (mod 4),
|delta_D(S)| = |S|(q-|S|)         (mod 8).                     (15)
```

The second congruence follows from D-regularity:
`|delta_D(S)|=|S|(q-1)-2e_D(S)`.

The scope is narrower than a new k>=3 cut obstruction.  The banked variance
identity already gives, whenever `4 | q`,

```text
|delta_D(S)| = -|S|^2                                  (mod 8),
e_D(S) = C(|S|,2) + q|S|/2                             (mod 4).
```

Thus `8 | q` only kills the correction term `q|S|/2` in the edge congruence;
the mod-eight cut class is already present at q=4.  Equation (15) is a useful
k-dependent specialization, not the missing k>=3 terminal.  Its value here
is that it sits on the same shore for which (10)--(11) control vertexwise
D/Omega incidence parity.

### Even-occupancy cut variance

The exact cut-variance identity becomes stronger on a kernel shore.  Put
`b_X=|N_A(X) intersect S|=2c_X` and write

```text
|S| = 2q a + r,        0 <= r < 2q.
```

Since `sum_X c_X=q|S|/2`, the q-squared integers `c_X-a` have sum `qr/2`.
Minimizing their square deviation from `r/(2q)` by zeros and ones gives

```text
|delta_D(S)|
  = sum_X (b_X-|S|/q)^2
  = 4 sum_X (c_X-|S|/(2q))^2
  >= r(2q-r).                                             (16)
```

This is the ordinary cut-variance bound with its modulus doubled from q to
`2q`, using the Baer/kernel evenness of every line occupancy.  Equality
forces every line to meet `S` in one of the two adjacent even sizes `2a`
and `2a+2`, with exactly `qr/2` lines of the larger size.  At the bottom
weights it recovers the structural calculations above:

```text
|S|=q+1  implies  |delta_D(S)|=q^2-1,
|S|=q+2  and S even-minimal implies |delta_D(S)|=q^2-4.
```

In particular no nonconstant kernel shore can be a minimum D-cut of size
`q-1`: the previously proved minimum-cut residue `|S|=qa +/- 1`, reduced
modulo `2q`, makes the right side of (16) at least `2q-1` (and is
`q^2-1` in the opposite-parity residue).

### Direct transport back to the broken Baer pairs

The symmetric difference targeted above already contains `T` in a precise
way.  Let `H` be the simple graph with adjacency matrix

```text
M_H = M_Omega + D = A^2(A+I)                    over F_2.        (17)
```

The diagonal in (17) is zero: `diag(A^2)=q=0`, while `diag(A^3)` counts
twice the triangles through a point.  Also `M_H 1=0`, so H is Eulerian.
On an A-edge, Omega is absent and D is present exactly for a T-edge.
Therefore

```text
H intersect A = T.                                             (18)
```

Remove this adjacency-edge part by putting

```text
K = H triangle T = Omega triangle (D setminus T).
```

Both H and T are Eulerian, hence K is Eulerian; by (18), K is disjoint from
A.  On the kernel shore `S`, equation (17) gives `M_H 1_S=0`, and therefore

```text
M_K 1_S = M_T 1_S.                              over F_2         (19)
```

This has an exact partial-involution interpretation.  For a point P, let
`sigma_P(S)` be the number of transpositions of `iota_P` with exactly one
endpoint in S.  The parity of `N_A(P) intersect S` is zero.  Every unsplit
transposition contributes zero modulo two and every split transposition
contributes one, while the points outside the involution domain are exactly
the T-neighbors.  Hence

```text
sigma_P(S) = |N_T(P) intersect S|
           = |N_K(P) intersect S|               (mod 2).        (20)
```

There is no matrix ambiguity in the location of K.  For nonadjacent points
`P,Y`, the A-edges between `N_A(P)` and `N_A(Y)` form a matching: two edges
sharing an endpoint would give that endpoint and P or Y two common
neighbors.  Its size is exactly `(A^3)(P,Y)`.  Since `(A^2)(P,Y)` is zero
on a D-pair and one on a non-D pair, (17) says

```text
PY in K  iff
  PY in D     and the cross-neighborhood matching has odd size, or
  PY notin D  and the cross-neighborhood matching has even size,           (21)
```

where `PY` is required to be a non-A pair.  Thus (20) is a nonlinear parity
identity between split local Baer transpositions and cross-neighborhood
matchings.  Any location theorem for K may be attacked directly in these
incidence terms, without referring to the auxiliary matrix E.

Thus the missing Baer-to-T bridge is not wholly absent: every vertex's
broken-pair incidence into S is reproduced by a canonical Eulerian graph K
of non-A pairs.  What remains is a location theorem for those K-edges (or a
reason that an Eulerian nonadjacent transport with (20) is incompatible
with connected D).  This is strictly sharper than trying to compare Omega
and T directly, since their disjointness has now been factored out.

The q=4 fixed-free control calibrates the remaining difficulty exactly.
The extended verifier finds

```text
|Omega|=40, |H|=48, |K|=40,
degree multiset of K = 4^8 6^8,
|K intersect D|=8, |K setminus D|=32.
```

Its two nonconstant binary kernel shores are the two D-components, and each
has 32 crossing K-edges while still satisfying (19) vertexwise.  Thus K need
not lie in D, avoid D, or preserve D-components; even a large K-cut is
compatible with the transport identity.  A terminal really must use the
`k>=3` incidence structure, not a support-containment shortcut.

### The half-occupancy (Bockstein) lift

The even line occupancies retain one more binary layer.  For a kernel shore
S put

```text
c = A 1_S / 2                         (an integer vector),
beta(S) = c mod 2,
B = supp(beta(S)).                                           (22)
```

Thus B is the set of polar lines meeting S in `2 mod 4` points.  When
`4 | q`, it has even size because

```text
sum_X c_X = q|S|/2 = 0  (mod 2),
```

and it is invariant under complementing S:

```text
beta(V setminus S) = (q/2)1-beta(S) = beta(S)  (mod 2).        (23)
```

This lift has a pointwise incidence consequence.  Fix `P in S`.  Each of
the q lines through P contains at least one further S-point.  A line in B
has S-intersection congruent to 2 modulo four, hence needs at least one
further point; a line outside B has positive S-intersection divisible by
four, hence needs at least three.  The q sets of further points are disjoint
by C4-freeness.  Therefore

```text
|S| >= 1 + |N_A(P) intersect B|
          + 3(q-|N_A(P) intersect B|)
     = 3q+1-2|N_A(P) intersect B|.                           (24)
```

In particular `B=empty` forces `|S|>=3q+1`; more generally every shore
smaller than `3q+1` forces a uniform lower bound on adjacency from S into B.
At the bottom weights `q+1` and `q+2`, every line through a point of S lies
in B, recovering the all-0/2 line-intersection profile from equality in
(16).

The lift also transports the next bit of the defect profile.  Put
`d=D 1_S`, and let p be its zero-one parity representative: `p=1_S` when
`|S|` is even and `p=1-1_S` when `|S|` is odd.  Since

```text
d = (q-1)1_S + |S|1 - 2Ac,
```

the integer half-residual `w=(d-p)/2` satisfies, over F_2 and for `4 | q`,

```text
w = 1_S + (|S|/2)1 + A beta(S)             if |S| is even,
w = ((|S|-1)/2)1 + A beta(S)               if |S| is odd.      (25)
```

Thus `A beta(S)` is exactly the second binary digit of the internal
D-degree vector, after removing the forced first digit (11).  This is a
genuine refinement of the closed mod-two kernel route: it is a new
vertexwise incidence vector, not another scalar cut residue.  Finally,

```text
1_S dot beta(S) = e_A(S)  (mod 2),
```

since `1_S^T A 1_S=2e_A(S)`.  Equivalently, A-edge parity is the quadratic
evaluation of the half-occupancy lift on its kernel shore.

The two constant lifts have strong support windows.  If `beta(S)=0`, (24)
applied to S and its complement gives

```text
3q+1 <= |S| <= q^2-3q-1.                                  (26a)
```

If `beta(S)=1`, every line meets S in at least two points, so incidence
counting gives `|S|>=2q`; the same holds for the complement by (23).  At
equality every line meets S in exactly two points, so `A1_S=2 1` and the cut
variance is zero.  Connected D excludes that equality and therefore

```text
2q+1 <= |S| <= q^2-2q-1                 if beta(S)=1.       (26b)
```

Constant beta also doubles the variance modulus once more.  Let
`epsilon in {0,1}` be its constant value.  Every line occupancy has the
form `2epsilon+4z_X`.  Write

```text
|S| = 2epsilon q + 4q a + r,       0 <= r < 4q.
```

Repeating the integer-variance minimization on the z-coordinates gives

```text
|delta_D(S)| >= r(4q-r).                                  (27)
```

Equality means that all line occupancies are the two adjacent permitted
values `2epsilon+4a` and `2epsilon+4a+4`.  When `r=0`, a connected nontrivial
shore cannot have zero variance; its nonzero zero-sum deviations are
multiples of four, so the first possible energy is 32.  Thus the constant
Bockstein branches either occupy the interior windows (26), or pay a
modulus-`4q` cut cost (27).  This is still not a terminal, but it is a
strictly finer consumer than (16).

The nonconstant branch has a complementary packing bound.  Suppose
`s=|S|<3q+1` and put

```text
L = ceil((3q+1-s)/2).
```

By (24), every point of S has at least L A-neighbors in B.  If
`r_X=|N_A(X) intersect S|` for `X in B` and
`I=sum_{X in B} r_X`, then `I>=sL`.  C4-freeness gives

```text
sum_{X in B} C(r_X,2) <= C(s,2).
```

Cauchy therefore yields

```text
I^2/|B| - I <= s(s-1),
|B| >= I^2/(I+s(s-1))
     >= s L^2/(L+s-1).                                  (28)
```

At the minimum possible shore `s=q+1`, one has `L=q`, and (28) gives
`|B|>=q(q+1)/2`.  Equality in (16) shows that these are exactly all the
secant lines, so equality holds.  Thus a small kernel shore forces a
quadratically large half-occupancy support B; the new layer cannot remain a
sparse correction to the first mod-two kernel vector.

At the two bottom weights this packing is an exact familiar design.  Equality
in (16) says every line meets S in zero or two points.  Hence the map

```text
X in B  |->  N_A(X) intersect S
```

is a bijection from B to the non-D pairs of S: every image is a pair, every
non-D pair has a unique common A-neighbor, and C4-freeness makes the map
injective.  Using the bottom defect profiles gives

```text
|S|=q+1:  B is indexed by E(K_{q+1}),
|S|=q+2:  B is indexed by E(K_{q+2} setminus M),               (29)
```

where M is the perfect matching `D[S]`.  In both cases the bipartite
A-incidence between S and B is exactly vertex-edge incidence in the graph
shown in (29).  This remains true even when S and B overlap as subsets of
the ambient vertex set; looplessness merely says that an overlapping label
X is not an endpoint of the pair it indexes.

Equivalently, with S and B treated as labeled copies, this incidence is
`(q,2)`-biregular.  Every A-neighbor of a point of S labels a line through
that point and hence lies in B, so

```text
N_A(S) is contained in B,
A has no edge from S to V setminus B.                           (29a)
```

Every point of B uses exactly two of its q A-edges on S and its remaining
`q-2` edges outside S.  Thus (29) specifies the whole A-interface of the
bottom shore, not only a pair-counting bijection.

Over F_2 this interface has exact rank.  The vertex-edge incidence matrix of
a connected graph has rank one less than its number of vertices; both
graphs in (29) are connected.  Hence

```text
rank_F2 A[S,B] = |S|-1.                                      (29b)
```

By (29a), the rows indexed by S have no entries outside B, so (29b) is also
their rank in the full adjacency matrix.  Their sole dependency is the sum
of all S-rows, namely `A1_S=0`.  Equivalently, no nonempty proper subset of
S supports another adjacency-kernel word.  The bottom shore is therefore
an indecomposable binary row dependency, not merely a minimum-weight set.

The overlap has its own rigid form.  A point `X in S` belongs to B exactly
when its polar line meets S twice, equivalently when its degree in `A[S]` is
two.  Any neighbor in `A[S]` also has positive even induced degree, hence
degree two.  Consequently

```text
A[S] = a disjoint union of cycles on S intersect B,
       plus isolated vertices on S setminus B,                 (30)
```

with no 4-cycle.  Thus any exclusion of a bottom kernel shore has a concrete
self-indexing target: embed the labels of a complete-graph (or
cocktail-party) edge-incidence design back into its own point set so that
the overlapping labels induce only C3 or cycles of length at least five.

### Coupling the two binary layers

Extend `sigma_P(R)` to any vertex set R: it is the number modulo two of
`iota_P` transpositions with exactly one endpoint in R.  Partitioning the
A-neighbors of P into the broken T-neighbors and the involution pairs gives
the general identity

```text
sigma_P(R) + |N_T(P) intersect R|
  = |N_A(P) intersect R|                    (mod 2).            (31)
```

Apply (31) to the half-occupancy support B.  Its right side is
`(A beta(S))_P`, which (25) identifies with the second binary digit w of the
D-degree into S.  Vertexwise,

```text
sigma(B) + T beta(S)
  = w + 1_S + (|S|/2)1                  if |S| is even,
sigma(B) + T beta(S)
  = w + ((|S|-1)/2)1                    if |S| is odd.          (32)
```

This is the promised direct coupling: the second defect digit is exactly a
sum of split Baer pairs on B and T-incidence into B, up to the displayed
forced constants.

It also gives a clean recursion-or-signature dichotomy.  If
`A beta(S) != 0`, its support is a nontrivial vertexwise second-bit Baer
signature, explicitly the right side of (32).  If `A beta(S)=0`, then B is
itself a binary kernel shore.  Equations (19), (20), and (31) repeat on B:

```text
K beta(S) = T beta(S) = sigma(B).                            (33)
```

The constant possibilities `beta=0,1` are already confined by (26)--(27).
Otherwise B is a new nonconstant even kernel shore (its cardinality is even
by (23)), so all support, cut, K/T, and half-occupancy laws above apply to B
again.  Thus the Bockstein layer cannot disappear silently: it either emits
the explicit second-bit signature (32), lands in a controlled constant
branch, or produces an iterated even kernel shore carrying the same Baer
transport.

Symmetry constrains any iterated branch.  For two kernel shores U,V, write
`u=1_U`, `v=1_V`, and let `c_U=Au/2`, `c_V=Av/2`.  Then

```text
u dot beta(V)
  = u^T c_V
  = (u^T A v)/2
  = c_U^T v
  = beta(U) dot v                              (mod 2).          (34)
```

Thus the half-occupancy lift is self-adjoint on pairs of kernel shores even
though it is not a linear map on their binary code.  Along any recursive
chain `u_{i+1}=beta(u_i)` that stays in the kernel,

```text
u_i dot u_{j+1} = u_{i+1} dot u_j,
u_i dot u_{i+2} = |supp(u_{i+1})| = 0           (mod 2),         (35)
```

because every beta-support has even cardinality (here, as throughout the
lift, `4 | q`).  Also
`u_i dot u_{i+1}=e_A(supp(u_i)) (mod 2)` by the quadratic identity after
(25).  Hence an iterated shore sequence must carry a symmetric shifted Gram
pattern; arbitrary cycles of kernel shores are not admissible.  Equations
(34)--(35) do not yet force linear independence or exclude a two-cycle, so
no dimension contradiction is claimed.

They do classify odd periodic orbits.  Suppose a literal recursive orbit
has odd period ell.  The first identity in (35), with indices modulo ell,
makes `u_i dot u_j` depend only on `i+j mod ell`.  Every diagonal value is
zero because every orbit vector is itself a beta-support and hence has even
weight.  Since multiplication by two permutes the residues modulo odd ell,
the diagonal classes `2i` exhaust all possible sums.  Therefore

```text
u_i dot u_j = 0 for every i,j on an odd-period orbit,
e_A(supp(u_i)) = 0 for every i.                              (36)
```

So an odd Bockstein cycle would have to span a totally isotropic subspace
of the binary coordinate pairing.  This still permits dependence and does
not rule out such an orbit, but it is a concrete obstruction unavailable
to an arbitrary recursion.

For an even literal period `ell=2m`, the same argument kills exactly the
even residue classes.  The Gram entry `u_i dot u_j` still depends only on
`i+j mod 2m`; diagonal sums `2i` exhaust all even residues, so

```text
u_i dot u_j = 0 whenever i and j have the same parity.          (36a)
```

Thus the even-phase shores and odd-phase shores each span a totally
isotropic subspace, and the orbit Gram matrix has block form
`[[0,C],[C^T,0]]`; only opposite phases can pair.  The period-two normal
form below is the first case of this bipartite isotropic structure.  Again,
this constrains rather than excludes longer even orbits.

The bottom incidence geometry excludes the shortest even return.  Suppose
`|S|` is `q+1` or `q+2`, B is itself a kernel shore, and put
`C=supp(beta(B))`.  Equation (29a) gives

```text
|N_A(P) intersect B| = q                 for every P in S.
```

Since `4 | q`, division by two and reduction modulo two give

```text
C intersect S = empty.                                          (37)
```

Thus a bottom shore cannot be a fixed point or belong to a two-cycle of the
Bockstein recursion: after `S -> B`, the next half-occupancy support avoids
S entirely.  If C is the zero vector the lift reaches the controlled
constant branch; if `A1_C != 0` it emits the next signature; and if C is a
new nonconstant kernel shore then it is an even shore, disjoint from S, on
which the full package recurses again.  In particular the exact
complete/cocktail incidence leaves no bottom period-two escape.

More generally, an even-period survivor has a rigid mod-four incidence
normal form.  Suppose U,V are nonconstant kernel shores with

```text
beta(U)=V,       beta(V)=U,
s=|U|,           t=|V|.
```

Then, pointwise,

```text
|N_A(x) intersect U| = 2 [x in V]  (mod 4),
|N_A(x) intersect V| = 2 [x in U]  (mod 4).                    (38)
```

In particular every U-point has `2 mod 4` neighbors in V and every V-point
has `2 mod 4` neighbors in U; all points off the opposite shore have degree
`0 mod 4` into it.  Let `a(s)` be the least integer congruent to 2 modulo
four which is at least

```text
max(2, ceil((3q+1-s)/2)),
```

and define `a(t)` symmetrically.  Equation (24) and (38) give the cross
minimum degrees `a(s),a(t)`.  C4-freeness and incidence balance then force

```text
s C(a(s),2) <= C(t,2),       s a(s) <= (q-2)t,
t C(a(t),2) <= C(s,2),       t a(t) <= (q-2)s.                 (39)
```

These are necessary conditions for every literal two-cycle, including
overlapping U,V (treat the two shores as labeled copies).  They subsume the
bottom exclusion: at `s=q+1` or `q+2`, the exact interface has U-to-V degree
q, congruent to zero rather than two modulo four.

A fixed point is substantially more constrained.  Put U=V and s=t.  Then
every induced degree in `A[U]` is `2 mod 4` and at least `a(s)`.  Pair
counting in U gives

```text
s C(a(s),2) <= C(s,2),
s >= a(s)(a(s)-1)+1.                                         (40)
```

If `s<3q+1`, using `a(s)>=(3q+1-s)/2` in (40) yields

```text
(3q-s)^2 <= 4s-3,
s >= 3q+2-sqrt(12q+1).                                      (41)
```

The same lower bound is automatic when `s>=3q+1`.  Hence no Bockstein fixed
shore lives near the generic minimum `q+1`: every fixed point is confined
to a narrow window below or above `3q`.  Equations (39)--(41) are an exact
normal form, not yet an exclusion of large or asymmetric two-cycles.

The pair inequalities also force at least one shore of every two-cycle into
that scale.  Let `m=max(s,t)`.  Both shores are nonconstant beta-supports,
so `s,t>=q+2`.  If `m<3q+1`, use the first inequality in (39), the bounds
`t<=m`, `s>=q+2`, and
`a(s)>=(3q+1-m)/2` to obtain

```text
4m(m-1) >= (q+2)((3q-m)^2-1).                              (42)
```

Thus a two-cycle cannot have both shores uniformly small: (42) places its
larger shore within `O(sqrt(q))` of `3q` (the leading-order threshold is
`3q-6 sqrt(q)`).  This is only a localization; it deliberately leaves the
large/asymmetric branch open.

### The finite dyadic stopping theorem

The half-occupancy lift is the first level of a genuinely k-dependent
hierarchy.  Let `q=2^k` with `k>=2`.  For `1<=j<=k-1`, suppose every line occupancy
`b_X=|N_A(X) intersect S|` is divisible by `2^j` (equivalently, all earlier
binary digits vanished), and define

```text
beta_j(S)_X = (b_X / 2^j) mod 2.                              (43)
```

Thus `beta_1=beta`.  Since `q/2^j` is even at these levels,

```text
beta_j(V setminus S) = beta_j(S),
|supp(beta_j(S))| is even.                                   (44)
```

There is a level-j version of (24).  Fix `P in S`, and put
`m=|N_A(P) intersect supp(beta_j(S))|`.  A marked line through P has positive
occupancy congruent to `2^j` modulo `2^(j+1)`, so it supplies at least
`2^j-1` further S-points.  An unmarked line has positive occupancy divisible
by `2^(j+1)`, so it supplies at least `2^(j+1)-1`.  The q sets of further
points are disjoint.  Hence

```text
|S| >= (2^(j+1)-1)q + 1 - 2^j m.                             (45)
```

In particular, if `beta_j(S)=0`, then (44)--(45), applied to S and its
complement, force

```text
(2^(j+1)-1)q+1 <= |S|
                     <= q^2-(2^(j+1)-1)q-1.                  (46)
```

The hierarchy must stop.  The kernel condition starts the induction because
every occupancy is even.  At any level, `beta_j(S)=0` says precisely that all
occupancies are divisible by `2^(j+1)`, so the next digit is defined.  If every
digit `beta_1,...,beta_(k-1)` vanished, then (46) at `j=k-1` would require both
S and its complement to have at
least

```text
(q-1)q+1 = q^2-q+1
```

points, whose sum exceeds `q^2`.  Therefore every nontrivial binary kernel
shore has a least level `j<=k-1` with

```text
beta_j(S) != 0.                                               (47)
```

At the final possible level `j=k-1`, a constant-one digit would make every
line occupancy exactly `q/2`: it is the only multiple of `q/2`, at most q,
whose quotient is odd.  Then `A1_S=(q/2)1`, the cut variance is zero, and S is
a union of D-components.  Consequently, when D is connected, a stopping
digit at level `k-1` is necessarily nonconstant.

This is the first mechanism in the Baer lane whose depth grows with k.  It
proves that the incidence hierarchy cannot remain invisible modulo
successively higher powers of two: before the q-scale it must emit a
nonzero even, complement-invariant marked-line layer, and at the last level
that layer is genuinely nonconstant under connectedness.

The stopping layer has quantitative consumers at every depth.  Put
`a=2^j`, `B=supp(beta_j(S))`, `s=|S|`, and

```text
L_j(t) = max(0, ceil(((2a-1)q+1-t)/a)).
```

Applying (45) to S and, using (44), to its complement gives

```text
deg_A(P,B) >= L_j(s)       for P in S,
deg_A(P,B) >= L_j(q^2-s)   for P outside S.                 (48)
```

Therefore exact incidence counting and the same C4-free pair packing used
in (28) imply

```text
q|B| >= s L_j(s) + (q^2-s)L_j(q^2-s),

|B| >= s L_j(s)^2 / (L_j(s)+s-1),
|B| >= (q^2-s)L_j(q^2-s)^2
                     / (L_j(q^2-s)+q^2-s-1).                (49)
```

As before, a fraction on the right is rounded up.  Thus a late nonconstant
stopping digit is not merely nonempty: it is simultaneously large enough to
service the two complementary shores, with shared pairs limited by
C4-freeness.

There is also a depth-j form of the constant-lift variance law (27).  If
`beta_j(S)=epsilon 1`, where `epsilon` is zero or one, every occupancy is
`epsilon a` modulo `2a`.  Write

```text
s = epsilon a q + 2a q h + r,       0 <= r < 2a q.
```

Minimizing the squared deviations among these permitted occupancies gives

```text
|delta_D(S)| >= r(2a q-r).                                (50)
```

Equality forces the two adjacent permitted occupancies
`epsilon a+2ah` and `epsilon a+2a(h+1)`.  Equations (16) and (27) are the
base even-occupancy case `(a,epsilon)=(1,0)` and the first lifted case
`a=2`, respectively.

At the last level there is an exact census, not just a bound.  Here
`a=q/2`, so every line occupancy is `0`, `q/2`, or q, and B is precisely the
set of half-occupied lines.  If `n_q` is the number of full lines, incidence
counting gives

```text
|B|/2 + n_q = s.
```

Substitution in the exact cut-variance identity yields

```text
|delta_D(S)| = s(q^2-s) - (q^2/4)|B|,
|delta_D(S)| = s(q^2-s)                 (mod q^2/2),          (51)
```

where the congruence uses the even weight of B.  Connectedness makes the
left side positive, so

```text
|B| < 4s(q^2-s)/q^2 <= q^2.                                (52)
```

Thus (48)--(52) squeeze the final nonconstant layer simultaneously by local
C4 packing and by an exact D-cut energy.  Extracting a forbidden partial
design from that squeeze is the remaining terminal.

The final layer also collapses the internal D-degree profile to two levels
on each shore.  Indeed the exact identity used in (25) is

```text
D1_S = (q-1)1_S + s1 - 2A(A1_S/2).
```

At the final level every entry of `A1_S/2` is a multiple of `q/4`, so the
last term is zero modulo `q/2`.  If `r` is the residue of s modulo `q/2` and
`rho` is the residue of `r-1` in `{0,...,q/2-1}`, then

```text
deg_{D[S]}(P) is in {rho,rho+q/2}       for P in S,
deg_D(P,S) is in {r,r+q/2}              for P outside S.    (53)
```

If x and y count the vertices taking the higher value on S and its
complement, respectively, the common cut size determines them exactly:

```text
|delta_D(S)| = s(q-1-rho) - (q/2)x
             = (q^2-s)r + (q/2)y.                           (54)
```

Thus the last stopping digit produces a two-cell degree profile in D, not
only a line-intersection profile in A.  Equations (51) and (54) couple its
marked-line count and its two high-degree populations through the same cut.

Equating the two expressions in (54) removes the cut altogether.  When
`r=0`, one has `rho=q/2-1`; when `1<=r<q/2`, one has `rho=r-1`.  Hence

```text
x+y = s                    if r=0,
x+y = 2(s-qr)              if 1<=r<q/2.                     (55)
```

In particular a nonzero residue at the final stopping level must satisfy

```text
s >= qr,       where r = s mod (q/2).                       (56)
```

This residue restriction is invisible in the scalar parity laws: it uses
the two different shores' exact degree profiles, not merely the cut size.

The local bound (48) makes the final layer much more rigid than (52) alone
suggests.  Since `deg_A(P,B)<=q` on both shores, its final-level
specialization forces

```text
q^2/2-q+1 <= s <= q^2/2+q-1.                               (57)
```

Write `s=q^2/2+d`, so `|d|<=q-1`, and put `C=V setminus B`.  The exact
pointwise form of (48), with `a=q/2`, is

```text
deg_A(P,C) <= 2-ceil((1-d)/(q/2))       for P in S,
deg_A(P,C) <= 2-ceil((1+d)/(q/2))       for P outside S.    (58)
```

Across the interval (57), both right sides are at most three.  Consequently

```text
Delta(A[C]) <= 3.                                           (59)
```

Every vertex of C indexes either an empty line or a full line, because its
S-occupancy is respectively zero or q.  Thus the final obstruction has been
reduced to a nonempty set of monochromatic lines whose induced A-graph is
subcubic, while all remaining lines are exactly half occupied.  A uniform
classification or elimination of this bounded-degree exceptional design
would close the final dyadic branch.

There is a canonical four-type decomposition of that exceptional design.
For `X in C`, let `p(X)=1` when X itself lies in S, and let `ell(X)=1` when
the line `N_A(X)` is full (rather than empty).  If `XY` is an A-edge inside
C, incidence in the two directions gives

```text
p(Y)=ell(X),       p(X)=ell(Y).                              (60)
```

Thus an A-edge swaps the ordered type `(p,ell)`.  The subcubic graph A[C]
is the disjoint union of its induced `(0,0)` part, its induced `(1,1)` part,
and a bipartite graph between types `(0,1)` and `(1,0)`; there are no other
cross-type edges.  This exact routing rule is additional structure beyond
subcubicity and is the natural entry point for coupling the exceptional
lines back to the Baer involutions.

The exceptional design is small.  Substituting `s=q^2/2+d` and
`|B|=q^2-|C|` into (51) gives the exact compression

```text
|delta_D(S)| + d^2 = (q^2/4)|C|.                            (61)
```

On the other hand every cut in the `(q-1)`-regular graph D satisfies
`|delta_D(S)| <= (q-1)min(s,q^2-s)=(q-1)(q^2/2-|d|)`.  Since
`|d|<=q-1`, the elementary bound

```text
d^2-(q-1)|d| <= 0
```

in (61) yields

```text
2 <= |C| <= 2q-2,       |C| even.                           (62)
```

Here nonemptiness follows from the nonconstant final digit, and evenness
from the even weights of both B and V.  The hierarchy has therefore
compressed a potential q-squared obstruction to an even, nonempty,
four-typed subcubic graph on at most `2q-2` exceptional lines.

Its line-type imbalance is fixed as well.  If `c=|C|` and `f` exceptional
lines are full, the final census `|B|/2+f=s`, together with
`s=q^2/2+d` and `|B|=q^2-c`, gives

```text
f = c/2+d,
#full-#empty = 2d,       |d| <= c/2.                        (63)
```

So the displacement of the shore from half size is exactly half the signed
imbalance of the two monochromatic line types.  In particular, the small
exceptional graph carries all of the global shore imbalance.

Opposite line types form a complete bipartite defect core.  Indeed a full
line and an empty line cannot share an A-neighbor: such a point would have
to lie both in S and outside S.  Since off-diagonal entries satisfy
`(A^2)_{XY}=1-D_{XY}`, it follows that

```text
C_full cross C_empty is contained in E(D).                  (64)
```

Consequently either one exceptional line type is absent, in which case
`|d|=c/2`, or both types occur and D-regularity gives

```text
|C_full|<=q-1,       |C_empty|<=q-1,
c <= 2(q-1-|d|).                                         (65)
```

In the mixed case, equality `c=2q-2` would force `d=0` and both classes to
have size `q-1`.  Then the `K_(q-1,q-1)` in (64) exhausts every D-degree of
C, making C a proper union of D-components, contrary to connectedness.
Thus the maximum mixed exceptional design is already excluded; the pure
full/pure empty branch and the smaller mixed cores are the two remaining
structural cases.

The same dichotomy is measured exactly by cut energy.  Let
`u=min(|C_full|,|C_empty|)=c/2-|d|`.  Rewriting (61) gives

```text
|delta_D(S)|
  = |d|(q^2/2-|d|) + (q^2/2)u.                              (66)
```

The first term is precisely the minimum variance in the preceding
zero-digit modulus `q^2/2`; every minority-type exceptional line costs one
additional quantum `q^2/2`.  Hence the pure branch is exactly the equality
case of that earlier variance bound, while the mixed branch has a
quantized positive excess.  This supplies a scalar detector for the
structural split in (64)--(65).

Finally, the two line types carry separate bounded-replication linear
designs.  Put `F=C_full`, `E=C_empty`, and define

```text
t_P^F = |N_A(P) intersect F|       for P in S,
t_P^E = |N_A(P) intersect E|       for P outside S.
```

Full lines have no incidences outside S and empty lines have none inside S.
Equations (58)--(59), regularity, and the off-diagonal identity
`A^2=J-D` therefore give

```text
0 <= t_P^F,t_P^E <= 3,
sum_(P in S) t_P^F = q|F|,
sum_(P outside S) t_P^E = q|E|,                            (67)

sum_(P in S) C(t_P^F,2) = C(|F|,2)-e_D(F),
sum_(P outside S) C(t_P^E,2) = C(|E|,2)-e_D(E).             (68)
```

Thus the last branch is equivalently two q-uniform linear block systems of
replication at most three, joined by the D-complete bipartite core (64),
and decorated by the four-type A-routing rule (60).  This is the precise
q-generic exceptional-design object still requiring elimination.

All of the final occupancy data has a compact signed form.  Define

```text
x = 2 1_S-1,
z = 1_F-1_E.
```

Thus x has full support with entries in `{+1,-1}`, while z has entries in
`{+1,0,-1}` and support exactly C.  Empty, half, and full occupancy are
equivalent coordinatewise to the single integer equation

```text
A x = q z,       |supp(z)|=c<=2q-2,       1^T z=1^T x=2d.   (69)
```

Applying `A^2=(q-1)I+J-D` gives the companion defect equation

```text
D x = (q-1)x + 2d 1 - q A z.                               (70)
```

The final dyadic terminal can therefore be stated as a sparse signed-image
problem: exclude a full-support sign vector whose A-image is q times a
signed vector on at most `2q-2` coordinates, subject to the four-type,
subcubic, and D-complete structure above.  This formulation is well suited
to a signed-support expansion argument and avoids enumerating the exceptional
designs individually.  The abstract Smith-normal-form/cokernel route is
already closed in the authoritative outline: the useful extra input here is
the sparse `{+1,0,-1}` support together with its saturated line types, not
the invariant factors of A alone.

The mixed support is smaller than the coarse bound (62).  Put
`a=|d|`, `u=min(|F|,|E|)`, and `m=q/2`.  If `a=0`, the relevant cap in (58)
is one on both shores, so `qu<=q^2/2` and `u<=m`.  If `a>0` and both line
types occur, (58) first forces `a<=m-1` (at `a>=m` the minority cap is
zero).  The minority shore then has replication at most one, giving

```text
qu <= q^2/2-a,       u <= m-1.                              (71)
```

The D-complete core independently gives

```text
u+2a <= q-1,       so u <= q-1-2a.                          (72)
```

Since `c=2(u+a)`, maximizing the minimum of the bounds in (71)--(72), with
the balanced case included separately, yields

```text
c <= 3q/2-2                 whenever F and E are both nonempty. (73)
```

Indeed the two affine bounds cross at `a=q/4`; on either side their maximum
is `3q/2-2`.  Thus only the pure branch can approach the earlier `2q-2`
support bound.  The mixed sparse-image terminal already has support at most
one and a half times q.

The replication structure sharpens this once more.  In the unbalanced mixed
case, the minority line type has replication at most one by (58); in the
balanced case either type does.  Two distinct lines of that type therefore
have no common A-neighbor, so they are D-adjacent.  Equation (64) also makes
each of them D-adjacent to every line of the opposite type.  Choosing one
minority line `X` gives

```text
C setminus {X} subseteq N_D(X),       hence c-1<=q-1 and c<=q. (73a)
```

The implication “replication at most one implies a D-clique” and the closed
defect-neighborhood capacity argument are Lean-checked by
`replicationAtMostOne_secondOrderDefect_adj` and
`mixedExceptional_union_card_le_of_replicationAtMostOne`.  Thus the mixed
terminal, like the pure terminal below, has support at most `q`; (73) remains
useful only as the earlier scalar route that did not exploit the same-type
D-clique.

The unbalanced mixed case also has an exact majority-defect identity.  Orient
the shore so `d=a>0`, let the majority full family have size `f=u+2a`, and
write `n_i=|{P in S:t_P^F=i}|`.  The first companion cut formula is now
`deg_D(P,V setminus S)=(q t_P^F-2a)/2`; hence every occupied-shore point has
positive majority replication.  Equation (58) sharpens the subcubic cap to
`t_P^F<=2`, so

```text
n_1+n_2=s,       n_1+2n_2=qf,
n_2=C(f,2)-e_D(F).
```

Using `2s=q^2+2a` and `f=u+2a` gives

```text
2e_D(F)+u=(q-f)^2.                                      (73b)
```

This is Lean-checked by `binarySquare_mixedMajority_defect_identity`.  In
particular `f=q` would force `u=0`, contrary to mixedness, while the covering
inequality `s<=qf` forces `f>q/2`.  Thus every unbalanced mixed survivor has

```text
q/2 < f <= q-1,       u <= (q-f)^2,       c=f+u<=q.      (73c)
```

The balanced mixed case retains the still stronger fact that both line types
have replication at most one, so the whole exceptional support is a D-clique.

Equivalently, put `r=q-f` in the unbalanced case.  Equations (73a)--(73c)
become the compact parameter normal form

```text
1 <= u <= r < q/2,
2e_D(F)=r^2-u,
2a=q-r-u,
c=q-r+u.                                                   (73d)
```

In particular `r` and `u` have the same parity, and the first layers are
rigid: `r=1` forces `(u,e_D(F),c)=(1,0,q)`; `r=2` forces
`(u,e_D(F),c)=(2,1,q)`.  This is not a finite-q census: `r` is a uniform
defect parameter, and (73d) prescribes the majority D-edge count at every
binary order.  The remaining structural task is to exclude these prescribed
small-edge majority graphs using the four-type A-routing rule (60) and D
connectedness, or force `r` large enough to contradict the dyadic stopping
data.

The occupied-shore replication profile is also fixed by `(q,r,u)`.  If
`n_1,n_2` count its majority replication-one and replication-two points, then

```text
n_1 = q(r+1)-r-u,
2n_2 = q^2-2qr-q+r+u.                                    (73e)
```

The subtraction-free form of (73e) is Lean-checked by
`binarySquare_mixedMajority_replication_profile`.  Thus the `r=1` layer has
exactly `2(q-1)` private points and `C(q-1,2)` pair-intersection points among
its `q-1` majority lines; the `r=2` layer has `3q-4` private points and one
missing majority line-pair intersection (the unique D-edge in `F`).  These
are uniform incidence designs, not order-specific enumerations.

The same normal form determines the entire D-boundary of the exceptional
support.  Its internal D-edges are the minority clique, the complete
minority--majority cross core, and the `e_D(F)` majority edges.  Therefore

```text
|delta_D(C)| + (r-u)^2 = (q-1)(q-r-u)
                       = 2a(q-1).                         (73f)
```

The subtraction-free form of (73f) is Lean-checked by
`binarySquare_mixedExceptional_defectCut_identity`.  Thus the signed
imbalance `2a` is exactly the leading defect-boundary scale; the correction
is the square of the gap between parameter defect and minority size.  In the
balanced mixed case, both types are replication-one D-cliques and the cross
core makes `D[C]=K_c`, so `|delta_D(C)|=c(q-c)`.  Consequently the endpoint
`c=q` would have zero D-boundary and make the proper set C a D-component,
contrary to the connected-D branch.  Hence every balanced mixed survivor
already satisfies `c<=q-1`.

There is no zero-boundary exceptional coincidence in the unbalanced case.
Write `v=r-u` and `w=q-2r`; then `w>=2`, and (73f) splits as

```text
|delta_D(C)| = w(q-1)+v((q-1)-v) >= 2(q-1).               (73fa)
```

Indeed `v<=r-1<q-1`, so both summands are nonnegative.  The inequality is
Lean-checked by `binarySquare_mixedExceptional_defectCut_lower`.  Thus the
saturated case `u=r` minimizes the boundary at fixed r, with exact value
`(q-2r)(q-1)`; connectedness is not being supplied by a hidden Pell-type
exception.

At the saturated unbalanced endpoint `c=q`, one also has `u=r`; every
minority vertex then exhausts its entire D-neighborhood on `C setminus {X}`.
Let `h=|C intersect S|`.  For a minority vertex in S, the number of its
D-neighbors across the shore is exactly `q-h`; for one outside S, the number
into S is exactly h.  Substitution into the two companion shore-degree
formulas, together with minority replication `0/1` and majority replication
`1/2`, forces

```text
h in {a,f} = {(q-2r)/2, q-r}.                              (73g)
```

This arithmetic dichotomy is Lean-checked by
`binarySquare_saturatedMixed_exceptionalShore_card_dichotomy`.  It also
records the four-type routing choice: when `h=f`, a minority center in S has
one A-neighbor in the outside-majority type and a minority center outside S
has one A-neighbor in its outside-minority type; when `h=a`, those degrees
are respectively two and zero.  Thus `r=1` permits only
`h=(q-2)/2` or `q-1`, and `r=2` only `h=(q-4)/2` or `q-2`.  The low-r layers
now have both their incidence design and their four-type population fixed.

The `h=f` alternative has an exact routing shape.  Every minority center in
S has cross-type A-degree one, while every outside-majority center can only
meet an inside-minority center and has minority replication at most one.
Since `|F setminus S|=|E intersect S|` when `h=f`, edge balance forces a
perfect matching between these two types.  Every minority center outside S
has A-degree one inside the outside-minority type, so that induced graph is
also a perfect matching.  Consequently

```text
|E setminus S| is even when h=f.                           (73h)
```

For `r=u=1`, (73h) forces the unique minority center to lie in S; the unique
outside-majority center is its A-matched partner.  For `r=u=2`, the `h=f`
case has either both minority centers inside S (matched to the two
outside-majority centers) or both outside S (matched to each other).  This
removes the mixed placement in the first two saturated layers without any
order-specific search.

The majority centers on the occupied shore carry the promised partial Baer
self-indexing explicitly.  Put `R=F intersect S`.  For `X in R`, the point X
has majority replication `t_X^F`; by the routing rule (60), an A-neighbor of
X inside F must also lie in R.  Hence

```text
deg_(A[R])(X)=t_X^F in {1,2}.                             (73i)
```

Thus `A[R]` is a disjoint union of paths and cycles.  If X is a path
endpoint, then as a point of the majority design it lies on the unique full
line indexed by its sole A[R]-neighbor: X is a private point of that line.
If X has degree two with neighbors Y,Z, then X is the unique intersection
point of the full lines indexed by Y and Z.  Conversely symmetry of A makes
these incidences exactly the A[R] edges.  At `r=1,h=f`, this self-indexed
path--cycle graph has `q-2` vertices; at `r=2,h=f`, it has `q-4` vertices
when both minority centers lie in S and `q-2` when both lie outside.  The
remaining low-r obstruction is therefore a uniformly described partial-Baer
path--cycle embedding inside the complete-pair (or one-missing-pair)
majority design, not an unstructured exceptional graph.

The majority design has a local private-point profile as well.  A majority
line X meets exactly those other majority lines not D-adjacent to X.  The
replication-two cap makes the resulting intersection points distinct on the
line, so among its q points the private ones number

```text
private_F(X) = q-(f-1-deg_(D[F])(X))
             = r+1+deg_(D[F])(X).                         (73j)
```

Summing (73j) recovers the first formula in (73e).  Pointwise it says more:
at `r=1`, every majority line has exactly two private points; at `r=2`, the
two endpoints of the unique D[F]-edge have four private points each, while
every other majority line has three.  Hence the sole missing intersection in
the `r=2` design is visible as one extra private point on each of its two
lines, a marked pair that the path--cycle self-indexing must respect.

The marked pair cannot be placed arbitrarily in that core.  If `Y-X-Z` is a
two-step in `A[R]`, then X itself is a common A-neighbor of Y and Z, so the
codegree identity gives `YZ notin E(D)`.  Consequently

```text
E(D[F]) contains no distance-two pair of A[R].             (73k)
```

At `r=2`, if the unique D[F]-edge has both endpoints in R, it is therefore
either an A[R]-edge (necessarily a triangle-free A-edge, since it is also a
D-edge) or its endpoints have A[R]-distance at least three or lie in
different path--cycle components.  At `r=1`, every A[R]-edge is instead a
triangle edge: D[F] is empty, so its endpoints have their unique additional
common A-neighbor.  This is the exact interface between the partial-Baer core
and `T=A intersect D`.

This partial-Baer core is not, by itself, contradictory.  In fact the local
majority design realizes every C4-free graph H of minimum degree one and
maximum degree two that obeys (73k).  Start from the abstract majority
incidence points: one point `p_XY` for every non-D pair of majority lines,
and `r+1+deg_(D[F])(X)` private points on line X.  For each label `X in R`,
place X as follows:

```text
deg_H(X)=2 with neighbors Y,Z: put X at p_YZ;
deg_H(X)=1 with neighbor Y:   put X at a private point of Y. (73l)
```

The first point exists by (73k).  Two degree-two labels could collide only
if they had the same two neighbors, which would form a C4 in H; endpoint
collisions are avoided because a vertex has at most two endpoint neighbors
and every line has at least `r+1>=2` private points.  Pair points and private
points are disjoint types.  The resulting incidence is symmetric and induces
exactly H on R.

Therefore neither the complete-pair `r=1` design nor the one-missing-pair
`r=2` design can be killed from (73d)--(73k) alone.  The next argument must
use how this locally feasible self-indexing extends to the remaining
`q^2-O(q)` vertices -- equivalently, how its path--cycle marks enter the
canonical `K/Omega` transport -- rather than attempting another internal
path/cycle classification.

The required extension has an exact local transversal profile.  Let
`M=V setminus C` be the balanced line centers and take `w in M`.  Double
count common neighbors of w with the majority centers.  A majority line is
met exactly when its center is not D-adjacent to w, and its full neighborhood
lies in S, so

```text
sum_(P in N_A(w) intersect S) t_P^F
  = f-deg_D(w,F).                                         (73m)
```

The half-line `N_A(w)` contains `q/2` shore points, each of majority
replication one or two.  If `b_w` counts its replication-two (pair) points
and `p_w` its replication-one (private) points, (73m) becomes

```text
b_w+deg_D(w,F)=q/2-r,
p_w=r+deg_D(w,F).                                         (73n)
```

The arithmetic elimination is Lean-checked by
`binarySquare_residualHalfLine_profile`.  In particular every residual
half-line contains at least r private majority points: at least one in the
`r=1` design and at least two in the `r=2` design.  This is precisely the
extension datum absent from the locally feasible construction (73l).

It also has a global form.  Every private majority point lies in S, has one
majority neighbor, no minority neighbor (minority lines are empty), and
therefore exactly `q-1` neighbors in M.  Summing `p_w` over M gives

```text
r|M|+e_D(M,F)=n_1(q-1),       |M|=q^2-c.                  (73o)
```

For a saturated `r=1` survivor this recovers
`e_D(M,F)=(q-2)(q-1)` from the `2(q-1)` private points; for saturated `r=2`
it gives `e_D(M,F)=(q-4)(q-1)`.  Thus the exact D-boundary (73f) is carried
entirely by the residual half-lines' excess private-point demand.  A closing
argument must show that these required private transversals cannot coexist
with the path--cycle self-indexing and C4-free residual neighborhoods.

The private-transversal system has an exact Gram form.  Let `P` be the set
of private majority points, and let R be the `P x M` incidence matrix of A.
Every private point has one majority neighbor, no minority neighbor, and
hence residual degree `q-1`.  For distinct private points `p,p'`:

- if they have the same majority owner line, that owner is already their
  common neighbor, so C4-freeness forbids a residual common neighbor;
- if their owner lines differ, they have no common exceptional neighbor, so
  the residual codegree is zero or one according as `pp'` is or is not a
  D-edge.

Let `Q_priv` be the disjoint union of cliques on the private points carried
by each majority line.  Then

```text
R R^T = (q-2)I + J - D[P] - Q_priv.                       (73p)
```

Thus the right side is not merely PSD: it has an integral 0--1 Gram factor
with column set M and row sum `q-1`.  Formula (73j) fixes `Q_priv` locally.
At `r=1`, it is `(q-1) K_2`, a perfect matching on the `2(q-1)` private
points.  At `r=2`, it is `2 K_4` together with `(q-4) K_3`: the two marked
majority lines carry four private points and the other `q-4` lines carry
three.  The residual extension problem is therefore a prescribed integral
Gram-factorization problem for `D[P]` coupled to the partial-Baer path--cycle
marks, a genuinely stronger target than the scalar boundary identities.

There is also a pointwise complementarity on each majority center X.  Its
D-neighbors consist of all u minority centers, its `deg_(D[F])(X)` majority
neighbors, and its neighbors in M.  Combining D-regularity with (73j) gives

```text
private_F(X)+deg_D(X,M)+u=q+r.                            (73q)
```

This is Lean-checked by
`binarySquare_majority_private_ordinaryDefect_complement`.  At the saturated
endpoint `u=r`, the two terms on the left excluding u sum to q.  Thus every
`r=1` majority center has exactly `q-2` D-neighbors in M.  At `r=2`, the two
marked centers have `q-4` such neighbors and every unmarked majority center
has `q-3`.  The missing majority intersection is therefore paired
pointwise with one missing ordinary D-neighbor on each marked line; the
extension defect is localized, not merely fixed in total by (73f).

At saturation the companion shore equation localizes the D-cut on the
design points themselves.  Since `2a=q-2r`, a majority point of replication
one or two satisfies

```text
t_P^F=1  => deg_D(P,V setminus S)=r,
t_P^F=2  => deg_D(P,V setminus S)=q/2+r.                  (73r)
```

This is Lean-checked by `binarySquare_saturatedMixed_shoreCut_profile`.
Thus every private point in the `r=1` Gram system (73p) has a unique
cross-shore D-neighbor; at `r=2` it has exactly two.  Pair-intersection points
carry the complementary large cut.  The private rows therefore come with
canonical one- or two-valued defect transport marks, not only their residual
A-incidence rows -- the natural input for coupling (73p) back to the
Eulerian `K/Omega` transport.

The unique `r=1` mark does **not** yet carry a canonical `K/Omega` sign.
This is the exact obstruction to identifying the two private points on a
majority line with an oriented port pair.  For a private point `P in S`, let
`m(P)` be its unique D-neighbor outside S and put

```text
tau_P = 1_[P m(P) in T],
kappa_P = 1_[P m(P) in K],
rho_P = |{Y outside S : PY in K setminus D}|.              (73ra)
```

If `tau_P=1`, then the marked edge is an A-edge.  Omega is absent on A-edges
and K was obtained by removing T from H, so the mark lies in neither Omega
nor K: `kappa_P=0`.  If `tau_P=0`, the marked D-edge is non-A and
`K=Omega triangle (D setminus T)` makes its K- and Omega-memberships
complementary.  Thus even the *existence* of a binary K/Omega mark first
requires excluding `T` at the unique D crossing.

Moreover, Eulerianity of K and (20) give the exact row remainder

```text
kappa_P + rho_P = |N_T(P) intersect S|          (mod 2).  (73rb)
```

Indeed the left side is the full K-incidence of P across S, while an
Eulerian graph has equal internal- and crossing-incidence parity, and (20)
identifies its internal parity with T-incidence into S.  Consequently, for
the private pair `{P,Q}` owned by one majority line, the desired opposite
mark condition is equivalent (after proving `tau_P=tau_Q=0`) to

```text
|N_T(P) intersect S| + |N_T(Q) intersect S|
  + rho_P + rho_Q = 1                            (mod 2).  (73rc)
```

Neither (19)--(21) nor the Gram identity controls the two `rho` terms.
More strongly, the first requested job is false in the saturated
`r=1,h=f` branch.  Here the unique minority center `E_0` lies in S and the
unique majority center `F_0` outside S is its A-matched partner by (73h).
The complete F--E defect core (64) also gives `E_0 F_0 in D`; hence

```text
E_0 F_0 in T,
m(E_0)=F_0,
tau_(E_0)=1 and kappa_(E_0)=0.                            (73rd)
```

The middle equality holds because `E_0` has all `q-1` majority centers as
its D-neighbors, of which exactly `q-2` lie in S, so `F_0` is its unique
cross-shore D-neighbor.  Also `E_0` has majority replication one, making it
one of the two private points owned by `F_0`.  Thus at least this owner pair
provably has an invisible T-mark.  A uniform port orientation cannot assign
K/Omega signs to both raw D-marks on every majority line.  Any surviving
coupling must either give T-marks a third, separately transported label or
orient a coarser/global combination in which the forced T-mark and the
`rho` remainder cancel.  Treating all unique D-neighbors themselves as
binary signed K/Omega labels is not merely an unsupported assumption: it
excludes an allowed structural branch.

The invisible mark is nevertheless not isolated.  The center `F_0` indexes
a full line, so every A-neighbor of `F_0` lies in S.  Since T is Eulerian
for binary q and `E_0 F_0 in T`, one has

```text
N_T(F_0) is contained in S,
0 < deg_T(F_0) = 0 (mod 2),
deg_T(F_0) >= 2.                                           (73re)
```

Hence a second T-edge at the same outside owner `F_0` is forced, and it also
crosses the shore.  The correct replacement for the failed pointwise sign
may therefore retain the even bundle of T-ports at `F_0`: the forced
invisible private mark has a same-owner T companion, although the present
identities do not yet identify which of the other `q-1` points on the full
line supplies it.  This is a strictly coarser datum than signing both private
marks, but unlike that signing it is forced in the surviving branch.

In fact the type of the companions is fixed.  The routing in (73h), together
with (60), makes `E_0` the only exceptional A-neighbor of `F_0`: there is no
second minority center, and a majority center in S cannot lie on the full
line of the majority center `F_0` outside S.  Every other point of that line
is therefore an ordinary balanced center.  Consequently there is a set
`U_0` with

```text
N_T(F_0) = {E_0} disjoint_union U_0,
U_0 contained in M intersect S,
|U_0| is odd (and in particular nonzero).                 (73rf)
```

Thus deleting the forced invisible exceptional port from the even T-bundle
leaves an **odd ordinary T-port bundle** at `F_0`.  Unlike a guessed binary
K/Omega label, this parity carrier follows from the existing design and
Eulerian laws.  A transport terminal may try to carry this owner-indexed odd
bundle through the residual half-line system (73m)--(73p).

There is a second, global odd residue.  In the same `r=1,h=f` branch, the
exceptional private points are exactly `E_0` together with those vertices of
`R=F intersect S` having degree one in the path--cycle graph `A[R]`: this is
the endpoint/private correspondence in (73i).  The number of degree-one
vertices is even by the handshaking lemma.  Since (73j) gives `2(q-1)`
private points in total, it follows that

```text
|P intersect C| = 1 + #{degree-one vertices of A[R]} is odd,
|P intersect M| is odd.                                  (73rg)
```

In particular an ordinary private point always exists.  This parity is
independent of how the ordinary private marks split among T, K, and Omega;
it is therefore a robust residual target for the owner-incidence-weighted
transport, rather than a consequence of the failed pointwise sign.

This oddness has a canonical owner-wise form.  Each majority line owns
exactly two private points.  Call an owner **mixed-private** when exactly one
of its private points lies in C and the other lies in M.  If `mu` is the
number of mixed-private owners and `nu` the number whose two private points
both lie in C, then

```text
|P intersect C| = mu + 2 nu,
mu is odd.                                                (73rh)
```

Every mixed-private pair is canonically oriented by its exceptional and
ordinary endpoints.  Thus the `r=1,h=f` survivor contains an odd number of
owner pairs with a genuine binary orientation, obtained from the C/M type
rather than from a nonexistent K/Omega sign.  The special owner `F_0` is one
of them, with pair `{E_0,Q_0}` for a unique ordinary private point `Q_0`.
This is the closest direct interface presently available to an odd family
of oriented owner-port switches.

The path--cycle core canonically pairs all of these oriented owners except
`F_0`.  For `X in R`, its exceptional private points are precisely its
degree-one neighbors in `A[R]`; hence X is mixed-private exactly when it has
one such neighbor.  A cycle contributes none.  A path component contributes
two such owners when it has two vertices or at least four vertices (the
owners adjacent to its two endpoints), and zero when it has three vertices.
Therefore, if `pi` counts the path components whose order is not three,

```text
mu = 1 + 2 pi.                                            (73ri)
```

The two mixed owners contributed by each path have a canonical pairing via
that path, whereas `F_0` is the unique unpaired mixed owner.  Thus any
owner-wise telescope that cancels the paired path contributions has a single
explicit boundary term, oriented from `E_0` to the ordinary private point
`Q_0`.  Establishing that cancellation in the simultaneous residual
incidence system is now a precise terminal target.

The odd T-bundle at `F_0` also projects canonically onto the path--cycle
core.  For each `Y in R`, let `W_Y` be the unique intersection point of the
two full lines indexed by `F_0` and Y; it exists because `D[F]` is empty.
These `q-2` pair points, together with the two private points `E_0,Q_0`, are
all q points of the full line at `F_0`.  Put

```text
B_0 = {Y in R : F_0 W_Y is in T},
theta_0 = 1_[F_0 Q_0 is in T].
```

The injectivity of the pair points and (73rf) give

```text
U_0 = ({Q_0} if theta_0=1 else empty)
      disjoint_union {W_Y : Y in B_0},
theta_0 + |B_0| = 1                              (mod 2). (73rj)
```

Thus the odd ordinary T-port bundle is equivalently an odd marked subset of
the Baer path--cycle labels, up to one explicit private boundary bit.  This
is a finite core-facing target: a transport law determining the parity of
`B_0` from the path pairing in (73ri) would determine `theta_0`, or vice
versa, without assigning K/Omega signs to arbitrary private marks.

The partial Baer involution at `F_0` supplies more than this parity.  Its
domain on the full line is the complement of the T-neighbors.  After the
decomposition above, it is

```text
{W_Y : Y in R setminus B_0}
  union ({Q_0} if theta_0=0 else empty).                  (73rk)
```

The involution is fixed-point-free and therefore perfectly matches this
set.  Via `W_Y -> Y`, it gives a matching on the unmarked core labels
`R setminus B_0`, except that when `theta_0=0` exactly one such label may be
matched to the boundary point `Q_0`.  The parity in (73rj) is precisely what
makes the displayed domain even.

No two labels Y,Z paired through `W_Y W_Z` can be adjacent in `A[R]`:
otherwise

```text
Y -- W_Y -- W_Z -- Z -- Y
```

is an ambient C4.  Hence the induced matching on core labels is edge-disjoint
from the path--cycle graph `A[R]`.  The surviving low-r object has therefore
sharpened to a path--cycle core with an explicit broken set `B_0` satisfying
(73rj) and a complementary nonedge matching (with at most the one boundary
mate `Q_0`).  This is a genuine Baer-involution coupling on the core, rather
than only a count of its private points.

Equations (73rj)--(73rk) give an exact boundary dichotomy:

```text
|B_0| even:
  theta_0=1, both private edges F_0E_0 and F_0Q_0 lie in T,
  and R setminus B_0 has a perfect nonedge matching;

|B_0| odd:
  theta_0=0, iota_(F_0) pairs Q_0 with a unique W_(Y_*),
  and the remaining labels in R setminus (B_0 union {Y_*})
  have a perfect nonedge matching.                         (73rl)
```

In the odd case the boundary pair is the actual triangle
`F_0--Q_0--W_(Y_*)--F_0`; in the even case there is no private point in the
involution domain, but both private owner edges are broken T-ports.  Thus
the last local ambiguity is no longer an arbitrary sign: it is the concrete
alternative **double broken private ports versus one boundary triangle**.
The residual transport must rule out or consistently propagate these two
explicit boundary states.

### The `r=1,h=f` parity kill

The boundary analysis above exposes a much shorter contradiction when
Eulerianity of T is applied at the minority endpoint `E_0`, rather than at
the majority owner `F_0`.  Since `E_0 in E intersect S` indexes an empty
line,

```text
N_A(E_0) intersect S = empty.                             (73rm)
```

At saturation its q-1 D-neighbors are exhausted by the complete F--E core:
they are exactly all majority centers.  Of those, `F_0` is the unique one
outside S.  Hence `E_0` has exactly one cross-shore D-neighbor.  The matching
in (73h) gives `E_0 F_0 in A`, while (64) gives the same edge in D, so

```text
N_T(E_0) = {F_0},
deg_T(E_0)=1.                                             (73rn)
```

But q is even and `binarySquare_regular_triangleFree_degree_even` proves
that every T-degree is even in a C4-free q-regular graph.  This contradicts
(73rn).  The final composition is Lean-checked by
`binarySquare_saturatedR1_hEqF_impossible`.

Therefore the saturated `r=1,h=f` branch is impossible.  In particular the
forced T-mark, odd owner family, core broken set, and Baer matching
(73rd)--(73rl) are now a diagnostic derivation of the contradiction, not a
surviving transport object.  The `r=1` work that remains is solely the other
placement from (73g), namely `h=(q-2)/2`; no argument should continue to
spend transport machinery on `h=f`.

The identical endpoint parity closes the saturated `r=2,h=f` branch in
both placements allowed by (73h).  There are two empty centers.

- If both lie in S, they are A-matched to the two outside full centers.
  Fix an empty center `E_i`.  Its q-1 D-neighbors are all `q-2` full
  centers and the other empty center.  Its empty line has no A-neighbor in
  S, while the perfect matching gives exactly one A-neighbor among the two
  outside full centers.  All its remaining A-neighbors lie in M, where it
  has no D-neighbor.  Therefore `deg_T(E_i)=1`.
- If both lie outside S, (73h) A-matches them to each other.  Their edge is
  also in D because the minority support is a D-clique.  Every full center
  lies in S and hence off the empty line of `E_i`; again D-degree is already
  exhausted inside C, so the matched minority edge is its unique T-edge.

Thus in either case

```text
deg_T(E_i)=1,                                             (73rno)
```

contradicting even T-degree.  The final composition is Lean-checked by
`binarySquare_saturatedR2_hEqF_impossible`.  Hence `r=2,h=f` is impossible
as well; the only saturated `r=2` placement still live is
`h=(q-4)/2`.  More generally, the lesson is that the `h=f` routing should be
tested first at an empty center: its D-degree is exhausted on the exceptional
core, so a unique routed A-edge immediately becomes a forbidden odd
T-degree.

In fact this closes `h=f` uniformly, not only in the first two layers.  Let
`r=u>=1` be arbitrary at saturation and put

```text
s_E = |E intersect S| = |F setminus S|.
```

Every minority center has D-neighborhood exactly
`F union (E setminus {E_i})`, of size `(q-r)+(r-1)=q-1`.  If `s_E>0`, choose
`E_i in E intersect S`.  Its empty line has no A-neighbor in S, and the
`h=f` routing gives it exactly one A-neighbor in `F setminus S`; the type
rule excludes A-edges to outside minority centers.  Since its D-degree is
already exhausted on C, this matched full center is its unique T-neighbor.
If `s_E=0`, then all minority centers lie outside S and all full centers lie
inside S.  The outside-minority induced graph is a perfect matching by
(73h); its edges lie in the minority D-clique, while the empty-line and shore
routing exclude every other D-neighbor from A.  Again each endpoint has
T-degree one.  Therefore

```text
s_E>0 or s_E=0  implies  some E_i has deg_T(E_i)=1,       (73rnb)
```

contradicting even T-degree in all cases.  The uniform final composition is
Lean-checked by `binarySquare_saturatedMixed_hEqF_impossible`.

Hence **every saturated mixed `h=f` branch is impossible for every r**.  The
only placement surviving (73g) is

```text
h=a=(q-2r)/2.                                            (73rnc)
```

This removes one entire side of the saturated low-support dichotomy and is
q-generic; no order-specific endpoint is involved.

The surviving `h=a` side has a uniform exceptional T-normal form as well.
Let `s_E=|E intersect S|`.  The routing rule gives every inside empty center
exactly two A-neighbors among the outside full centers, and gives every
outside empty center no exceptional A-neighbor.  Since every empty center's
D-degree is exhausted on `F union (E setminus {E_i})`, these are exactly its
T-neighbors:

```text
E_i in S      => deg_T(E_i)=2,
E_i outside S => deg_T(E_i)=0.                            (73rnd)
```

The two full leaves belonging to distinct inside empty centers are all
distinct.  Indeed two empty centers are D-adjacent in the minority clique,
so they have no common A-neighbor; a shared full leaf would contradict that
codegree-zero condition.  Thus `A[C]` contains `s_E` vertex-disjoint
two-edge T-stars on the empty-center side (together with the majority core
and other allowed majority edges).

For each such star, Eulerianity of T places its two incident edges on a
common simple T-cycle, just as in (73rs)--(73rt).  Removing the empty center
gives a T-path coupling its two distinct outside-full leaves.  Consequently
the saturated mixed problem has now reduced uniformly to the single
placement `h=a`, with a family of disjoint paired exceptional T-ports plus
the partial-Baer majority core and the residual M incidence.  When `s_E=0`
there is no exceptional T-port and the obstruction lies entirely in the
core/residual coupling.

The shore populations and empty-line capacity in this sole surviving
placement are exact.  Write `q=2m`, `a=m-r`, and `s_E=s`.  Then

```text
|F intersect S| = a-s,        |F setminus S| = m+s,
|E intersect S| = s,          |E setminus S| = r-s.       (73rne)
```

Since `|S|=q^2/2+a` and `|C intersect S|=a`, removing C gives the strikingly
parameter-free residual shore sizes

```text
|M intersect S| = q^2/2,
|M setminus S| = q(q-2)/2.                                (73rnf)
```

The q-point lines indexed by distinct empty centers are pairwise disjoint,
because the minority D-clique gives every pair codegree zero.  An inside
empty center's line contains its two distinct outside-full T-leaves and
`q-2` points of `M setminus S`; an outside empty center's line contains q
points of `M setminus S`.  Consequently the empty lines occupy exactly

```text
s(q-2)+(r-s)q = qr-2s
```

distinct ordinary outside points, leaving

```text
|M setminus S|-(qr-2s) = q(a-1)+2s.                       (73rng)
```

Thus the residual outside capacity is fixed before any Baer matching or
K/Omega choice is made.  At the extreme `a=1` it consists of exactly `2s`
uncovered ordinary points; when also `s=0`, the empty lines partition all of
`M setminus S`.  These are q-generic endpoint conditions inside the live
`h=a` family, not order-specific enumerations.

The partial-Baer core excludes the penultimate placement of the inside
minority population.  By (73i), every vertex of `A[R]` has degree one or
two, so R cannot be a singleton.  Since `|R|=a-s`,

```text
s != a-1;
equivalently, s=a (R empty) or s<=a-2 (|R|>=2).           (73rnh)
```

This implication is Lean-checked arithmetically by
`binarySquare_no_singleton_partialBaer_core` once the graph-theoretic
zero-or-at-least-two alternative is supplied.  In particular, at the
extreme `a=1` the case `s=0` is impossible.  Its sole surviving placement
has `s=1`, no majority core, one two-edge T-star, and by (73rng) exactly two
uncovered ordinary points outside S.  This endpoint is still q-generic: it
occurs at `r=q/2-1` for every binary q.

Those two uncovered points form an exact residual terminal.  Let them be
`z_1,z_2 in M setminus S`.  By definition they lie on no empty line, so
`t_(z_i)^E=0`; as outside points they cannot lie on a full line either, so
`t_(z_i)^F=0`.  Evaluating (70) at an ordinary outside point gives

```text
2 deg_D(z_i,S) = 2a + q t_(z_i)^E.
```

At `a=1` this yields

```text
deg_D(z_i,S)=1.                                          (73rni)
```

The unique cross-shore D-neighbor lies in `M intersect S`: the sole inside
exceptional center is empty and has its D-degree exhausted on C, while there
is no inside full center because R is empty.  Hence the entire extreme
`a=1` layer consists of one paired exceptional T-star together with exactly
two ordinary outside vertices, each carrying one residual cross-shore
defect mark into the fixed `q^2/2`-point inside M shore.  Whether those two
marks coincide is now a concrete two-port terminal.

The two uncovered ports are necessarily A-adjacent.  Fix `z_i` and an empty
center `E_j`.  They are non-A because `z_i` is not on any empty line, and
they are non-D because every empty center's D-degree is exhausted on C.
Hence the codegree dichotomy supplies a unique common A-neighbor `y_(i,j)`
on the empty line of `E_j`.  The empty lines are disjoint, so for fixed i
these `r=q/2-1` witnesses are distinct.  Each lies in the covered part of
`M setminus S`: a full-center witness would put the outside point `z_i` on
a full line, while the `h=a` routing excludes empty-center witnesses.

The balanced line indexed by `z_i outside S` has exactly `q/2` outside
A-neighbors.  The witnesses account for `q/2-1` of them.  Any additional
covered outside point lies on a unique empty line and would be a second
common neighbor with its empty center, contradicting uniqueness.  There are
only two uncovered points and no loops, so the final outside neighbor of
each is the other one:

```text
z_1 z_2 is in A.                                         (73rnj)
```

Thus the extreme `a=1` survivor is literally one ordinary owner edge
`z_1z_2`, with one residual cross-shore D-mark attached to each endpoint.
The remaining dichotomy is whether those marks coincide and whether the
owner edge itself lies in D (hence T); this is the same repeated-target
versus distinct-port terminal isolated independently in the simultaneous
transport lane.

The T-parity ledger at this owner edge is exact.  Write `w_i in M intersect
S` for the unique cross-shore D-neighbor of `z_i`, and put

```text
delta = 1_[z_1 z_2 in D],
tau_i = 1_[z_i w_i in A],
b_i = |{E_j : z_i y_(i,j) is in D}|.
```

The outside A-neighbors of `z_i` are exactly `z_(3-i)` and the witnesses
`y_(i,j)`, while among its inside A-neighbors only the unique D-mark `w_i`
can lie in T.  Therefore

```text
deg_T(z_i)=delta+tau_i+b_i,
delta+tau_i+b_i = 0                              (mod 2),
tau_1+b_1 = tau_2+b_2                            (mod 2). (73rnk)
```

If the two transversals share a witness `y_(1,j)=y_(2,j)`, then that point is
the unique common A-neighbor of `z_1,z_2`.  The owner edge is consequently
non-D (`delta=0`), and the triangle `z_1z_2y_(1,j)` makes both incident
witness edges non-D as well; the shared coordinate contributes zero to both
`b_i`.  Thus (73rnk) isolates the remaining phase exactly: owner-edge status
equals cross-mark status plus the parity of triangle-free witness edges.
This is the empty-line-transversal version of the outward signed residue in
the simultaneous transport terminal.

There is also a sharp crossed-mark exclusion.  If `tau_i=1`, then the marked
edge `z_iw_i` lies in T and has no common A-neighbor.  Since `z_1z_2 in A`,
the opposite endpoint cannot be adjacent to `w_i`:

```text
tau_i=1  implies  z_(3-i) w_i is not in A.                (73rnl)
```

In fact mark coincidence is stronger than this first crossed exclusion.  If
`w_1=w_2=w` and `tau_i=1`, then `z_i` is a common A-neighbor of the opposite
defect pair `z_(3-i),w`: the owner edge is in A and so is `z_iw`.  This is
impossible because `z_(3-i)w` is the marked D-pair for the opposite endpoint.
Therefore

```text
w_1=w_2  implies  tau_1=tau_2=0.                         (73rnl')
```

Thus coincident marks leave no active marked edge at all; (73rnk) then fixes
the two witness parities to `(beta_1,beta_2)=(delta,delta)`.

The owner edge itself has exactly three possible geometries.  If
`delta=1`, it is a T-edge and hence lies on a simple T-cycle, producing an
alternate T-path between `z_1,z_2`.  If `delta=0`, the codegree dichotomy
gives a unique common A-neighbor v.  The complete outside-neighbor
description used in (73rnj) shows that either

```text
v = y_(1,j) = y_(2,j) for one empty line E_j,
```

or `v in M intersect S`.  There is no other outside possibility: shared
witnesses must have the same j because the empty lines are disjoint.  In the
inside case v is distinct from both defect marks `w_i`; otherwise the marked
D-edge `z_iw_i` would have the opposite owner endpoint as a common
A-neighbor.  Hence the terminal states are precisely

```text
(I)  a broken owner T-edge with an alternate T-path;
(II) a boundary triangle through one shared empty-line witness;
(III) a boundary triangle through one unmarked inside ordinary point.      (73rnm)
```

Case (II) contributes zero at its shared coordinate to both witness phases
in (73rnk); case (III) leaves all empty-line witness coordinates distinct.
This is a complete geometric localization of the owner-edge phase before
the simultaneous routing equations are applied.

The remaining binary phase assignments can be exhausted without a search.
Put `beta_i=b_i mod 2`.  Equation (73rnk) gives the complete table

```text
delta  (tau_1,tau_2)   (beta_1,beta_2)
  0          00               00
  0          10               10
  0          01               01
  0          11               11
  1          00               11
  1          10               01
  1          01               10
  1          11               00.                         (73rnn)
```

For distinct marks all eight rows remain compatible with the currently
proved local equations.  For coincident marks (73rnl') leaves only the two
`tau_1=tau_2=0` rows, namely `(delta,beta_1,beta_2)=(0,0,0)` and
`(1,1,1)`.  The triangle localization (73rnm)
refines the `delta=0` rows by the location of their common neighbor but does
not remove their remaining phase choices.  This is an honest negative
terminal: local T-parity, codegree, and mark coincidence do not by themselves
kill `a=1`.  A final exclusion must use a simultaneous routing relation that
couples the two witness parities or the two cross-mark phases; (73rnn) states
exactly which two/eight local rows that relation has to separate.

There is already an exact signed simultaneous-routing identity at this
endpoint.  Put

```text
w = 1_(z_1)-1_(z_2).
```

The outside-neighbor classification in (73rnj) gives, as an integer vector
on `V setminus S`,

```text
(A w)|_(V setminus S)
  = -1_(z_1)+1_(z_2)
    + sum_(E_j in E) (1_(y_(1,j))-1_(y_(2,j))).           (73rnx)
```

A shared witness cancels in its summand.  In particular the signed sum on
every empty-line block is zero: that line contains one `+1` witness and one
`-1` witness, or their common witness with coefficient zero.  Since
`1^T w=0`, the square identity also gives

```text
A^2 w = ((q-1)I-D)w,
(A^2 w)_(E_j)=0 for every empty center E_j,               (73rny)
```

the last equality using `E_j z_i` non-D for both endpoints.  Thus the
two-port terminal carries a genuine root-sum/port-difference compatibility:
the oriented owner difference routes through all empty lines with exact
blockwise cancellation before reaching the inside-neighbor difference.
This is the adjacency-square analogue of the simultaneous SRP functional's
sum--difference identity; unlike the local phase table, it uses all empty
fibers at once and is therefore a plausible input for separating the
remaining rows of (73rnn).

On the inside shore the same identity is completely sharp.  Both `z_i` have
exactly one D-neighbor in S, namely `w_i`.  Since w itself vanishes on S,
(73rny) gives the vector identity

```text
(A^2 w)|_S = -1_(w_1)+1_(w_2).                            (73rnz)
```

The right side cancels when the marks coincide and is the exact oriented
two-port difference when they are distinct.  There is no residual term.
Consequently the blockwise-balanced outside current (73rnx), after two
A-steps, transports into precisely the cross-shore mark difference.  This
is the clean sum-to-difference compatibility sought in the simultaneous
transport lane, now forced directly by the adjacency-square/defect identity
at the extreme saturated endpoint.

The coordinate form also exposes the exact labeled cross routes.  When
`w_1!=w_2`, the pair `z_i,w_i` is D and has no common A-neighbor, whereas
`z_(3-i),w_i` is non-D (the opposite endpoint's unique inside D-mark is
`w_(3-i)`) and therefore has one common A-neighbor.  Write it `p_i`.  Then

```text
N_A(z_i) intersect N_A(w_i) = empty,
N_A(z_(3-i)) intersect N_A(w_i) = {p_i},
p_i=z_i  iff  tau_i=1.                                  (73rnz')
```

The last equivalence uses the owner edge `z_1z_2 in A`: if `tau_i=1`, the
unique crossed route is `w_i-z_i-z_(3-i)`, and the converse is immediate.
Moreover `p_1=p_2` can occur only when `delta=0` and both `tau_i=0`, because
a shared cross intermediary is a common A-neighbor of the owner pair, while
an owner endpoint cannot serve as both intermediaries.  Thus the exact
mark-difference in (73rnz) retains the intermediate-port label that scalar
phase compression discarded.  Mark coincidence is precisely the degenerate
case in which both crossed codegrees drop from one to zero, recovering
(73rnl').

Consequently the complete coarse labeled state space is finite and very
small.  Let `kappa=1[p_1=p_2]` in the distinct-mark branch (and leave it
undefined for coincident marks).  Substituting (73rnk), (73rnl'), and
(73rnz') gives

```text
marks       delta  tau_1 tau_2  beta_1 beta_2  allowed kappa
coincident    0       0     0       0      0        --
coincident    1       0     0       1      1        --

distinct      0       0     0       0      0       0 or 1
distinct      0       1     0       1      0        0
distinct      0       0     1       0      1        0
distinct      0       1     1       1      1        0
distinct      1       0     0       1      1        0
distinct      1       1     0       0      1        0
distinct      1       0     1       1      0        0
distinct      1       1     1       0      0        0.       (73rnz'')
```

Thus there are exactly eleven coarse labeled states: two coincident states,
and nine distinct states because the first distinct phase row splits by
intermediary coincidence.  This table uses every presently proved local
owner/mark/codegree squeeze.  It is not an impossibility claim: all eleven
rows remain syntactically compatible with those local constraints.

There is one further exact localization relevant to the witness phases.  If
`tau_i=0` and `p_i` is an outside point, the complete outside-neighbor list
(73rnj) forces

```text
p_i = y_((3-i),j) for a unique empty line E_j.
```

If `p_i` is inside, it instead records a genuine residual-M port.  Therefore
the unresolved datum in (73rnz'') is not another bit of phase: it is, for
each unique crossed route, whether its intermediate label is an empty-line
witness or an inside residual port, and in the outside case which empty-line
block carries it.  This is exactly the color/fiber label that must be
retained by any final simultaneous-routing argument.  Importantly, the mere
incidences `z_(3-i)-p_i-w_i` do **not** force the witness edge
`z_(3-i)p_i` to be non-D: that would require an additional common neighbor,
equivalently another routing incidence analyzed below.

Here is the correct conditional rule.  Still assuming distinct marks and
`tau_i=0`, put

```text
chi_i   = 1[p_i z_i in A],
gamma_i = 1[z_(3-i) w_i in A].
```

For the edge `z_(3-i)p_i`, the vertex `z_i` is a common neighbor exactly
when `chi_i=1`, and `w_i` is a common neighbor exactly when `gamma_i=1`.
C4-freeness therefore gives `chi_i+gamma_i<=1`.  If either bit is one, that
edge is non-D.  If both are zero, its D-status is genuinely undecided: it is
D when there is no further common neighbor, and otherwise has a unique new
common neighbor `q_i`.  Equivalently,

```text
chi_i+gamma_i = 1  implies  z_(3-i)p_i notin D,
z_(3-i)p_i in D    implies  chi_i=gamma_i=0,              (73rnz_d)
```

and in the non-D case the unique continuation through that edge is `z_i`,
`w_i`, or a new port according as `chi_i=1`, `gamma_i=1`, or both vanish.
For an outside `p_i=y_((3-i),j)`, this is the exact rule for the witness atom
`d_((3-i),j)`.  It is the desired straight/turn/switch trichotomy, but it
retains the extra incidence bit that the incorrect unconditional-zero claim
had silently discarded.

Including the D-bit makes the continuation alphabet exactly four symbols.
Write `d_i^cross=1[z_(3-i)p_i in D]`.  Then (73rnz_d) and the binary
codegree dichotomy give the exhaustive table

```text
chi_i  gamma_i  d_i^cross   continuation through z_(3-i)p_i
  1        0         0      owner bend, unique common neighbor z_i
  0        1         0      mark bend,  unique common neighbor w_i
  0        0         1      defect stop, no common neighbor
  0        0         0      fresh port, unique new common neighbor q_i. (73rnz_e)
```

There are no other rows: the `11` row is C4-forbidden, and a D-edge has
codegree zero while a non-D pair has codegree one.  When `p_i` is the outside
witness on line `E_(ell_i)`, `d_i^cross` is literally the corresponding
witness atom `d_((3-i),ell_i)` in (73rnz''').  Hence the phase table fixes the
parity of the untouched witness fibers by

```text
sum_(j != ell_i) d_((3-i),j)
  = beta_(3-i) + d_i^cross                         (mod 2). (73rnz_f)
```

Thus the eleven coarse rows refine canonically by a four-letter local event,
and the only remaining witness freedom is carried by the other empty-line
blocks.  This is the exact extreme-endpoint analogue of contracting straight
passages and retaining turn/switch/boundary events in the shared occurrence
flow; no identification with a global closed token cycle is asserted here.

The owner-bend symbol has an additional fiber localization.  Suppose
`p_i=y_((3-i),j)` is outside.  Then `chi_i=1` says that this point is also
adjacent to `z_i`.  But `E_j,z_i` are non-D and their unique common
A-neighbor is `y_(i,j)` by construction.  Since `p_i` is adjacent to both,
uniqueness forces

```text
chi_i=1  iff  y_(1,j)=y_(2,j)                            (73rnz_g)
```

for an outside crossed intermediary.  Hence an outside owner bend occurs
exactly on a shared-witness line.  There is at most one such line, because
two shared witnesses would be two common neighbors of the owner pair.  If
both oriented crossed routes have outside owner bends, they therefore use
the same point: `p_1=p_2`, and (73rnz') places the state in the unique
`kappa=1, delta=0, tau_1=tau_2=0` row of (73rnz'').  Outside owner bends are
thus globally localized; mark bends, defect stops, and fresh continuations
remain distributed among the other fibers.

The corresponding signed occurrence boundary is already integral (all
differences in the following display are taken in `Z`).  For
each endpoint write `d_(i,j)=1[z_i y_(i,j) in D]`, so that
`b_i=sum_j d_(i,j)`.  Subtracting the two exact T-degree formulas in
(73rnk), rather than merely reducing them modulo two, gives

```text
Lambda
  := ((tau_1+b_1)-(tau_2+b_2))/2
   = (deg_T(z_1)-deg_T(z_2))/2
   = (tau_1-tau_2 + sum_j(d_(1,j)-d_(2,j)))/2.           (73rnz''')
```

This is an integer because both T-degrees are even.  Reversing the oriented
owner occurrence (`1 <-> 2`) negates `Lambda` exactly.  Thus `Lambda` is the
route-odd character of the full marked-witness bundle, not just its mod-two
shadow (73rnk).  The localization above is label-sensitive but does not by
itself determine the corresponding atom `d_((3-i),j)`.

Formal availability of the reversed orientation does not imply cancellation:
it is the same unoriented owner occurrence viewed backward.  Vanishing of the
global sum of (73rnz''') requires the missing occurrence-weight reversibility
that also remains in the labeled SRP and B3 bundle lanes.  This identifies the
extreme endpoint's precise contribution to that shared open lemma: an
oriented bundle consisting of one marked-port atom and one defect bit for
each empty-line witness, with the crossed-route intermediary labels retained.

The next capacity layer `a=2` also collapses to two exact placements.  Since
`0<=s<=a` and (73rnh) excludes `s=a-1`, one has

```text
a=2  implies  s=0 or s=2.                                (73rnz_h)
```

If `s=0`, then `R=F intersect S` has two vertices.  Every vertex of `A[R]`
has degree one or two by (73i), so the two vertices are adjacent and both
have degree one: the partial-Baer core is a single reciprocal-private edge.
All `r=q/2-2` empty centers are outside, their disjoint lines occupy `qr`
ordinary outside points, and (73rng) leaves exactly `q` uncovered ordinary
outside points.  Thus this placement has no exceptional T-star; its entire
obstruction is a two-vertex Baer core coupled to a q-point residual outside
set.

If `s=2`, then `R` is empty.  The two inside empty centers support two
vertex-disjoint two-edge T-stars, hence four distinct outside-full leaves;
the remaining empty centers are outside.  Formula (73rng) leaves exactly
`q+4` uncovered ordinary outside points.  Each full leaf has exactly one
exceptional T-edge, namely its edge to its star center, so Eulerianity forces
an odd nonempty bundle of its remaining T-neighbors in `M intersect S`.
For the two leaves of the same star these ordinary bundles are disjoint:
they already share their empty center as a common A-neighbor, and another
shared point would create a C4.  The two star cycles therefore couple four
odd ordinary port bundles in two disjoint pairs.

Consequently `a=2` has the finite normal form

```text
s=0:  one reciprocal-private A-edge + q uncovered M-points;
s=2:  two disjoint T-stars + four paired odd M-port bundles
      + (q+4) uncovered M-points.                        (73rnz_i)
```

Neither form is killed by local parity alone.  The former needs transport
between the reciprocal private endpoints and the q residual outside points;
the latter needs simultaneous routing of the two star-paired odd bundles.
This is the first layer beyond the fully labeled `a=1` terminal and uses no
order-specific enumeration.

The `a=2,s=0` core has a sharper two-line transversal form, with one genuine
D-status split.  Let its two vertices be `X,Y`.  Their core edge lies in A,
but unlike the `r=1` layer it need not be non-D: at general saturation the
majority defect core can have internal edges.  Put

```text
epsilon=1[XY notin D]=|N_A(X) intersect N_A(Y)| in {0,1}. (73rnz_j)
```

If `epsilon=0`, then `XY` lies in T and its two full lines are disjoint.  If
`epsilon=1`, they have a unique common A-neighbor `v`.  There are no other
inside exceptional centers and `A[R]` contains only `XY`, so in this case
`v in M intersect S`.

As points of the majority design, `X` and `Y` each have replication one.
Their cross-shore D-degree is therefore `r` by (73r), already exhausted by
the `r` outside empty centers in the complete F--E defect core.  Consequently
every uncovered ordinary point `z` outside S is non-D to both `X` and `Y`.
For the q-point uncovered set `Z`, define the unique common neighbors

```text
x_z in N_A(X) intersect N_A(z),
y_z in N_A(Y) intersect N_A(z).                          (73rnz_k)
```

The full lines at `X,Y` lie inside S, so both witnesses lie in S.  If
`epsilon=0`, all q witness pairs are distinct, since a coincidence would be
a common neighbor of the D-pair `X,Y`.  If `epsilon=1`, then `x_z=y_z` iff
both equal v, equivalently iff `zv in A`.  Thus the reciprocal-private edge
carries q labeled two-line transversals in either case; sharing is absent in
the T-edge case and localized at the unique line-intersection point in the
non-D case.

In the `epsilon=1` case the shared coordinates number exactly two.  The point `v` is
ordinary, so its balanced line has `q/2` neighbors outside S.  Every outside
empty center `E_j` is non-D to `v` (the empty center's D-neighborhood is
exhausted on the exceptional core), and therefore has a unique common
A-neighbor with `v`.  This point lies on the empty line of `E_j`, hence is
one of the covered ordinary outside points.  Distinct empty lines are
disjoint, so the `r=q/2-2` empty centers account for exactly r distinct
outside neighbors of `v`.  There are no outside exceptional A-neighbors of
`v`: its two majority incidences are precisely `X,Y`, both inside, and an
empty line has no inside point.  It follows that

```text
|N_A(v) intersect Z| = q/2-r = 2.                        (73rnz_l)
```

By (73rnz_k), exactly these two z's have `x_z=y_z=v`.
Consequently the q transversals split canonically into two shared
coordinates and `q-2` unshared pairs.  The shared part is now the same
two-port size as the `a=1` endpoint, while the even `q-2` residue carries
the genuinely new occurrence-flow content.  In the `epsilon=0` case all q
transversals are unshared.

This two-line system is an exact cross-shore kernel, not only a count on Z.
Put `w=1_X-1_Y` and let `L_X=N_A(X)`, `L_Y=N_A(Y)`.  Since both lines are
full, they lie in S, and

```text
h:=Aw=1_(L_X)-1_(L_Y) is supported on S.                 (73rnz_m)
```

The endpoints `X,Y` have identical D-status at every outside vertex.  Every
outside empty center is D-adjacent to both, and the cross-shore D-degree r
of each private endpoint is already exhausted by these r empty centers.
Thus no other outside vertex -- full or ordinary -- is D-adjacent to either.
Hence `Dw` vanishes outside S.  Using `1^T w=0` in the square identity gives

```text
(Ah)|_(V setminus S)=(A^2w)|_(V setminus S)=0.           (73rnz_n)
```

Equivalently, if B is the A-incidence block from S to its complement, then
both `w` and `h` lie in `ker(B^T)`.  They are independent: h is nonzero on
the `q-1-epsilon` points of `L_X setminus (L_Y union {Y})`, where w
vanishes.  Thus

```text
nullity(B^T)>=2.                                         (73rnz_o)
```

Coordinatewise, every outside full or ordinary vertex has one common
neighbor with X and one with Y, while an outside empty center has zero with
both.  The signed line current therefore balances at every outside
occurrence simultaneously.  This is a closed aggregate transport identity
for the `a=2,s=0` branch, obtained without pairing individual transversal
labels or assuming a token-cycle closure.

Cancelling the two exceptional coordinates turns this kernel into a regular
occurrence graph.  Put

```text
u=(A+I)w=h+w,
U_+ = L_X setminus (L_Y union {Y}),
U_- = L_Y setminus (L_X union {X}).
```

Then u is `+1` on `U_+`, `-1` on `U_-`, and zero elsewhere.  By the
codegree dichotomy (73rnz_j),

```text
|U_+|=|U_-|=q-1-epsilon,
B^T u=0.                                                  (73rnz_p)
```

Every point of `U_+ union U_-` is ordinary and lies inside S, so its balanced
line has exactly `q/2` outside neighbors.  At an outside vertex, (73rnz_p)
says that the number of positive support neighbors equals the number of
negative support neighbors.  Each number is at most one: two neighbors from
the same side would give that outside vertex and X (or Y) as two common
neighbors of the corresponding pair, violating C4-freeness.  Hence every
outside vertex has support degree zero or two, and in the latter case it
joins exactly one `U_+` point to one `U_-` point.

Contract every active outside vertex to such an edge.  Two different outside
vertices cannot yield the same edge, since they would be two common
neighbors of its endpoints.  The resulting graph H is therefore simple and

```text
H is (q/2)-regular bipartite on U_+ disjoint_union U_-,
|E(H)|=(q/2)(q-1-epsilon).                               (73rnz_q)
```

Thus the aggregate kernel has an unconditional finite occurrence model:
a regular bipartite graph, rather than a conjectural pairing of transversal
tokens.  In particular H admits a one-factorization, and because `q/2` is
even for `k>=3`, its factors may be paired into cycle covers.  Any final
labelled obstruction in this placement must survive those genuine closed
cycles; closure itself is no longer a gap.

The occurrence graph has a canonical partial matching of private labels.
Label each edge of H by the outside vertex that was contracted to it.  Every
outside full center is active: it is non-D to X and Y by cross-D exhaustion,
and it cannot use the common point v in the `epsilon=1` case because v already
has majority replication two at X,Y.  Its X-witness cannot be Y either:
routing (60) puts every majority A-neighbor of the inside center Y inside S,
whereas the outside full center lies outside; symmetrically its Y-witness is
not X.  Hence the two witnesses lie in `U_+` and `U_-`.  There are exactly
`q/2` such centers.
Their H-edges form a matching.  Indeed a point of `U_+` already lies on the
full line X, so two additional outside-full neighbors would give majority
replication at least three; the same holds on `U_-`.  Consequently

```text
P_F := {H-edges labelled by F setminus S} is a matching,
|P_F|=q/2.                                                (73rnz_r)
```

Its matched endpoints are exactly the points of majority replication two
(the intersections with an outside full line), while the unmatched endpoints
are private points of X or Y.  Each side therefore contains

```text
q/2 matched points and q/2-1-epsilon private points.      (73rnz_s)
```

The inactive outside set is equally explicit.  Its cardinality is ambient
outside size minus `|E(H)|`:

```text
q^2/2-2 - (q/2)(q-1-epsilon)
  = q/2-2 + epsilon(q/2) = r+epsilon(q/2).               (73rnz_t)
```

For `epsilon=0` these are precisely the r outside empty centers.  For
`epsilon=1` they are those centers together with the `q/2` outside ordinary
neighbors of v; the latter are exactly the r covered points from (73rnz_l)
and its two uncovered shared-transversal points.  Thus H retains every
outside occurrence except the geometrically forced zero-current set, and
its distinguished F-matching records the private/intersection status at
both endpoints.  This supplies an exact private feature layer on top of the
conserved occurrence graph, in the format required by the shared tagged-
bundle rigidity program.

For this occurrence layer the shared reversal-rigidity interface is not a
target but an exact theorem.  Let a dart be an incidence `(p,z)` where
`p in U_+ union U_-` and the active outside label z contracts to an H-edge.
The unique positive/negative neighbor statement defines a fixed-point-free
route reversal `rho` pairing the two darts over z.  In the free module on
active outside labels define

```text
Phi(p,z) = +e_z  for p in U_+,
Phi(p,z) = -e_z  for p in U_-.                           (73rnz_u)
```

Then `Phi(rho d)=-Phi(d)`, and the realized dart sum vanishes coordinatewise:

```text
sum_(realized darts d) Phi(d)=0.                         (73rnz_v)
```

After quotienting by route reversal, one representative column remains for
each active z, and these columns are the distinct basis vectors `e_z`.
They are therefore linearly independent over every coefficient field.  The
coefficient-peeling argument of the shared tagged-bundle schema now forces
the two realized orientations over every z to have equal weight (indeed both
weights are one here).  Thus occurrence-weight reversibility is proved for
the dart-incidence form of the `a=2,s=0` transversal layer, uniformly in
epsilon.

Consequently every additive route-odd functional whose label is resolved at
the active outside occurrence cancels pairwise on H.  Any surviving
obstruction must either use the inactive zero-current set from (73rnz_t), or
couple labels belonging to different H-edges in a way not visible to the
private coordinate `e_z`.  This cleanly separates the solved local
reversibility problem from the remaining genuinely simultaneous label
transport.

This does **not** prove reversal symmetry for a ledger that counts each
H-edge only once and attaches a genuinely two-local label to its ordered
endpoint pair.  Such an edge label need not split into the two dart weights
used in (73rnz_u), and its reversal need not be a second realized occurrence.
The result solves precisely the incidence-separable part of the shared
rigidity problem; the nonseparable two-endpoint layer remains open, in exact
agreement with the one-port telescoping obstruction in the SRP lane.

The canonical F-matching (73rnz_r) does not by itself solve that two-local
problem.  Its edge tag is private but reversal-even: reversing an F-labelled
H-edge fixes the same outside full center, and both endpoints have majority
replication two.  Therefore the antisymmetrization of the bare tag

```text
(outside-full label, matched/matched endpoint status)
```

is zero.  The matching supplies privacy but no route-odd column.  A
nontrivial extension of `Phi` must additionally retain endpoint-resolved
secondary-fiber or defect data whose two values can differ under reversal,
and then prove conservation for that enriched tag.  This is exactly the
genuinely two-local gap isolated by the shared SRP/B3 analysis, now verified
inside the concrete pilot graph rather than inferred abstractly.

The first reversal-sensitive two-local tag has an exact complementary-slack
identity, rather than standalone conservation.  For an H-edge labelled by z
with endpoints `p_+ in U_+`, `p_- in U_-`, retain the ordered bits

```text
theta_+(p_+,z)=1[p_+z in D],
theta_-(p_-,z)=1[p_-z in D].
```

These are precisely the cross-shore T-incidences at the support points,
because every outside A-neighbor of `U_+ union U_-` is active and represented
in H.  Put `Theta_+`, `Theta_-` for their total sums over H.  Also let
`N_+`, `N_-` count the outside D-incidences at the two support sides that
are **not** A-edges.

Each side has exactly `q/2` replication-two points (the matched endpoints of
`P_F`) and `q/2-1-epsilon` private points.  By (73r), their outside D-degrees
are respectively `q-2` and `r=q/2-2`.  Hence the total outside D-incidence
on either side is the same number

```text
C_D=(q/2)(q-2)+(q/2-1-epsilon)r,
Theta_+ + N_+ = C_D = Theta_- + N_-.                    (73rnz_w)
```

Therefore

```text
Theta_+-Theta_- = -(N_+-N_-).                            (73rnz_x)
```

So the ordered H-edge defect tag is genuinely reversal-sensitive, but it is
not conserved by the current companion budgets: its residue is exactly the
opposite signed imbalance of non-A outside defect incidences.  The test does
not fail vaguely; it names the missing layer.  A viable enriched `Phi` must
either retain those non-A D-incidences as secondary-fiber/deletion data or
prove their signed imbalance vanishes by an additional simultaneous
identity.  This is the `a=2` incarnation of the SRP lane's conclusion that
per-layer route data must be kept before aggregate cancellation.

The Eulerian K-parity identity (20) does not make the residue in (73rnz_x)
vanish for free, but it translates it exactly.  For `k>=3`, both possible
outside D-degrees at a support point are even:

```text
r=q/2-2 = 0,          q-2 = 0                    (mod 2).
```

Thus pointwise `N_p=Theta_p (mod 2)`.  Let
`U=U_+ union U_-`.  Since subtraction and addition agree modulo two and
Theta counts every cross-shore T-incidence of U,

```text
N_+-N_- = Theta_++Theta_-
          = e_T(U,V setminus S)
          = e_T(U,S setminus U)                  (mod 2). (73rnz_y)
```

The last equality is exactly Eulerian cut parity for T.  Summing (20) over U
and using Eulerianity of K gives the parallel identity

```text
e_K(U,V setminus S)=e_K(U,S setminus U)
                   =e_T(U,S setminus U)           (mod 2). (73rnz_z)
```

Therefore the K machinery supplies no additional zero: it identifies the
slack parity with the internal T/K boundary of the occurrence support.  An
F2 rigidity argument would close if that internal boundary were even, but
its evenness is a new simultaneous statement, not a consequence of (20).
This prevents treating the local K-parity as a completed conservation law
and isolates the exact parity lemma still required.

The internal boundary in (73rnz_y) has no exceptional parity residue.  In
the `s=0` placement the inside exceptional centers are only X and Y.  When
`epsilon=1`, the additional line-intersection point v is ordinary, and the
edges `Xv,Yv` are non-T: the other core center is a common A-neighbor of
each edge.  The full line at X is

```text
{Y} disjoint_union U_+ disjoint_union ({v} if epsilon=1),
```

and similarly at Y.  Since every T-degree is even and `XY in T` exactly
when `epsilon=0`,

```text
e_T(U_+,{X}) = 1-epsilon,
e_T(U_-,{Y}) = 1-epsilon                    (mod 2).       (73rnz_z1)
```

Their sum is zero modulo two.  Consequently

```text
e_T(U,S setminus U)
  = e_T(U,(M intersect S) setminus U)        (mod 2).      (73rnz_z2)
```

Thus the F2 obstruction is entirely an ordinary-block boundary; no
exceptional mark remains to be tabulated.  Closing the `s=0` parity route is
equivalent to proving that the T-cut of U inside the ordinary residual block
is even.

The other `a=2` placement, `s=2`, has an exact four-bundle alternative.  Let
`E_1,E_2` be the inside empty centers and let `F_(i,0),F_(i,1)` be the two
outside-full leaves of the T-star at `E_i`.  Put

```text
U_(i,a)=N_T(F_(i,a)) intersect (M intersect S).
```

Each `U_(i,a)` is odd and nonempty, and the two bundles belonging to one
star are disjoint.  For leaves from different stars set

```text
n_(a,b)=|U_(1,a) intersect U_(2,b)| in {0,1}.             (73rnz_aa)
```

The upper bound is C4-freeness: two points in the intersection would be two
common A-neighbors of the corresponding leaf pair.  A point cannot belong
to three leaf bundles, because then it would meet both leaves of one star,
contradicting their disjointness.  Thus every ordinary port appearing in the
four bundles has leaf-incidence degree one or two; degree-two ports occupy a
unique cell of the binary matrix `N=(n_(a,b))`.

Let `s_(i,a)` count the degree-one ports in `U_(i,a)`.  The four odd bundle
equations give

```text
s_(1,a)+n_(a,0)+n_(a,1) = 1                       (mod 2),
s_(2,b)+n_(0,b)+n_(1,b) = 1                       (mod 2),
sum_a s_(1,a) = sum_(a,b)n_(a,b) = sum_b s_(2,b) (mod 2),
sum_(i,a) s_(i,a) = 0                             (mod 2). (73rnz_ab)
```

Hence the total number of singleton ports is even.  If it is positive, it
is at least two; at each such point the unique incident leaf T-edge leaves
an odd number of further T-edges to the rest of the graph, because the total
T-degree is even.  These are genuine external routing ports.

If N is a permutation matrix, its two occupied cells give distinct ordinary
points `p_0,p_1`, and the forced edges form the simple T-cycle

```text
E_1-F_(1,0)-p_0-F_(2,sigma(0))-E_2
   -F_(2,sigma(1))-p_1-F_(1,1)-E_1,                      (73rnz_ac)
```

where sigma is the corresponding permutation.  (The `p_i` may have further
T-edges, and even singleton ports may also be present, so this is a contained
cycle, not necessarily a whole component.)  Conversely, if N is not a
permutation matrix, the singleton total cannot be zero: zero would make all
four row/column margins odd and the binary 2-by-2 classification would force
N to be a permutation matrix.  Hence a non-permutation N forces at least two
external singleton ports.  The `s=2` placement therefore has the exhaustive
matrix-level alternative

```text
N permutation:     an explicit star-to-star T 8-cycle;
N non-permutation: an even positive family of at least two
                   external singleton T-ports.           (73rnz_ad)
```

This removes the vague “four odd bundles” description.  The parity of the
singleton population at each star is also fixed by the number of occupied
cross cells, while non-permutation of the cross matrix certifies that at
least two ports must enter the simultaneous residual transport.

The complete singleton-routing table follows directly from the four margin
parities in (73rnz_ab).  A leaf has an odd (hence nonzero) singleton bundle
exactly when its corresponding row or column of N has even sum.  Up to
permuting the two leaves at either star:

```text
shape of N                 forced odd singleton leaves        minimum
zero matrix                all four leaves                       4
one occupied cell          opposite leaf at each star            2
two, permutation           none (all singleton counts even)       0
two, same row              both leaves of star 1                  2
two, same column           both leaves of star 2                  2
three occupied cells       one leaf at each star                   2
all four cells             all four leaves                         4. (73rnz_ae)
```

For one occupied cell the forced leaves are the row and column not meeting
that cell.  For three occupied cells they are the row and column of sum two
(equivalently, the row and column opposite the missing cell).  Thus every
non-permutation state not only has external ports: their star/leaf locations
and parities are fixed by N.  The permutation state is the sole state with no
forced external leaf and is exactly the state carrying the 8-cycle
(73rnz_ac).

Each singleton port has its own exact absorption/exit bit.  Let p be a
degree-one port, incident in the four-bundle system to the unique leaf F.
Because p lies inside S, it is adjacent to no empty center (all empty lines
contain no inside point).  Majority replication at most two permits at most
one additional full-center neighbor.  If its edge to that secondary full
center is in T, write `eta_p=1`; otherwise put `eta_p=0`.  A secondary T-edge
cannot go to another one of the four leaves, since then p would be a
degree-two cross-star port rather than a singleton.  Hence it goes, when
present, to one of the remaining outside full centers.

Let `d_M^T(p)` count all remaining T-neighbors of p among ordinary points.
Even T-degree gives

```text
d_M^T(p) = 1+eta_p                              (mod 2). (73rnz_af)
```

Thus `eta_p=0` forces an odd nonempty ordinary T-exit bundle, while
`eta_p=1` absorbs the leaf parity at a secondary full center and leaves an
even ordinary exit count.  A private singleton port has `eta_p=0`
automatically.

For comparison, a degree-two cross-star port is already adjacent in T to
one leaf of each star.  Those two full incidences exhaust its majority
replication, and it has no empty-center neighbor, so its ordinary T-exit
count is even.  The four-bundle interface therefore has the exact local
alphabet

```text
cross port:              even ordinary exit;
singleton + no T switch: odd ordinary exit;
singleton + T switch:    even ordinary exit.             (73rnz_ag)
```

This is the star-layer version of the shared through/turn/switch
classification: the matrix N locates the through ports, while `eta_p`
decides whether each forced singleton is absorbed or launches an odd
ordinary transport bundle.

The switch bits themselves form a finite parity-transport graph.  There are
`q/2+2` outside full centers in this placement; removing the four star leaves
leaves exactly `q/2-2=r` residual full centers.  Form a bipartite graph J
from the four leaves to these r centers, with one edge for every singleton
port p having `eta_p=1`.  A leaf--center pair supports at most one J-edge:
two switching ports would be two common A-neighbors of those two full
centers.  Thus J is simple.

For a leaf L, write `m_L` for its row or column sum in N and let `lambda_L`
be the parity of all ordinary T-exit incidences from its singleton ports.
Summing (73rnz_af) over those ports and using (73rnz_ab) gives

```text
lambda_L = 1+m_L+deg_J(L)                       (mod 2).  (73rnz_ah)
```

At a residual full center G, every A-neighbor lies inside S, no empty center
is adjacent to it, and no other full center outside S can be adjacent to it.
Its T-neighbors are therefore ordinary inside points.  Split them into the
switching singleton ports and all remaining ordinary ports.  Even T-degree
gives

```text
gamma_G := #(remaining ordinary T-ports at G)
         = deg_J(G)                              (mod 2). (73rnz_ai)
```

Consequently

```text
sum_L lambda_L + sum_G gamma_G = 0               (mod 2), (73rnz_aj)
```

because the four constant terms and the two copies of every N- and J-edge
cancel.  The graph J therefore transports the margin-parity defects from
the four leaves to residual full centers; a switch does not erase a parity
charge, it moves it.

In fact the purely binary obstruction always vanishes.  Put
`b_L=1+m_L`, the forced leaf-charge before switches.  Since every occupied
cell of N contributes to two margins,

```text
sum_L b_L = 0                                      (mod 2). (73rnz_ak)
```

Choose one residual center `G_0` (there is one because
`r=q/2-2>=2`) and, in the abstract complete bipartite switch graph, join
`G_0` exactly to the leaves with `b_L=1`.  Then every leaf has
`deg_J(L)=b_L`, while `deg_J(G_0)=sum_L b_L` is even and every other residual
center has degree zero.  Equations (73rnz_ah)--(73rnz_ai) give

```text
lambda_L=0 for every leaf L,       gamma_G=0 for every center G. (73rnz_al)
```

This construction is simple and covers charge weights zero, two, and four;
at a charged leaf the odd singleton count guarantees at least one candidate
port.  It is deliberately only an abstract parity realization: the chosen
ports need not all admit the same secondary center `G_0`, or any prescribed
center at all.  Thus leaf charges, center capacities, simplicity, and parity
transport alone can never force an ordinary exit.  The remaining datum is
exactly the actual switch-eligibility relation -- which singleton port can
meet which residual full center in T -- together with its simultaneous
defect/intersection labels.  This is precisely the labeled-switch constraint
shared with the SRP dart system.

There is also a useful localization warning for that next datum.  If
`e=(L,G,p)` is an actual edge of J, then p already has the two full-center
neighbors L and G.  The majority replication bound is two, and p has no
empty-center neighbor, so

```text
N_A(p) intersect (E union F) = {L,G}.                    (73rnz_am)
```

In particular the realized source port p has no unused exceptional neighbor
with which to carry an off-route switch label.  Its direct source data are
only the consumed pair `(L,G)` and its even ordinary T-exit bundle from
(73rnz_af).  Therefore a nontrivial eligibility invariant cannot be an
on-port refinement of `eta_p`: it must compare e with the remaining
eligibility census at its endpoints, namely switches through other singleton
ports of L or other leaf ports at G, retaining the corresponding ordinary
exit/defect labels.  At the unlabelled graph level these are merely
`N_J(L) setminus {G}` and `N_J(G) setminus {L}` and handshaking again
telescopes.  The required information is the off-occurrence, consumed-port
fiber census rather than the realized edge atom itself -- exactly the same
distinction exposed by the SRP on-route atomization test.

The star geometry nevertheless supplies the first exact off-occurrence
cross-tag.  Let E be the inside empty center whose star contains L.  For a
switch `e=(L,G,p)`, consider the routed three-vertex wedge

```text
E -- L -- p.
```

The residual center G is adjacent to p by definition.  It is not adjacent
to E, because the only outside-full neighbors of E are its two star leaves,
and it is not adjacent to L, because a residual outside full center has no
outside-full neighbor.  Hence

```text
sum_(x in {E,L,p}) 1[Gx in A] = 1,                       (73rnz_an)
```

with p the unique incidence.  Thus `(E,L,p) x G` is literally an actual
route label cross-tagged by a singly incident off-route exceptional fiber.
It is private at full resolution: the route label contains p, and a fixed
leaf--center pair has at most one common port by C4-freeness.  This is the
Baer-star instance of the resolved singleton-incidence census in the SRP
dart lane.

Privacy is not conservation.  Summing these atoms without their remaining
endpoint census gives only `|E(J)|`, and reversing the description of the
same switch does not create a second realized occurrence with opposite
weight.  A load-bearing use of (73rnz_an) must therefore cross-correlate it
with the other-port deletion profiles identified after (73rnz_am), or prove
an occurrence-level balance for those profiles.  The local star supplies
the required private column, but not yet its conserved coefficient.

The bare endpoint-deletion census has one canonical two-local scalar.  Write
`d_L=deg_J(L)` and `d_G=deg_J(G)`.  From an oriented switch occurrence, the
number of other switches available at its leaf endpoint is `d_L-1`, and the
number at its residual-center endpoint is `d_G-1`.  Summing over occurrences
and dividing the ordered pair count by two gives

```text
Delta_J
 := sum_L C(d_L,2) - sum_G C(d_G,2)
  = (1/2) sum_(e=(L,G) in E(J)) ((d_L-1)-(d_G-1)).       (73rnz_ao)
```

Equivalently, if X is the binary leaf-by-center incidence matrix of J, the
two terms are its row-degree and column-degree collision masses (the
off-diagonal parts of the corresponding degree-Gram expansion).  A pair
of distinct switch edges cannot share both endpoints because J is simple;
therefore every nonzero coordinate of this difference has a unique
leaf-sharing or center-sharing witness, never both.  Reversing the two shores
negates `Delta_J`.  This is the first genuinely two-local, reversal-odd
statistic carried by the other-port deletion profiles.

But (73rnz_ao) is an identity, not a vanishing theorem.  Handshaking fixes
the one-edge marginals and says nothing about the difference of the two
wedge counts; even imposing `d_L=b_L` and even `d_G` from the charge-free
abstract model does not determine either binomial sum modulo two.  Thus the
endpoint census supplies the correct private row/column-Gram defect, while
an SRP-derived occurrence balance is still needed to conserve it or cancel
it against the ordinary-exit/defect census.

The privacy compression has one exact collision sector.  The port p may be
dropped from the label `(E,L,p) x G`: for fixed `(L,G)`, C4-freeness gives at
most one common port, so `(L,G)` still identifies the switch occurrence.
Now drop the leaf and retain only the star-level cross-tag `(E,G)`.  It has
multiplicity at most two, one through each of the two leaves of E.  If both
occurrences exist, with ports `p_0,p_1`, their forced T-edges contain

```text
E-L_0-p_0-G-p_1-L_1-E,                                  (73rnz_ap)
```

a simple T 6-cycle.  The leaves are distinct; the ports are distinct because
the two same-star bundles are disjoint; and neither port equals an
exceptional center.  Conversely, a repeated `(E,G)` switch label is exactly
such a two-leaf switch collision and supplies this cycle.

Thus the off-route switch coordinate is private after compression to
`(E,G)` unless the geometry already contains a canonical star-to-residual
6-cycle.  This is the precise collision alternative hidden by the bare J
degree census.  It does not by itself exclude the collision -- T may contain
6-cycles -- but it replaces a generic privacy failure by a concrete short
routed object whose remaining ordinary/defect attachments can be audited.

The remaining attachment census is already coupled to the canonical graph
K.  Fix an inside empty star center E and a residual outside full center G.
Every A-neighbor of E lies outside S, while every A-neighbor of G lies inside
S, so E and G have no common A-neighbor; they are also nonadjacent.  Hence
`EG in D`.  By (21), the A-edges between `N_A(E)` and `N_A(G)` form a
matching and their number is `A^3(E,G)`, with

```text
1[EG in K] = A^3(E,G)                              (mod 2). (73rnz_aq)
```

Every switch from a leaf L of E to G through p contributes the distinguished
cross-matching edge `Lp`: indeed `L in N_A(E)`, `p in N_A(G)`, and `Lp in T`.
Let `c_(E,G)` be the number of these switch edges (zero, one, or two by
(73rnz_ap)), and let `rho_(E,G)` count all remaining edges of the
`N_A(E)`--`N_A(G)` cross matching.  Then

```text
1[EG in K] = c_(E,G)+rho_(E,G)                    (mod 2). (73rnz_ar)
```

This identifies the required secondary-fiber label exactly.  A private
star-level switch (`c_(E,G)=1`) is detected by K unless the residual matching
census `rho_(E,G)` is odd; a two-leaf collision contributes the explicit
6-cycle but cancels from this parity.  Thus the compensation is no longer an
unspecified defect tag: it is the parity of the cross-neighborhood matching
after deleting the realized leaf--port switch edges.  Summing (73rnz_ar)
against the shore relation (20) is the concrete next conservation test.

That test gives an exact centerwise balance.  Fix a residual full center G.
All of its T-neighbors lie in S, so their number is the even integer
`deg_T(G)`.  Applying (20) at G therefore says that its K-incidence into S
is even.  The only exceptional vertices inside S are the two empty centers
`E_1,E_2`; all remaining inside vertices are ordinary.  Hence, modulo two,

```text
sum_(i=1,2) 1[E_i G in K]
   = deg_K(G, M intersect S)

sum_(i=1,2) (c_(E_i,G)+rho_(E_i,G))
   = deg_K(G, M intersect S).                           (73rnz_as)
```

The second line substitutes (73rnz_ar).  Thus the cross-tagged switch atoms
do have an occurrence-level conservation law, but only after adjoining two
specific secondary ledgers: the unused cross-neighborhood matching edges
`rho` and the ordinary inside K-incidences at G.  Bare J loses both and hence
cannot see (73rnz_as).  This is the exact Baer-side source-times-consumed-
fiber balance sought by the parallel SRP/B3 analysis; the remaining task is
to resolve the ordinary K term into the same private route labels, or show
that its aggregate contribution vanishes in the terminal pairing.

The residual matching term rho has a canonical finite atomization.  For an
edge `xy` of the `N_A(E)`--`N_A(G)` cross matching, retain the endpoint type

```text
chi(x)=leaf if x is one of the two star leaves of E,
       ordinary otherwise,
```

and the three-bit T-word on the length-three route

```text
E-x-y-G:  (1[Ex in T], 1[xy in T], 1[yG in T]).          (73rnz_at)
```

If x is a leaf L, then `EL in T`.  Moreover y is adjacent to the two full
centers L and G, so the replication-two cap prevents y from meeting any
other leaf.  If additionally `Ly in T`, then y lies in L's bundle and is
automatically a singleton port in the four-bundle system.  Consequently

```text
switch edge  iff  chi(x)=leaf and the T-word is 111.     (73rnz_au)
```

Thus `c_(E,G)` is exactly the leaf-111 cell of the matching, while
`rho_(E,G)` is the disjoint union of every other endpoint/word cell.  The
secondary residue in (73rnz_as) is therefore not an amorphous remainder: it
is a finite labeled route alphabet, with the desired source cell removed.
Any cancellation with the ordinary K term can now be sought cellwise, and
failure can be localized to a specific non-111 or ordinary-source route.

The ordinary K term in (73rnz_as) can likewise be resolved entirely into
incidence atoms.  For an ordinary inside vertex z nonadjacent to G, put

```text
nu_(G,z) = |N_A(G) intersect N_A(z)| in {0,1},
mu_(G,z) = A^3(G,z)                              (mod 2).
```

Because K is disjoint from A, equation (17) gives on this non-A pair

```text
1[Gz in K] = nu_(G,z)+mu_(G,z)                  (mod 2). (73rnz_av)
```

Here `nu` is either absent or has one unique common-neighbor witness, while
`mu` is the parity of the matching of A-edges between `N_A(G)` and
`N_A(z)`.  Therefore (73rnz_as) becomes the fully incidence-resolved law

```text
sum_i (c_(E_i,G)+rho_(E_i,G))
 = sum_(z in M intersect S, Gz notin A)
       (nu_(G,z)+mu_(G,z))                     (mod 2). (73rnz_aw)
```

Both sides now consist of unique common-neighbor atoms and linear
cross-neighborhood matchings.  No auxiliary K-edge remains.  The unresolved
step is narrower: construct a label-preserving pairing (or signed capacity
inequality) between the route cells (73rnz_at) on the left and the
common-neighbor/cross-matching atoms on the right.  C4-freeness supplies
privacy within each fiber, but not this cross-fiber conservation by itself.

There is a decisive limitation on the unweighted form of this conservation.
Suppose, toward the desired exit contradiction, that every ordinary exit
charge vanishes.  In particular (73rnz_ai) gives
`deg_J(G)=gamma_G=0` modulo two at every residual center.  But

```text
sum_(i=1,2) c_(E_i,G) = deg_J(G) = 0              (mod 2),
```

so (73rnz_as) collapses to

```text
sum_(i=1,2) rho_(E_i,G) = deg_K(G,M intersect S)  (mod 2). (73rnz_ax)
```

The switch atoms themselves disappear from the aggregate equation exactly
in the charge-free regime that must be excluded.  Hence (73rnz_aw), although
an exact incidence-resolved conservation ledger, cannot be applied after
summing away the star label.  A terminal must assign a nonconstant joint
weight to `(E,leaf,G,route-cell)` before the two-star sum, with the matching
weight transported to the `nu/mu` atoms.  This rules out any proof based only
on the centerwise scalar balance and matches the independent failure of
additive-linear census potentials in the B3 ledger.

There is a sharp linear-algebra dichotomy for producing the missing star
weight.  Over F2 let `h=e_(E_1)+e_(E_2)`.  Either there is a vector
`v in ker A` with

```text
v(E_1)+v(E_2)=1,                                      (73rnz_ay)
```

or the functional h annihilates all of `ker A`.  Since A is symmetric, the
latter condition is equivalent to `h in im A`; hence there is an x with

```text
A x = h.                                               (73rnz_az)
```

In the first branch, the general identity `M_K v=M_T v` (the same proof as
(19), using `Av=0`) supplies a transport equation whose coefficients
distinguish the two empty stars before they are summed.  It also introduces
the other v-weighted exceptional/ordinary cells, which must be retained; no
automatic contradiction is claimed.

In the second branch, applying A once more gives

```text
A^2 x = A h = 1_(N_A(E_1)) + 1_(N_A(E_2)).             (73rnz_ba)
```

The two neighborhoods are disjoint because the empty centers have no common
A-neighbor.  Moreover A is alternating, so
`0=x^T A x=x(E_1)+x(E_2)`; adding the constant kernel vector if necessary
normalizes `x(E_1)=x(E_2)=0`.  Thus failure of every kernel separator is not
featureless: the canonical two-pole right-hand side admits a normalized
potential whose second derivative is exactly the union of the two empty
lines (the potential itself need not be unique).  The joint-state terminal
may therefore split cleanly into a kernel-separator transport branch and a
two-pole potential branch, rather than assuming a star character exists.

The two-pole branch already contains an actual route.  Use the normalization
`x(E_1)=x(E_2)=0` and put `X=supp(x)`.  In the cut graph
`A[X,V setminus X]`, a vertex outside X has cut-degree parity `(Ax)_v`, while
a vertex in X has cut-degree parity

```text
q-(Ax)_v = (Ax)_v                                  (mod 2),
```

because q is even.  Equation (73rnz_az) therefore says that the only
odd-degree vertices of this cut graph are `E_1,E_2`.  Hence they lie in the
same component and the cut graph decomposes into an `E_1`--`E_2` path plus
closed trails:

```text
E_1 -- ... -- E_2  inside A[X,V setminus X].             (73rnz_bl)
```

At either endpoint the first cut edge is a T-edge exactly when it uses one
of that empty center's two full leaves; every other endpoint edge goes to an
ordinary point on the empty line and is non-T by (73rnd).  Thus the image
branch is not merely a linear potential: it yields a two-pole A-route with a
finite leaf/ordinary endpoint decoration, plus Eulerian cut corrections.
This is the natural object to compare with the six-edge cross-star transports
in (73rnz_bb).

The two-pole syndrome has its own sharp packing bound.  Choose
`p in X intersect N_A(E_1)`, which exists because `(Ax)_(E_1)=1`.  The empty
lines are disjoint, so `p` is not adjacent to `E_2`.  For each
`Y in N_A(p) setminus {E_1}`, one has `(Ax)_Y=0` while `p in X intersect
N_A(Y)`; hence there is another point

```text
x_Y in (X setminus {p}) intersect N_A(Y).
```

The `q-1` points `x_Y` are distinct: if the same point served Y and Y', then
the pair `p,x_Y` would have the two common A-neighbors Y,Y', contradicting
C4-freeness.  Therefore

```text
|X| >= q.                                                (73rnz_bm)
```

If equality holds, X consists of p and these `q-1` witnesses.  Since
`(Ax)_(E_2)=1` and p is not adjacent to `E_2`, some witness `x_Y` is adjacent
to `E_2`, giving the explicit A-path

```text
E_1-p-Y-x_Y-E_2.                                        (73rnz_bn)
```

Thus the image branch splits further into a minimum two-pole coset carrying
a length-four route, or a support of size at least `q+1`.  This is the
syndrome-two analogue of the earlier `q+1` lower bound for nonzero kernel
supports.

The equality structure is a two-pencil design.  Let
`r in X intersect N_A(E_2)`.  Apply the same q-point packing argument based
at r.  If a second point of X lay on the `E_2` line, then in the equality
packing it would also share with r one of the other `q-1` line centers,
giving that pair two common A-neighbors.  Hence

```text
X intersect N_A(E_1) = {p},
X intersect N_A(E_2) = {r}.                            (73rnz_bo)
```

Moreover every line center `Y in N_A(p) setminus {E_1}` contains exactly
the two X-points `p,x_Y`: a third X-point is already the witness assigned to
some other line through p and would again give two common neighbors with p.
The analogous statement holds for the q-1 non-pole lines through r.  Thus
the two pencils partition `X setminus {p}` and `X setminus {r}` into
singletons, and their shared member is the unique common line center of
`p,r` occurring in (73rnz_bn).  Any minimum two-pole potential must realize
this exact paired-pencil geometry.

It also has an exact defect signature.  Let
`L=N_A(E_1) union N_A(E_2)`.  Since `|X|=q` is even, the defining relation
`D=A^2+J+I` and (73rnz_ba) give

```text
D 1_X = 1_L + 1_X.                                      (73rnz_bp)
```

The two-pencil structure says `L intersect X={p,r}`.  Consequently p and r
have even D-incidence into X -- in fact zero, because each other X-point
shares with the pole a current line from its pencil -- while every point of
`X setminus {p,r}` has odd D-degree into X.  On the other shore, every point
of `L setminus {p,r}` has odd D-incidence into X and every point outside
`L union X` has even incidence.  Thus the minimum two-pole A-route comes with
a completely explicit D-boundary parity profile, suitable for the same
source/defect cross-tag ledger as (73rnz_aw).

The canonical K-transport extends to this syndrome with an explicit source.
Recall `H=A^2(A+I)` and `K=H+T` over F2.  From `Ax=h` and
`A^2x=Ah=1_L`,

```text
K x = T x + A^2 h + A h
    = T x + D h + h + 1_L.                              (73rnz_bq)
```

The second equality uses `A^2h=Dh+h`, since h has even weight and
`D=A^2+J+I`.  Thus (73rnz_bq) is the inhomogeneous two-pole analogue of the
kernel-shore transport (19): K-incidence into X equals T-incidence into X,
corrected only by adjacency in D to the two poles, the pole indicators, and
the two empty lines.  In the minimum branch every one of those correction
classes is already resolved by (73rnz_bo)--(73rnz_bp).  This supplies the
promised K-coupling input for pricing the two-pencil defect units; it does not
yet prove that their total contribution vanishes.

Here the exceptional-core census removes the apparent D-source entirely.
Every empty center has

```text
N_D(E_i)=F union (E setminus {E_i}),
```

because these `q-1` exceptional vertices exhaust its regular D-degree.
Consequently the two columns differ only at the poles themselves and
`Dh=h`.  Equation (73rnz_bq) simplifies to

```text
K x = T x + 1_L.                                        (73rnz_bs)
```

Thus K- and T-incidence into X agree exactly off the two empty lines, while
every point of L carries one correction unit.  The lines are disjoint, so
each correction has a unique empty-center owner label.  This is an exact
identity plus a localized exceptional alphabet -- the Baer-side instance of
the near-identity/pivot-neighborhood structure isolated by the B3 dual
ledgers.  Unlike the instance-specific B3 alphabet, L has size `2q`; further
pricing must use its two line fibers rather than treating it as uniformly
bounded.

The original partial Baer involutions compress those two fibers.  On the
line `N_A(E_i)`, the only T-neighbors of `E_i` are its two full leaves.
They are precisely the two points omitted from the domain of `iota_(E_i)`;
the remaining `q-2` ordinary line points form fixed-point-free transposition
pairs.  Thus each correction line has the canonical decomposition

```text
N_A(E_i)
 = {two full leaves}
   disjoint-union ((q-2)/2 ordinary Baer pairs).          (73rnz_bt)
```

Over F2, any correction price constant on an `iota_(E_i)` pair cancels on
that pair.  The invariant part of the q-point correction therefore reduces
to the two leaf atoms, four in total across both lines.  Conversely, any
surviving ordinary correction must be antisymmetric inside a specifically
labeled Baer pair.  This converts the q-scaled near-identity exception into
a bounded leaf alphabet plus paired ordinary fibers -- exactly the
pivot/relay split needed for joint pricing.

At the two poles this transport detects the endpoint type exactly.  The pair
`E_1E_2` is a D-edge in the minority clique, neither pole lies in L, and
`h(E_i)=1`, so the last three correction terms in (73rnz_bq) cancel at
`E_i`.  Using `X intersect N_A(E_i)={p_i}` from (73rnz_bo) and the exact
empty-star T-neighborhood (73rnd) gives

```text
deg_K(E_i,X) = deg_T(E_i,X)
             = 1[p_i is one of the two full leaves of E_i]  (mod 2).
                                                               (73rnz_br)
```

Thus the leaf-versus-ordinary endpoint decoration of the two-pole cut route
is not an external case label: it is the parity of the canonical K-fiber from
the pole into the rest of the minimum support.  A leaf endpoint carries an
odd K-residual and an ordinary endpoint an even one.  This is precisely the
source-times-secondary-fiber form required by the joint pricing ledger.

In the minimum branch, the line correction is an exact one-unit dichotomy.
Let `sigma_i` be the parity of the ordinary `iota_(E_i)` transpositions with
exactly one endpoint in X.  Since the line meets X in the unique point p_i,

```text
sigma_i = 0  if p_i is a full leaf,
sigma_i = 1  if p_i is ordinary.                         (73rnz_bu)
```

In the second case the sole split pair is the Baer pair containing p_i; in
the first case every ordinary pair lies wholly outside X.  Combining
(73rnz_bu) with the endpoint detector (73rnz_br) gives

```text
deg_K(E_i,X) + sigma_i = 1                       (mod 2). (73rnz_bv)
```

Thus each pole supplies one binary demand, carried in exactly one of two
channels: an odd K-fiber when the endpoint is a leaf, or one private split
Baer pair when it is ordinary.  The split-pair channel is a literal private
unit; the K-channel is presently controlled only in parity.  The two-pole
minimum block is therefore a binary transfer cell, not merely an unstructured
profile.  Closing the branch requires resolving the odd K-fiber into priced
units and showing that the downstream relay ledger cannot pay both pole
demands simultaneously.

The K-channel has the same incidence atomization as (73rnz_av).  For
`z in X setminus {p_i}`, the unique pole-line intersection implies
`E_i z notin A`.  The empty center's D-neighborhood is exactly
`F union (E setminus {E_i})`, so this non-A pair has codegree one exactly
when z is ordinary and codegree zero exactly when z is exceptional.  If
`mu_(E_i,z)=A^3(E_i,z)` modulo two denotes the parity of its
cross-neighborhood matching, (17) gives

```text
1[E_i z in K] = 1[z in M] + mu_(E_i,z)            (mod 2). (73rnz_bw)
```

(The point p_i itself is A-adjacent to E_i and contributes no K-edge.)
Summing (73rnz_bw) over the other `q-1` support points and using
(73rnz_br) yields

```text
1[p_i is a leaf]
 = |M intersect (X setminus {p_i})|
   + sum_(z in X setminus {p_i}) mu_(E_i,z)        (mod 2). (73rnz_bx)
```

Thus the odd K-fiber is fully resolved into ordinary endpoint-type units and
cross-neighborhood matching atoms, each matching linear by C4-freeness.  In
the ordinary-endpoint branch the same right side is even and the private
split Baer pair carries the pole demand instead.  Both channels of
(73rnz_bv) are now expressed in the common source/type/matching alphabet.

The endpoint-type terms cancel completely between the two descriptions.
Put `m_X=|M intersect X|` and
`o_i=1[p_i is ordinary]`.  Since every point on the empty line is either a
full leaf or ordinary,

```text
1[p_i is a leaf] = 1+o_i,
|M intersect (X setminus {p_i})| = m_X+o_i        (mod 2).
```

Substitution into (73rnz_bx) gives, separately for both poles,

```text
sum_(z in X setminus {p_i}) mu_(E_i,z) = 1+m_X    (mod 2).
                                                               (73rnz_by)
```

In particular the two pole cross-matching ledgers have identical parity and
their combined total is even.  This is a genuine reversal balance intrinsic
to the minimum two-pencil block: leaf/ordinary endpoint changes move the
demand between the type bit and split-pair channel but do not change the
total matching parity seen from either pole.  What remains is labelwise
pairing of those matching atoms, not aggregate conservation.

The labelwise reversal defect is itself canonical.  On the common index set
`X setminus {p,r}`, both pole pairs are non-A, and hence

```text
mu_(E_1,z)+mu_(E_2,z)
  = (A^3 h)_z
  = (A^2 1_L)_z.                                       (73rnz_bz)
```

The last equality uses `Ah=1_L`.  The two pole sums in (73rnz_by) have only
two unmatched indices: r occurs only in the `E_1` sum and p only in the
`E_2` sum.  Their combined evenness is therefore the closed boundary law

```text
mu_(E_1,r)+mu_(E_2,p)
 + sum_(z in X setminus {p,r}) (A^3 h)_z = 0      (mod 2). (73rnz_ca)
```

The apparent cochain actually vanishes in the rigid minimum branch.  As
shown below, `A^2h=0`, and hence `A^3h=0`.  Therefore (73rnz_bz)--(73rnz_ca)
sharpen to

```text
mu_(E_1,z)=mu_(E_2,z)       for z in X setminus {p,r},
mu_(E_1,r)=mu_(E_2,p).                                  (73rnz_caa)
```

Pointwise pole reversal is already exact on the common domain, and the two
unmatched endpoint parities agree.  All remaining content is finer than the
binary `mu` labels: it lies in the owner/occurrence decomposition of the two
endpoint atoms.

In fact the whole matching ledger has a direct `Omega` price.  Recall from
(9) that

```text
M_Omega=A^3+J+I.
```

For every `z in X setminus {p_i}`, the pair `E_i,z` is non-A and has distinct
ends.  Hence `J_(E_i,z)=1`, `I_(E_i,z)=0`, and

```text
mu_(E_i,z)=(A^3)_(E_i,z)=1+(M_Omega)_(E_i,z).
```

There are `q-1` such indices, an odd number because `q` is even.  Summing and
using (73rnz_by) therefore gives, separately at the two poles,

```text
deg_Omega(E_i, X setminus {p_i}) = m_X             (mod 2).
                                                               (73rnz_cb)
```

Thus the common matching parity is not a new cross-neighborhood quantity:
after the universal odd-size offset is removed, it is exactly the parity of
one canonical `Omega` shore degree, and both pole degrees equal the same
ordinary mass `m_X`.  Equivalently, (73rnz_ca) is the evenness of the sum of
these two restricted `Omega` degrees.  This is the joint price needed to
compare the two-pole route with the charge-free `Omega/D` Gram bit: any
remaining contradiction must distinguish the two pole labels or control
`m_X`; it cannot come from their unlabelled total.

The explicit D-boundary profile (73rnz_bp) does control that mass.  Neither
pole belongs to `X` by normalization.  Neither belongs to `L`: there are no
loops, and the two inside empty centers are nonadjacent because each empty
line has no A-neighbor in the occupied shore.  Therefore

```text
deg_D(E_i,X)=0                                           (mod 2).
```

But the exhausted neighborhood
`N_D(E_i)=F union (E setminus {E_i})` says that this degree is exactly the
number of exceptional vertices of X.  Since `F`, `E`, and the ordinary set
`M` partition the vertices, `|X|=q` is even, and `E_i notin X`, it follows
that

```text
m_X=|M intersect X|=0                                   (mod 2). (73rnz_cc)
```

Consequently (73rnz_by) and (73rnz_cb) sharpen simultaneously to

```text
sum_(z in X setminus {p_i}) mu_(E_i,z)=1,
deg_Omega(E_i, X setminus {p_i})=0               (mod 2), (73rnz_cd)
```

for each pole separately.  Thus each pole has an odd cross-matching demand
but an even restricted `Omega` degree: the universal complement bit between
`A^3` and `M_Omega` is the entire parity discrepancy.  There is no
ordinary-mass escape in the minimum two-pencil branch.

However, the odd restricted ledger closes tautologically at its omitted
endpoint.  From `Ax=h` and `Dh=h`,

```text
A^3 x=A^2h=Dh+h=0.
```

Therefore the full `A^3` row of either pole has even sum on X, and

```text
sum_(z in X setminus {p_i}) mu_(E_i,z)
  = (A^3)_(E_i,p_i).                                    (73rnz_ce)
```

The endpoint pair is an A-edge.  Omega has no A-edges, so (9) gives
`(A^3)_(E_i,p_i)=1`.  Thus (73rnz_cd)'s oddness is exactly the universal
adjacent endpoint complement; by itself it is not an unpaid relay demand.
Any terminal must retain a finer occurrence label that prevents this
endpoint closure from being the whole story.

This also rules out every higher unlabeled walk refinement.  From `A^3x=0`,

```text
A^m x=0 for every m>=3.                                  (73rnz_cf)
```

Hence no operator that is merely a polynomial in A with all terms of degree
at least three can activate a secondary defect on the two-pole support.
Longer walk counts only repeat the same endpoint cancellation.  A successful
activation identity must break the commutative A-polynomial algebra, for
example by inserting an owner/mate diagonal projection between adjacency
steps.  This matches the independent SRP activation gap: its primary odd bit
also does not currently imply a nonzero secondary-resolved source defect.

The smallest such decorated operator already recovers the endpoint owner
type.  For a type class `C in {F,E,M}`, let `P_C` be its diagonal indicator
and put, in characteristic two,

```text
kappa_C=(A P_C+P_C A)x.                                  (73rnz_cg)
```

This is the commutator of adjacency with the owner projection.  At a pole
`E_i`, the first term counts C-type points of X on its line, while the second
term is `1[E_i in C]` because `Ax=h`.  The two-pencil equality says the line
meets X only at `p_i`, and (73rnz_bt) says that endpoint is leaf or ordinary,
never empty.  Hence

```text
kappa_F(E_i)=1[p_i is a leaf],
kappa_M(E_i)=1[p_i is ordinary],
kappa_E(E_i)=1.                                          (73rnz_ch)
```

Their sum is zero, as it must be because `P_F+P_E+P_M=I` and the commutator
with I vanishes.  Thus the noncommuting activation is not hypothetical: its
pole restriction is exactly the leaf/split-pair binary transfer cell
(73rnz_bu)--(73rnz_bv), expressed as an owner-marked commutator.  What is not
yet controlled is the support of `kappa_C` away from the poles, or a global
identity forcing its marked endpoint units into the SRP/Baer gauge class.

There is nevertheless an immediate activation dichotomy.  Every commutator
has even total mass.  Indeed, over F2,

```text
1^T kappa_C
 = 1^T A P_C x + 1^T P_C A x
 = q 1^T P_C x + |C intersect {E_1,E_2}| = 0,            (73rnz_ci)
```

because q is even and each type class contains either both poles (`C=E`) or
neither (`C=F,M`).  Hence the mass of `kappa_C` away from the poles equals
its pole mass.  If exactly one endpoint is a leaf and the other ordinary,
(73rnz_ch) gives

```text
|supp(kappa_F) setminus {E_1,E_2}| = 1,
|supp(kappa_M) setminus {E_1,E_2}| = 1              (mod 2). (73rnz_cj)
```

Thus the mixed endpoint-type branch necessarily activates nonprivate marked
units in both owner channels.  Private endpoint payment can survive only
when the two endpoints have the same type (both leaves or both ordinary).
This reduces the activation gap from four endpoint decorations to two
same-type branches.

The activated support is more sharply localized.  Symmetry of A gives

```text
x^T kappa_C
 = x^T A P_C x + x^T P_C A x = 0.                       (73rnz_cja)
```

Thus every owner commutator has even support inside X as well as even total
support.  In the mixed-type branch, each of `kappa_F,kappa_M` has exactly one
pole unit, and the poles lie outside X.  Consequently each channel has an
odd number of further support points in
`V setminus (X union {E_1,E_2})`.  The nonprivate activation is therefore an
external-shore relay, not an internal cancellation hidden inside X.

For scope, the exact source formula is

```text
kappa_C=A 1_(X intersect C)+P_C h.                       (73rnz_cjb)
```

Off the poles it records the parity of C-crossing A-incidences into X.  This
makes `kappa_C` a canonical marked source syndrome, but does not yet express
it as a sum of two-ended relay-boundary columns: an A-dart from outside X is
one-ended in (73rnz_cjb).  Nonempty external support is therefore activation,
not yet a quotient-span or trail solution.  Producing that boundary
decomposition is precisely the remaining gauge-coupling step.

Defect connectivity supplies that decomposition if one first forgets the
fine route labels.  Let `partial_D` be the vertex--edge incidence matrix of
D over F2.  Since D is connected,

```text
im(partial_D)={vertex vectors of even mass}.
```

Thus (73rnz_ci) gives, for every owner class C, a D-edge chain `r_C` with

```text
partial_D r_C=kappa_C.                                  (73rnz_cjc)
```

In the mixed branch this chain joins the pole unit to an odd collection of
external marked units; in the ordinary branch it can be adjoined to the two
canonical mate relays.  This is an actual two-ended boundary solution, but
it still forgets which D-edges admit the route cells (73rnz_at).

The gauge ambiguity of (73rnz_cjc) has an exact cut/cycle dichotomy.  Let
`k_D` be the indicator of K restricted to the D-edges.  The price

```text
<k_D,r_C>
```

is independent of the chosen D-chain exactly when `k_D` annihilates the
cycle space of D, equivalently (because D is connected) when `k_D` is a cut
of D.  Otherwise there is a D-cycle Z with

```text
<k_D,1_Z>=1.                                             (73rnz_cjd)
```

Hence gauge coupling now has two concrete exits: identify the cut potential
and evaluate it on `kappa_C`, or price an odd-K holonomy cycle.  The remaining
difficulty is not boundary existence; it is transporting either object into
the finite owner/T-word route alphabet without losing its label.

The cut exit has a concrete normal form.  If
`k_D(uv)=t(u)+t(v)` on D-edges, then every T-edge has K-value zero and hence

```text
t(u)=t(v)                    for uv in T.                (73rnz_cje)
```

On a non-A D-edge, `K=Omega+D`, so

```text
1[uv in Omega]=1+t(u)+t(v).                              (73rnz_cjf)
```

Moreover symmetry of A evaluates the pairing-independent chain price as

```text
<k_D,r_C>=<t,kappa_C>
 = <A t,P_C x>+<t,P_C h>.                               (73rnz_cjg)
```

For `C=F,M` the last term vanishes, so the price is exactly the `At`-mass on
the C-type part of X.  Thus the cut branch is no longer an abstract
possibility: it asks whether a T-component-constant two-coloring satisfying
(73rnz_cjf) can have the owner-restricted `At` parity forced by activation.
The holonomy branch instead supplies the explicit odd-K D-cycle (73rnz_cjd).

That holonomy already lies in the common matching alphabet.  A T-edge has
K-value zero.  On a non-A D-edge `uv`, the codegree term `A^2_(u,v)` is zero,
and (17) gives

```text
1[uv in K]=(A^3)_(u,v)=mu_(u,v).
```

Therefore an odd-holonomy cycle Z satisfies

```text
sum_(uv in E(Z) setminus T) mu_(u,v)=1.                 (73rnz_cjh)
```

Each summand is the parity of a C4-linear cross-neighborhood matching.  The
cycle exit thus needs no further atomization; it is already an odd closed
matching ledger.  Only the cut-potential exit still lacks a contradiction or
a transport into the owner/T-word capacity system.

The cut exit also has an exact transport to that alphabet.  Let `K_D` be the
subgraph of K on D-edges and put `O=K setminus D`.  Under the cut hypothesis,
the adjacency matrix of `K_D` has entry `D_(u,v)(t(u)+t(v))`, so

```text
K_D x=D(t x)+t(Dx).
```

Using the minimum-shore profile `Dx=1_L+x` from (73rnz_bp) and the K-transport
`Kx=Tx+1_L` from (73rnz_bs) gives

```text
O x=T x+1_L+D(t x)+t(1_L+x).                            (73rnz_cji)
```

Expanding `D=A^2+J+I` removes the remaining raw defect incidence.  The two
copies of `t x` cancel, leaving

```text
O x=T x+(1+t)1_L+A^2(t x)+<t,x>1.                       (73rnz_cjia)
```

The `A^2(t x)` term is a parity sum of unique common-neighbor witnesses
(off the zero diagonal), while the other terms are the already labeled
T-incidence, line-owner source, and one scalar bit.  This is the fully
incidence-resolved cut transport.

Its two large hyperedge terms admit genuine two-ended refinements.  Put
`s=A(t x)`.  Then

```text
A^2(t x)=A s
```

is the sum, over active witnesses `y in supp(s)`, of the q-point star
`N_A(y)`.  Since q is even, pair the q neighbors of each such y arbitrarily.
Every pair `{v,w}` produces the two-ended relay

```text
v--y--w,                                                 (73rnz_cjib)
```

and y is its unique common-neighbor label by C4-freeness.  Changing the
pairing is only the familiar even-star gauge.  Thus every common-neighbor
hyperedge in (73rnz_cjia) is a sum of private two-ended witness columns.

The T-word of those columns has only one gauge bit.  At an active witness y,
mark each incident star edge by `tau(v)=1[yv in T]`.  The number of marked
edges is `deg_T(y)`, which is even.  In any pairing, let `n_00,n_01,n_11`
count pairs with zero, one, or two marked edges.  Then

```text
n_01=0,
n_00+n_11=q/2=0                         (mod 2),
```

where the second equality uses `8 | q`.  Hence

```text
n_00=n_11                                      (mod 2). (73rnz_cjiba)
```

Thus mixed T-word relays always cancel in pairs, and the 00/11 classes carry
one common pairing-gauge bit.  The arbitrary even-star pairing cannot create
an independent odd switch charge.  This is exactly the fine-label reduction
needed to compare the witness columns with the route alphabet (73rnz_at).

In fact one can choose a canonical T-word-adapted pairing.  On
`N_A(y) setminus N_T(y)`, use the original partial Baer involution `iota_y`;
it pairs all non-T neighbors canonically.  The omitted set `N_T(y)` has even
size, so pair only those broken points arbitrarily.  The resulting relays
have

```text
word 00 on every canonical iota_y pair,
word 11 on every paired broken-T pair,                 (73rnz_cjibaa)
```

with no mixed word at all, occurrence by occurrence.  Thus the T-word gauge
can be eliminated completely: pairing freedom remains only inside the 11
fiber, where it cannot alter the route word.  Any genuine fine obstruction
must therefore use the endpoint owner labels of broken T-neighbors, not a
00/11 pairing artifact.

Only the 11 fiber retains an owner pairing state.  A non-T special leaf lies
in the canonical `iota_y` domain and has no pairing choice.  First suppose
`y notin {E_1,E_2}`.  Every neighbor of an outside full leaf lies in the
occupied shore, where the replication-two bound lets y have at most two
T-neighbors among the four star leaves.  It cannot have two sibling leaves:
then y and their empty center would have those two leaves as common
A-neighbors, violating C4-freeness.  Consequently the non-pole broken-T
pairing possibilities are

```text
0 T-leaf neighbors: no owner-marked 11 relay;
1 T-leaf neighbor:  one forced leaf--nonleaf 11 relay;
2 T-leaf neighbors: the leaves are cross-star, and either pair together
                    or launch two separate leaf--nonleaf 11 relays.       (73rnz_cjibb)
```

There is one separate pole-witness row.  Since `X intersect N_A(E_i)={p_i}`,

```text
s(E_i)=(A(t x))(E_i)=t(p_i).
```

Thus `E_i` is active exactly when `t(p_i)=1`.  Its broken-T set is precisely
its two sibling leaves by (73rnd), so those leaves form one forced sibling-11
relay through `E_i`.  This case has no pairing choice and contributes no new
gauge bit; it is the fixed sibling edge already used in the quotient Q.

For a non-pole witness, choose the broken-T pairing owner-adaptively:

```text
two cross-star T-leaves: pair the leaves together;
one T-leaf:              pair it with one nonleaf T-neighbor;
no T-leaf:               pair nonleaves arbitrarily.          (73rnz_cjibba)
```

The middle choice is always possible: the broken-T set is even, so after one
leaf its nonleaf population is odd and nonzero.  After the prescribed owner
pairs are removed, an even number of nonleaves remains.  Hence
(73rnz_cjibba), together with the forced pole row, eliminates the last owner
gauge at the level of the special-leaf/T-word alphabet: two leaves give one
cross-star 11 through-relay, one leaf gives one 11 exit, and zero leaves gives
none.  Remaining freedom pairs only non-special-leaf 11 endpoints.  It cannot
change the displayed leaf/T-word cell, but those endpoints may still carry
finer `F/E/M` or mate labels; compatibility with that refined capacity
alphabet remains part of the terminal.

Thus the special-leaf owner refinement has no remaining pairing ambiguity in
the chosen normal form.  The one-leaf state forces a unique odd owner exit,
while the two-leaf state realizes the cross-star through cell already
isolated by (73rnz_an)--(73rnz_ap).  With (73rnz_cjibaa) and
(73rnz_cjibba), every witness star has a fixed special-leaf/T-word profile,
independent of q; only the finer nonleaf subtype pairing remains.

For witnesses that actually carry a special-leaf owner, even that finer
subtype is fixed by the earlier switch classification.  With two cross-star
leaves, those two full-center incidences exhaust the replication-two cap, so
every remaining broken-T endpoint is ordinary; pair the leaves together and
then pair ordinary endpoints.  With one leaf, there is at most one additional
full-center T-neighbor G.  Its presence is exactly the switch bit `eta_y` of
(73rnz_af): choose

```text
eta_y=1: pair the leaf with the unique residual full center G;
eta_y=0: pair the leaf with one ordinary T-neighbor.       (73rnz_cjibbb)
```

In the second case an ordinary neighbor exists because (73rnz_af) gives an
odd nonempty ordinary exit bundle; in the first case the remaining ordinary
bundle is even.  Thus after the prescribed owner relay, all remaining broken
endpoints are ordinary and pair among themselves.  Every owner-bearing 11
relay now has a fixed endpoint subtype, T-word, and switch/exit label.  The
unresolved nonleaf subtype pairing occurs only in witness stars carrying no
special-leaf owner, so it cannot privately absorb a star demand.

The switch endpoint can also be propagated canonically through its residual
full center.  At a residual center G, let `j_G` be the number of switching
singleton ports and `r_G` the number of its remaining ordinary T-ports.
Equation (73rnz_ai) is exactly

```text
j_G=r_G                                               (mod 2).
```

If this common parity is odd, choose one switch port and one ordinary port
and pair them through G; after removing them, both populations are even and
pair internally.  If it is even, pair each population internally from the
start.  Therefore the normal form at G is

```text
j_G odd:  one leaf--switch--G--ordinary exit,
           plus leaf--leaf throughs and owner-free ordinary pairs;
j_G even: only leaf--leaf throughs and owner-free ordinary pairs.         (73rnz_cjibbc)
```

Thus an odd owner switch cannot terminate privately at a residual full
center: it launches a marked exit into M.  Together with the direct ordinary
exit in the `eta=0` case, every singleton leaf owner either reaches an
ordinary endpoint or is paired into a leaf--leaf through.  The remaining
capacity problem is consequently concentrated at the ordinary endpoints and
their `nu/mu` labels in (73rnz_aw), not at the exceptional owner centers.

The K-price of the canonical transition system is explicit.  On a 00 pair
from `iota_y`, the two endpoints are adjacent by definition of the Baer
involution, and K has no A-edges, so its price is zero.  On an 11 pair
`{v,w}` of broken T-neighbors, the endpoints cannot be adjacent: otherwise
`v,y,w` is a triangle and the edges `yv,yw` are not in T.  They already share
y, so C4-freeness makes y their unique common neighbor; hence `vw` is non-A
and non-D.  Equation (17) gives

```text
1[vw in K]=1+mu_(v,w).                                  (73rnz_cjibbf)
```

Therefore the total transition price at y in the canonical normal form is

```text
Theta_y=deg_T(y)/2
        + sum_(broken-T pairs {v,w} at y) mu_(v,w)       (mod 2). (73rnz_cjibbg)
```

This is independent of every 00 Baer pair and records exactly the secondary
half-degree bit plus the cross-matching prices of the 11 relays.  Every
owner-bearing through/switch/exit constructed above occupies a specified
summand of (73rnz_cjibbg); owner-free ordinary pairs occupy the remaining
summands.  Thus the sink-side capacity question has reduced to comparing the
marked owner summands with the single local bit `Theta_y`, the Baer analogue
of the SRP half-flip/interval bit.

These local transitions assemble into an Eulerian normal-form relay graph.
Let R have one edge `vw`, labeled by y, for every broken-T pair `{v,w}` at
witness y in any fixed completion of the normal form above.  Two different witnesses cannot create
the same relay edge, because then v,w would have two common A-neighbors.
Moreover every T-edge `vy` contributes exactly one occurrence of v to the
pairing at y.  Therefore

```text
deg_R(v)=deg_T(v)=0                                  (mod 2), (73rnz_cjibbh)
```

so R is Eulerian.  All of its edges are non-A/non-D and retain their unique
witness, owner, endpoint-subtype, and word-11 labels.  By
(73rnz_cjibbf)--(73rnz_cjibbg),

```text
|E(R) intersect E(K)|=sum_y Theta_y                  (mod 2). (73rnz_cjibbi)
```

Thus every normal-form fine capacity ledger has the same exact cut/cycle terminal
as the coarse D-chain: either `K restricted R` is a cut of each R-component,
or R contains an owner-labeled cycle with odd K-holonomy.  Unlike the earlier
coarse dichotomy, each R-edge is an actual owner/T-word relay and retains its
labels; the remaining owner-free completion choice does not erase them.  The
final task is now to exclude the cut potential on R or price one explicit odd
owner-labeled holonomy cycle.

Moreover the entire pairing gauge is generated locally.  Any two perfect
pairings of an even star are connected by four-endpoint switches

```text
{a--b,c--d}  <-->  {a--c,b--d}.                          (73rnz_cjibc)
```

Thus a proposed fine route price `w` is independent of the witness-star
pairing exactly when every realizable labeled quadruple satisfies

```text
w(a,b)+w(c,d)=w(a,c)+w(b,d).                             (73rnz_cjibd)
```

If (73rnz_cjibd) fails, the two sides give an explicit four-relay holonomy
localized at one unique witness y.  If it holds, every q-point star price is
well-defined independently of all pairing choices.  Because (73rnz_cjiba)
and (73rnz_cjibb) leave only bounded binary T-word/owner states, checking
gauge compatibility has reduced to a finite table of local quadrilateral
identities, uniform in q; no large-star enumeration remains.

There is also no hidden nonadditive invariant in the successful-table case.
The standard complete-graph cocycle calculation says that a symmetric
pair-weight satisfying every switch identity (73rnz_cjibd) has the form

```text
w(a,b)=phi(a)+phi(b)+c.                                  (73rnz_cjibe)
```

Indeed the four-cycle relations generate all differences of perfect
pairings; fixing two reference endpoints recovers `phi`, with one constant
class left over.  Summing (73rnz_cjibe) over a perfect pairing gives the sum
of the endpoint potentials plus `c q/2`.  The latter vanishes because `q/2`
is even, while the former depends only on the fixed star margins and is
exactly the additive-linear information already exhausted by
(73rnz_aj)--(73rnz_al).

Consequently a genuinely capacity-sensitive pair-local price that is required
to ignore the star pairing must fail a quadrilateral identity and create the
explicit four-relay holonomy of (73rnz_cjibd).  Pairing-independent prices are
additive and powerless.  The alternative is to use the canonical
`iota_y`/broken-T pairing (73rnz_cjibaa), in which case a nonadditive price may
depend on the fixed through/exit owner profile (73rnz_cjibba).  Thus the fine
terminal has exactly two honest forms: a localized four-relay holonomy for an
arbitrary pairing, or a canonical-Baer owner price on the fixed normal form.
No pairing-agnostic nonadditive third option exists.

Similarly, because T is Eulerian, `Tx` is exactly the boundary vector of the
T-cut `delta_T(X)`: outside X it counts T-neighbors in X, while inside X the
even T-degree converts internal incidence to external incidence.  Hence the
T term already consists of canonical two-ended T-edge columns.  After these
refinements, the only non-chain pieces in (73rnz_cjia) are the colored line
source and the global scalar column; the O-side remains the atomized
one-ended dart ledger (73rnz_cjj).

The colored line source compresses to at most two owner atoms.  On the line
`N_A(E_i)`, its support is the set of points with `t=0`.  Pair those points
arbitrarily; every pair gives a unique two-edge relay through `E_i`.  At most
one point remains, and its parity is

```text
q+sum_(v in N_A(E_i)) t(v)=(A t)_(E_i).                 (73rnz_cjic)
```

Thus the line term is a sum of two-ended pole-line columns plus one possible
leftover carrying the explicit owner label `E_i`, for each pole.  This is the
same owner-restricted cut price appearing in (73rnz_cjg).

Finally, the scalar column `1` has even mass because `|V|=q^2` is even.
Connectedness of D therefore realizes it as the boundary of a D-edge chain,
by the same incidence-image argument as (73rnz_cjc).  Consequently the entire
right side of (73rnz_cjia) is a sum of two-ended geometric chains plus at most
the two pole-owner leftovers (73rnz_cjic).  The sole remaining conversion is
to glue the atomized O-darts on the left to those chain endpoints without
discarding their `1+mu` labels.

That dart conversion has an exact boundary residue.  Let `delta_O(X)` be the
O-cut of X.  Outside X its edge-boundary is `Ox`; inside X the difference
between external and internal O-incidence is the O-degree.  Hence

```text
O x=partial_O(delta_O(X))+x deg_O.                       (73rnz_cjid)
```

Because `K=O disjoint-union K_D` is Eulerian, `deg_O=deg_(K_D)` modulo two.
For the D-cut `K_D=delta_D(t)`, its degree vector is `Dt+t` (D has odd degree
`q-1`).  Therefore

```text
O x=partial_O(delta_O(X))+x(Dt+t).                       (73rnz_cjie)
```

Every O-dart has now become its actual two-ended O-edge, retaining the
edge's `1+mu` label from (73rnz_cjj).  The remaining vertex residue is
supported on X and has total mass

```text
<x,Dt+t>=<Dx,t>+<x,t>=<1_L,t>.                           (73rnz_cjif)
```

This is exactly the combined parity of the two line-owner leftovers in
(73rnz_cjic).  Adjoin those leftover atoms to `x(Dt+t)`; the resulting
vector has even mass and is therefore another D-chain boundary.  Thus the
entire cut branch admits a coarse two-ended geometric decomposition that
preserves every O-edge matching label.  What is still unproved is the finer
capacity statement that these chain pairings can be chosen compatibly with
the owner/T-word cells (73rnz_at), rather than merely in the ambient D/O
graphs.

Every O-edge is a non-A, non-D pair.  It therefore has one unique
common-neighbor witness and, by (17),

```text
1[uv in O]=1+mu_(u,v).                                  (73rnz_cjj)
```

Thus both sides of the cut/cycle dichotomy are now incidence-resolved: the
cycle branch is the odd matching ledger (73rnz_cjh), while the cut branch is
the source equation (73rnz_cji) with each O-edge split into its unique
common-neighbor and cross-matching atoms.  What remains in either branch is
the same capacity problem -- preserve the owner/T-word label while pairing
these atoms -- rather than an unlocated graph edge.

The syndrome packing bound (73rnz_bm) removes one of those branches and
rigidifies the other.  Suppose first that both endpoints are leaves and that
`kappa_F` has no off-pole support.  Then (73rnz_ch) says `kappa_F=h`.  Since
`P_Fh=0`, the definition (73rnz_cg) becomes

```text
A(P_Fx)=h.
```

Every solution of this syndrome has support at least q by (73rnz_bm), while
`supp(P_Fx)` is contained in X and `|X|=q`.  Hence X would consist entirely
of full centers.  But this placement has only `q/2+2<q` full centers for
`q>=8`, a contradiction.  Therefore the both-leaf branch also forces
nonempty off-pole `kappa_F` support.

The same argument in the both-ordinary branch says that if `kappa_M` has no
off-pole support, then `A(P_Mx)=h`, so the packing equality forces

```text
X subset M, and in fact X=P_M X.                         (73rnz_ck)
```

Consequently every minimum two-pole support activates a nonprivate owner
commutator unless both endpoints are ordinary and every point of X is
ordinary.  The activation problem has collapsed to this single pure-ordinary
two-pencil residue.

That residue has a forced mate relay.  For an ordinary endpoint `p_i`, let

```text
a_i=iota_(E_i)(p_i).
```

Then `a_i` lies on the pole line and is adjacent to `p_i`; it is the outside
endpoint of the unique split Baer pair.  Since the pole line meets X only at
`p_i`, one has `a_i notin X`.  Also `a_i` is not a pole, while
`p_i in X intersect N_A(a_i)`.  The equation `Ax=h` therefore makes
`deg_A(a_i,X)` even.  In the equality packing, every non-pole line center
through `p_i` contains exactly two X-points, so there is a unique

```text
z_i in X setminus {p_i} with a_i z_i in A.               (73rnz_cl)
```

Thus the split pair cannot pay privately: it extends canonically to the
marked relay `p_i--a_i--z_i`.  The two mate centers are distinct, since a
common `a_1=a_2` would be a common A-neighbor of the D-adjacent empty poles,
whose codegree is zero.  Hence the pure-ordinary residue supplies two actual
owner-marked exits into X.  Combined with (73rnz_cj) and the both-leaf
packing argument, every endpoint decoration now activates either an
off-pole commutator unit or a canonical mate relay.

The parallel SRP separator now identifies the exact topology such a terminal
would need.  Its selected row--atom incidence graph is Eulerian; pairing at
degree-four atoms is a gauge choice, while the pairing-independent constant
class is the parity of the selected atom support.  Even support gives a local
circuit and odd support gives a global cover.  This is the same distinction
as the Baer quotient's pairing gauge and intrinsic bit `omega_Q`.

For the two-pole state, (73rnz_caa) already pairs every binary relay label
and identifies the two endpoint parities.  Thus the formerly proposed
relay-evenness problem is solved at the `mu` level; adjoining a formal
pole--pole edge would add no information there.  The parallel SRP topology
becomes relevant only after refining each endpoint parity into owner/mate
occurrences.  The remaining precise task is therefore

```text
couple the forced off-pole commutator units / ordinary mate relays to the
pairing-independent Omega/SRP gauge class.
                                                               (73rnz_cm GAP)
```

Equivalently, one needs a noncommuting marked operator whose endpoint value
is not forced by the universal A-edge complement.  Only after that activation
step is there a labeled trail whose gauge class can be compared with
`omega_Q` or the SRP constant class.

The charge-free hypothesis also has an exact pivot-pairing normal form.
Because every residual center G then has even J-degree, pair its incident
switch edges arbitrarily (degree zero, two, or four).  A paired pair
`(L,p,G)` and `(L',p',G)` supplies the T-path

```text
L-p-G-p'-L'.                                             (73rnz_bb)
```

Contract all such paths to edges of a labeled multigraph P on the four
leaves.  Every switch occurrence is used once, so

```text
deg_P(L)=deg_J(L)=b_L                              (mod 2). (73rnz_bc)
```

Thus the odd-degree set of P is exactly the forced charge vector b from
(73rnz_ak).  An edge of P joining sibling leaves closes with their two star
edges to give exactly the T 6-cycle (73rnz_ap).  An edge joining leaves of
different stars extends with the two star edges to a six-edge T-path from
`E_1` to `E_2`.  Hence every abstract charge-free switch realization is a
finite system of pivot-labeled same-star cycles and cross-star transports,
plus an even cycle space on four leaves.

This is the Baer dictionary for the pivot/relay skeleton of the B3 capacity
certificates: charged leaves are demand roots, a residual center G is the
pivot label pairing two or four demands, and the unused `rho` plus right-hand
`nu/mu` atoms in (73rnz_aw) are the relay ledger that must pay for that
pivot.  The pairing at a degree-four center is not canonical, so the normal
form is an existence statement; a proof must either choose weights invariant
under its three pairings or retain G as the uncontracted joint label.

The whole exceptional interface now closes on the four-leaf quotient.  Add
to P the two sibling edges, each representing the two-edge star path through
`E_i`, and add one cross-star edge for every occupied cell of N, representing
its two-edge path through the corresponding degree-two port.  Call the
resulting labeled multigraph Q.  At a leaf L its degree satisfies

```text
deg_Q(L) = deg_P(L)+1+m_L = b_L+1+m_L = 0        (mod 2). (73rnz_bd)
```

Thus Q is Eulerian and decomposes into closed trails.  Its three edge types
expand to actual T-paths of lengths four (paired switch), two (empty star),
and two (cross port), respectively.  Consequently every charge-free
exceptional routing is a closed labeled T-walk system generated on only four
leaf states.  A parallel P/sibling pair expands to the C6 in (73rnz_ap), and
a parallel P/cross-port pair is another six-edge closed route; longer quotient
cycles give the corresponding longer even T-walks.

This explains why no boundary parity survives: after all switches are paired,
the exceptional interface is already Eulerian.  The terminal information can
only be the joint labels/holonomy carried around these closed quotient trails
or a capacity price on their relay atoms.  It cannot be recovered from an
unlabelled exit count.

Modulo parallel-edge multiplicity, the topology is completely classified.
The reduction `bar Q` is a simple Eulerian graph on four vertices, hence an
element of the three-dimensional cycle space of `K_4`.  Its eight possible
values are

```text
empty;
one of the four triangles;
one of the three Hamilton four-cycles.                    (73rnz_be)
```

Indeed a nonempty even-degree simple graph on four vertices has every
nonisolated degree two, so it is a triangle or a four-cycle.  Even parallel
pairs disappear from `bar Q`; these include the labeled C6 blocks above and
cannot be discarded from the actual route ledger unless their two labels
cancel.  Thus the remaining holonomy audit has only seven nonzero quotient
skeletons, together with the joint labels on even parallel-pair corrections.

In particular every leaf-only potential is invisible on the closed quotient.
For any `chi:{four leaves}->F_2`,

```text
sum_(LL' in E(Q)) (chi(L)+chi(L'))
  = sum_L deg_Q(L) chi(L) = 0.                           (73rnz_bf)
```

Thus a weight depending only on the leaf, or only on its parent star, is a
coboundary with zero Q-holonomy.  Even the separator branch (73rnz_ay) becomes
load-bearing only if its values are cross-tagged with the pivot G, the route
cell, or the relay atom before contraction.  The required potential is
genuinely joint-label data, not a scalar coloring of the four quotient
vertices -- the exact finite analogue of the SRP transition commutator and
the failure of additive B3 census potentials.

Three joint edge characters are sufficient and necessary for the simple
shadow.  Fix any spanning tree R of `K_4` on the four leaves and let
`e_1,e_2,e_3` be its complementary chords.  For Q put

```text
q_j = multiplicity_Q(e_j)                         (mod 2). (73rnz_bg)
```

Because `bar Q` is Eulerian, its values on the three chords determine its
tree-edge values uniquely: the boundary equations solve successively along
the tree.  Therefore

```text
(q_1,q_2,q_3)=(0,0,0)  iff  bar Q is empty.             (73rnz_bh)
```

For a fixed choice of the degree-four pivot pairings, this is the minimal
linear holonomy target: the cycle space has dimension three, so no smaller
family of F2 characters separates all seven nonzero shadows.  The three
chord weights depend jointly on the unordered leaf pair and hence escape
(73rnz_bf).  They still ignore even parallel-pair corrections; those require
the pivot/route labels retained in the full ledger.

The degree-four pairing choice has an exact gauge.  The three pairings of
four incident leaves are the three perfect matchings of `K_4`; changing from
one to another changes P, hence Q, by the symmetric difference of two perfect
matchings, a Hamilton four-cycle.  The three Hamilton four-cycles span a
two-dimensional subspace H of the three-dimensional cycle space (their sum
is zero).  Therefore, if a degree-four pivot is present, the chord vector in
(73rnz_bg) is defined only modulo H.  Its sole pairing-invariant linear bit is

```text
omega_Q := |E(Q)|
         = |N| + |E(P)|
         = |N| + |E(J)|/2                         (mod 2), (73rnz_bi)
```

where the two sibling edges cancel modulo two and pairing J-edges gives
`|E(P)|=|E(J)|/2`.  Equivalently, `omega_Q` is `|N|` plus the parity of the
number of degree-two residual centers (a degree-four center contributes two
P-edges).  It distinguishes the triangle coset from the empty/four-cycle
coset: triangles have odd size, while the empty graph and Hamilton cycles
have even size.

Hence the canonical topology splits once more:

```text
no degree-four pivot:  the full three-bit chord holonomy is intrinsic;
degree-four pivot:     only omega_Q survives pairing gauge.     (73rnz_bj)
```

The lost two bits are not absent from the uncontracted geometry; they are
stored in the chosen pairing/mate decoration at G.  Any proof needing them
must retain that decoration, exactly as the SRP ledger retains its mate tag.

The surviving bit is exactly the switch Gram defect with a leaf correction.
For every even integer d,
`C(d,2)=d/2` modulo two.  Hence in the charge-free regime

```text
sum_G C(d_G,2) = |E(J)|/2                         (mod 2).
```

Combining this with (73rnz_ao) and (73rnz_bi) gives

```text
omega_Q
 = |N| + sum_L C(d_L,2) + Delta_J                (mod 2). (73rnz_bk)
```

The leaf binomial term counts pairs of distinct switches sharing their leaf;
the center binomial term already absorbed into `Delta_J` counts pairs sharing
their pivot.  Thus the sole pairing-invariant quotient holonomy is precisely
the reversal-odd row/column Gram defect corrected by the fixed cross-port
count and the leaf-side collision census.  This is the direct bridge from
the four-leaf quotient to the SRP commutator ledger: controlling `Delta_J`
jointly with the leaf collisions controls `omega_Q`.

The remaining `r=1` placement has a compact two-case normal form.  Put
`h=(q-2)/2=q/2-1` and retain `E_0` for the unique empty center.

- If `E_0 in S`, then `|R|=q/2-2` and `|F setminus S|=q/2+1`.
  The `h=a` routing gives `E_0` exactly two A-neighbors among those outside
  full centers.  Both edges lie in T by the complete F--E defect core.
  No other A-edge joins these exceptional types, so outside `A[R]` the graph
  `A[C]` is one two-edge T-star centered at `E_0`, plus isolated vertices.
- If `E_0 outside S`, then `|R|=q/2-1` and `|F setminus S|=q/2`.
  Routing (60) leaves `E_0` and every outside full center isolated in
  `A[C]`; hence its only nontrivial part is the path--cycle graph `A[R]`.

In both cases the defect graph on the exceptional support is exactly

```text
D[C] = K_(1,q-1),                                        (73ro)
```

with center `E_0`, because `D[F]` is empty and the F--E core is complete.
Thus the live `r=1` problem is no longer the earlier `F_0` boundary system:
it is a path--cycle partial-Baer core of order `q/2-2` or `q/2-1`, decorated
in the first placement by one forced two-edge T-star, and coupled through
the residual M block to the fixed exceptional D-star (73ro).

The `E_0 in S` case has two forced odd ordinary T-bundles.  Let `F_1,F_2`
be the two outside full centers adjacent to `E_0`.  Evaluating the companion
equation (70) at either `F_i` (where `x=-1`, `z=1`, and
`(Az)_(F_i)=-1`) gives

```text
N_D(F_i) is contained in S.                               (73rp)
```

Its full line also lies in S.  Since `F_i E_0 in T` and T is Eulerian,

```text
N_T(F_i) = {E_0} disjoint_union U_i,
U_i contained in M intersect S,
|U_i| is odd and nonzero.                                 (73rq)
```

Here every other exceptional center is excluded by the two-case routing
above.  Moreover `U_1` and `U_2` are disjoint: a common point would be a
second common A-neighbor of `F_1,F_2` in addition to `E_0`, contradicting
C4-freeness.  Thus the live inside-minority placement carries two disjoint
odd ordinary T-port bundles.  Unlike the killed `h=f` case, the exceptional
T-degree is two and these two odd remainders occur at distinct full centers;
the next transport must couple them rather than seek a one-vertex parity
contradiction.

The `E_0 outside S` case instead has a repeated-target endpoint structure.
If X is a degree-one vertex of a path component of `A[R]`, then X is a
majority private point by (73i), so (73r) gives it exactly one cross-shore
D-neighbor.  The complete exceptional D-star already supplies `E_0`, hence

```text
m(X)=E_0.                                                 (73rr)
```

This marked edge is non-A because the empty line at `E_0` has no neighbor
in S.  Consequently the two endpoints of every path component carry the
same actual non-A D-target `E_0`; path components canonically pair all such
endpoint marks.  This is the repeated-target state from the capacity
dictionary, rather than a family of independent K/Omega signs.  Any residue
in the outside-minority placement must therefore come from the cycle
components or from how the paired endpoint occurrences interact with the
residual M incidence, not from endpoint-mark parity alone.

The two odd bundles in the inside-minority placement are coupled by an
actual T-cycle.  The empty-line routing and the complete F--E core give

```text
N_T(E_0) = {F_1,F_2}.                                    (73rs)
```

Every edge of a finite Eulerian graph lies on a cycle.  Since these are the
only two T-edges at `E_0`, a simple T-cycle containing `E_0F_1` must leave
`E_0` through `E_0F_2`.  Removing `E_0` from that cycle gives a T-path

```text
F_1 -- u_1 -- ... -- u_2 -- F_2,
u_i in U_i,                                               (73rt)
```

The first and last internal vertices are ordinary by (73rq); later vertices
may revisit other exceptional centers through M, so no stronger cleanliness
is claimed.  Nevertheless the two disjoint odd bundles are not merely
parity-correlated: at least one port of each lies on the same T transport
path.  A terminal may now compare the residual owner/incidence data at the
two ends of this path, rather than trying to orient every element of `U_1`
and `U_2` separately.

Two exact consumers of the Gram identity make its extra content explicit.
Put `n=n_1=|P|` and recall that the column sum of R at `w in M` is
`p_w=r+deg_D(w,F)`.  Pairing (73p) with the all-ones vector gives

```text
sum_(w in M) p_w^2
  = n(n+q-2)-2e_D(P)-2e(Q_priv).                          (73s)
```

Thus the convex energy of the residual private-point loads is not free: it
is complementary to the induced D-energy on the private points.  In the
first two layers this reads

```text
r=1: sum (1+d_F(w))^2
       = 2(q-1)(3q-5)-2e_D(P),
r=2: sum (2+d_F(w))^2
       = (3q-4)(4q-6)-6q-2e_D(P).                         (73sa)
```

Likewise, since `R R^T` is PSD, every real vector x orthogonal to 1 obeys

```text
x^T (D[P]+Q_priv) x <= (q-2) ||x||^2.                    (73t)
```

Equations (73s)--(73t) are the spectral/convex feasibility test for the
otherwise locally realizable cores in (73l).  Any proposed path--cycle
embedding must now extend to a private-point defect graph and a column-load
sequence satisfying both the exact energy and the compressed eigenvalue
bound, in addition to the one/two cross-shore marks (73r).

The large pure branch is impossible.  By replacing `S` with its complement
it is enough to treat `E=empty`, so `d=c/2` and `s=(q^2+c)/2`.  Put
`t_P=|N_A(P) intersect F|`.  The pointwise companion equation (70), evaluated
on the two shores, gives

```text
deg_D(P,V setminus S) = (q t_P-c)/2       for P in S,
deg_D(P,S) = c/2                          for P outside S.  (74)
```

In particular `q t_P>=c`.  If `q<c<=2q-2`, the subcubic bound (59) therefore
forces `t_P in {2,3}` at every point of `S`.  Let `n_2,n_3` count these two
replication classes.  Incidence balance and the shore size give

```text
n_2+n_3=s,             2n_2+3n_3=qc.
```

The pair identity (68), merely using `e_D(F)>=0`, gives

```text
2n_2+6n_3 <= c(c-1).                                  (75)
```

Eliminating `s,n_2,n_3` from these relations yields
`4qc<=3q^2+c^2+2c`.  But incidence nonnegativity first forces `c>=q+2`, and
the reverse strict inequality holds throughout `q+2<=c<=2q-2` for `q>=8`.
This arithmetic contradiction is Lean-checked by
`binarySquare_pureLargeExceptional_impossible`.  Hence every surviving pure
exceptional design satisfies

```text
c <= q.                                                   (76)
```

There is also a lower squeeze in the pure branch.  Since `c>0`, the first
formula in (74) forces `t_P>=1` at every `P in S`.  Hence incidence balance
gives `s<=qc`; substituting `2s=q^2+c` yields

```text
q < 2c,       so q/2 < c <= q in the surviving pure branch. (77)
```

This last arithmetic implication is Lean-checked by
`binarySquare_pureExceptional_halfDegree_lt_card`.

The surviving interval has an exact internal-defect identity.  Let
`n_i=|{P in S:t_P=i}|` for `i=1,2,3`, and write `e=e_D(F)`.  The cover,
incidence, and pair equations are

```text
n_1+n_2+n_3=s,
n_1+2n_2+3n_3=qc,
n_2+3n_3=C(c,2)-e.
```

Eliminating the replication counts and using `2s=q^2+c` gives

```text
2(e_D(F)+n_3)=(q-c)^2.                                  (78)
```

This is Lean-checked by
`binarySquare_pureExceptional_defect_triple_identity`.  In particular the
endpoint `c=q` forces both `e_D(F)=0` and `n_3=0`: every two full lines meet,
no three meet, and their union consists of one point for each line-pair plus
exactly one private point on each line.  More generally (78) quantifies the
total failure of that endpoint design by the square distance from `c=q`.

The unresolved signed-support terminal has therefore split into two strictly
smaller regimes: mixed support `c<=q`, with the unbalanced case in the exact
`(r,u)` normal form (73d)--(73h), or pure support `q/2<c<=q`.  The latter
still obeys (74), so every point of its occupied shore has positive
exceptional replication.  Eliminating the pure partial-linear-space regime
and the routed mixed low-r designs remains necessary.

Equations (7)--(78) are the first canonical cut detector manufactured from
the partial Baer involutions and its first exact transport into `D`.  They
also state exactly what is still missing.  The graph K is the nonadjacent
part of `Omega triangle D`, is Eulerian, and transports T-incidence on S by
(19)--(20).  Any k-dependent terminal can now aim at locating K inside the
non-A pairs, rather than trying to couple the local involutions directly.
The q=4 fixed-free control is compatible with (7)--(78), so these laws alone
do not conceal an order-independent
contradiction.

## Disposition

The involution-coupling audit does not yet yield a contradiction beneath
`A-REG-NONBIP`.  Its durable result is the narrowed target:

> Control the canonical nonadjacent Eulerian transport
> `K=Omega triangle (D setminus T)` on the binary kernel shore; it reproduces
> the broken Baer-pair/T incidence vertexwise, while degree parity and scalar
> connectivity are already exhausted.

Equivalently, prove that binary fixed-point-free incidence forces the
missing-pair graph D to split into its affine parallel-class cliques.  Any
successful proof must manufacture this partition without assuming the line
intersections whose absence D records.
