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
