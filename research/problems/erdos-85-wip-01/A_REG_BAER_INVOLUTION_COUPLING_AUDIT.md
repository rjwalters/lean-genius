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

Equations (7)--(30) are the first canonical cut detector manufactured from
the partial Baer involutions and its first exact transport into `D`.  They
also state exactly what is still missing.  The graph K is the nonadjacent
part of `Omega triangle D`, is Eulerian, and transports T-incidence on S by
(19)--(20).  Any k-dependent terminal can now aim at locating K inside the
non-A pairs, rather than trying to couple the local involutions directly.
The q=4 fixed-free control is compatible with (7)--(30), so these laws alone
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
