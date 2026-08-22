# A-REG Baer involution coupling audit

Status: q-generic negative audit under `A-REG-NONBIP`, 22 August 2026.

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

## Disposition

The involution-coupling audit does not yield a new theorem beneath
`A-REG-NONBIP`.  Its durable result is the narrowed target:

> Couple the partial Baer involution orbits to the locations of `T` inside a
> connected `D`; degree parity and scalar connectivity are already exhausted.

Equivalently, prove that binary fixed-point-free incidence forces the
missing-pair graph D to split into its affine parallel-class cliques.  Any
successful proof must manufacture this partition without assuming the line
intersections whose absence D records.
