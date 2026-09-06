# NONBIP-CONNECTED: self-polar configuration translation

## Exact obstruction dictionary

The hypothetical symmetric zero-diagonal `q`-regular `C4`-free adjacency
matrix `A` on `q^2` vertices is also the incidence matrix of a self-polar,
absolute-point-free symmetric configuration `(q^2)_q`.  Its deficiency graph
`D` joins noncollinear point pairs and is `(q - 1)`-regular.  Thus the present
NONBIP-CONNECTED branch asks whether such a configuration can have connected
deficiency graph, subject to the additional identities already proved in this
development.

This translation is important because symmetric configurations with these
parameters exist for prime-power `q`: delete an incident point/line pencil from
a projective plane of order `q`.  In that classical construction the remaining
points split into `q` groups of size `q`, and two points are noncollinear exactly
when they lie in the same group.  Hence

```text
D = q K_q.
```

Parameter-only nonexistence arguments therefore cannot work.  Connectedness
isolates an exotic, non-projective-derived case.

## What the external literature supplies

### Symmetric configurations

Davydov, Faina, Giulietti, Marcugini, and Pambianco survey many constructions
of symmetric configurations and deficient difference sets in
[On constructions and parameters of symmetric configurations
v_k](https://arxiv.org/abs/1203.0709).  Their results reinforce the point above:
the parameters `(q^2)_q` alone are not contradictory.  I found no theorem there
that rules out a connected deficiency graph, nor a theorem saying that such a
configuration must extend to a projective plane.

### Polarities of symmetric semipartial geometries

Debroey and Thas develop spectral formulas and absolute-point bounds for
[polarities of symmetric semipartial
geometries](https://www.bdim.eu/item?fmt=pdf&id=RLINA_1977_8_62_5_606_0).
Those theorems are potentially terminal, but their hypotheses are substantially
stronger than ours: they require uniform numbers of common collinear points for
noncollinear pairs and a `0`-or-`t` intersection law for nonincident point-line
pairs.  Connectedness of `D` does not presently imply either condition.

Consequently, promotion of our configuration to a semipartial geometry is a
real missing structural lemma, not a change of vocabulary.  If such promotion
were obtained, the classical polarity machinery would become relevant.

#### Exact matrix form of the missing semipartial axioms

Let `C` be the collinearity graph on points.  The square-order defect identity
gives

```text
A² = qI + C,                 C = J - I - D.
```

Since `D` is `(q - 1)`-regular on `q²` vertices, direct expansion gives

```text
C² = q(q - 2)J + I + 2D + D².
```

For a noncollinear pair `x,y` (that is, a `D`-edge), the number of points
collinear with both is therefore

```text
(C²)_{xy} = q(q - 2) + 2 + (D²)_{xy}.
```

Thus the first semipartial uniformity axiom is exactly constancy of the defect
codegree `(D²)_{xy}` over all `D`-edges.  Connectedness and regularity alone do
not imply this; the existing development controls sums and moments of these
entries, but contains no edgewise-constancy theorem.

For the second axiom, take a point `x` and a line indexed by `y`.  The number
of points on that line collinear with `x` is

```text
(CA)_{xy} = (A³ - qA)_{xy}.
```

When `x` is not incident with the line (`A_{xy}=0`), this is simply
`(A³)_{xy}`.  Hence the required `0`-or-`t` law is precisely the existence of a
single integer `t` such that

```text
A_{xy}=0  implies  (A³)_{xy} in {0,t}.
```

The banked cubic bounds, histograms, and binary transport equations do not
establish this two-valued conclusion: in particular the transport results see
parity or aggregate mass, not equality of all positive cubic entries.  These
two formulas isolate the exact promotion gap and make it independently
checkable.  Any future semipartial route must prove at least one genuinely new
entrywise uniformity statement rather than another moment identity.

#### Corrected terminal audit: promotion suffices at square order

Correction, 2026-09-06: the previous version correctly noted that the
Debroey--Thas absolute-point bound assumes a nonzero absolute-point count,
but incorrectly concluded that semipartial promotion is insufficient here.
The special square-order parameters provide a different terminal.

A semipartial geometry has a strongly regular collinearity graph; see
[Abreu, Funk, Krčadinac, and Labbate, *Strongly regular configurations*,
Section 3](https://arxiv.org/html/2104.04880v2). Here is the direct count.
Write `alpha` for the positive value in the nonincident point-line law.
For two collinear points x,y, their common line contributes `q-2` common
collinear points. Each of the other `q-1` lines through x contributes
`alpha-1`: y is not on that line and is collinear with x on it, so the
intersection count is positive and hence alpha. These contributions are
disjoint by partial linearity. Thus adjacent pairs in C have the constant
codegree `q-2+(q-1)(alpha-1)`. The other semipartial axiom gives constant
codegree for nonadjacent pairs. Consequently C, and its complement D, are
strongly regular (allowing the imprimitive cases).

A connected strongly regular D on q² vertices of degree q-1 would have
diameter at most two. Its radius-two count would imply

```text
q² <= 1+(q-1)+(q-1)(q-2) = q²-2q+2,
```

which is impossible for q>1. If D is disconnected, its nonadjacent
codegree is zero because vertices in different components have no common
neighbor. Every component must then be a clique: a shortest path between
nonadjacent vertices in a component would contain a distance-two pair.
Regularity forces `D=q K_q`. This is already excluded for binary q>=8 by
`binarySquare_regular_not_allUnit_of_two_pow` in
`Erdos85BinarySquareRegularParity.lean`.

In fact the second promotion axiom alone suffices. Since
`A³=qJ-A-AD` and every column of D has q-1 ones, for `A[x,y]=0` we have
`A³[x,y]=q-(AD)[x,y]>=1`. Thus its proposed `0`-or-alpha law has no zero
case: every nonincident point-line pair has exactly alpha collinear points.
Fix a point x. There are q(q-1) points collinear with x, each incident with
q-1 lines not through x. There are q(q-1) lines not through x, so counting
these incidences gives `alpha=q-1`.

For even q this is already a contradiction: x is not incident with its
own indexed line because A has zero diagonal, while `A³[x,x]=2t_x` is
even, being twice the number of triangles through x. The law would make
it equal to the odd number q-1. Thus the nonincident cubic uniformity
premise is impossible for every even q, without a binary-power or
connected-defect assumption. This shorter parity terminal was independently
identified during squad review.

If x,y are noncollinear, each of the q lines through y then contains q-1
points collinear with x. The lines meet only at y, which is not collinear
with x, so x,y have q(q-1) common neighbors in C: their C-neighborhoods
are equal. Hence noncollinearity, with equality added, is an equivalence
relation. Its classes have size q because D has degree q-1, giving
`D=q K_q` directly. This supplies a terminal from the nonincident cubic
uniformity premise alone; the separate defect-edge codegree premise is
not needed.

No such cubic uniformity is presently proved. This correction restores
the conditional implication, not a proof of promotion or any change in
A-REG status. Generic fixed-point-free semipartial examples at other
orders do not refute this square-order argument. No new Lean theorem is
claimed.

### Extension to a projective plane

Partial-plane extension results, including Stephen Dow's
[An improved bound for extending partial projective
planes](https://doi.org/10.1016/0012-365X(83)90036-5), assume considerably more
structure than is available here.  Completing our configuration in the
classical way would produce parallel classes and force `D = q K_q`, directly
contradicting the connected branch.  Thus a theorem of the form “connected
implies completion” would be unexpectedly strong; I found no such theorem.

### Levi graph as a girth-six graph of excess `2(q - 1)`

The bipartite Levi graph has adjacency matrix

```text
[ 0  A ]
[ A  0 ],
```

so it is `q`-regular, has `2q²` vertices, and has girth at least six.  The
girth-six Moore bound at degree `q` is `2(q² - q + 1)`, making its cage-theory
excess exactly `2(q - 1)`.  From a point root, the `q - 1` same-side vertices
not reached within distance two are precisely its neighbors in `D`; the same
holds on the line side because `A` is symmetric.  Therefore the standard
near-Moore excess graph is

```text
D disjoint-union D,
```

and the polarity exchanges the two copies.

This makes the cage literature conceptually relevant but not directly
terminal.  Results such as Filipovski--Ramos Rivera--Jajcay's
[On biregular bipartite graphs of small
excess](https://doi.org/10.1016/j.disc.2019.04.004) treat excess at most four;
other standard even-girth excess theorems assume excess at most `q - 2`.
Our excess `2q - 2` lies outside both regimes.  Moreover, projective-plane
constructions give `q`-regular bipartite girth-six graphs on
`2(q² - 1)` vertices, fewer than ours, so an order or cage bound cannot rule
out the Levi graph.

The near-Moore translation is nevertheless diagnostic: its excess operator is
not a new invariant but exactly the already-studied `D`.  A transferable cage
argument would have to exploit the part-swapping fixed-free polarity, rather
than only regularity, girth, order, or the excess graph spectrum.

### Moore defect one

The cleanest classical terminal found is the nonexistence of diameter-two
regular graphs of defect one (apart from the cycle case); see Delorme and
Pineda-Villavicencio,
[On graphs of defect at most 2](https://arxiv.org/abs/1010.5658), which records
the Erdős--Fajtlowicz--Hoffman defect-one result.

Our ambient graph has degree `q` and `q^2` vertices, one below the diameter-two
Moore bound `q^2 + 1`.  Therefore, for `q >= 3`, it would be impossible if it
had diameter two.  The exact missing bridge is

```text
every pair with no common neighbor is adjacent,
equivalently D is a subgraph of the ambient graph.
```

This is much stronger than connectedness of `D`, but it is precise and admits a
bounded audit against the existing owner, parity, and triangle identities.

#### Bounded audit: the bridge is impossible at even `q`

The repository already contains both ingredients of a decisive local audit:
`binarySquare_regular_triangleFree_degree_even` and
`binarySquare_regular_defect_degree`.  An ambient edge is an edge of `D`
exactly when it is triangle-free.  Hence, at even `q`, the number of incident
edges in `G ∩ D` is even at every vertex, whereas the degree in `D` itself is
`q - 1`, which is odd.  It follows pointwise that

```text
for every vertex x, some D-neighbor of x is not adjacent to x in G.
```

In particular `D <= G` is not merely unproved: it contradicts the established
local parity law.  The Moore defect-one theorem therefore cannot close this
branch through the diameter-two bridge.  This falsifies that bounded probe and
prevents further work on it.

## Verdict

No ready-made theorem found in the searched configuration, polarity, or
partial-plane literature rules out connected `D`.  The Moore defect-one route
is a useful neighboring terminal, but its necessary graph inclusion `D <= G`
is refuted pointwise by the established even triangle-free-degree law.
Semipartial promotion would be terminal at these square-order parameters by
the argument above; indeed the nonincident cubic uniformity premise alone
suffices, but remains unproved. The generic absolute-point bound alone is inapplicable. Completion
is useful mainly as a warning: the standard realizations exist, but their deficiency
graph is maximally disconnected.  A viable configuration-theoretic endgame
must therefore use the special `(q²)_q` parameters and self-polar labeling more
strongly than either generic completion or generic semipartial theory does.
