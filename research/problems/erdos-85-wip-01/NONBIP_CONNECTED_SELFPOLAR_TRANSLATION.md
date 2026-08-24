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

### Extension to a projective plane

Partial-plane extension results, including Stephen Dow's
[An improved bound for extending partial projective
planes](https://doi.org/10.1016/0012-365X(83)90036-5), assume considerably more
structure than is available here.  Completing our configuration in the
classical way would produce parallel classes and force `D = q K_q`, directly
contradicting the connected branch.  Thus a theorem of the form “connected
implies completion” would be unexpectedly strong; I found no such theorem.

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
is refuted pointwise by the established even triangle-free-degree law.  Within
the configuration literature, the most precise surviving bounded structural
question is whether our already-proved codegree identities imply either
semipartial uniformity axiom.  Completion is useful mainly as a warning: the
standard realizations exist, but their deficiency graph is maximally
disconnected.
