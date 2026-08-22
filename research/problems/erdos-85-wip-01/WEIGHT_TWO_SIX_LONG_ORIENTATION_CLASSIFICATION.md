# Weight-two C6 plus long-cycle orientation classification

## Statement

Let `q=2^k` with `k>=3`.  Suppose a weight-two alternating-eigenline defect
component has exactly two internal ambient cycles,

```text
H = C6 disjoint-union C_(2q-6),
```

and suppose one cycle is T-saturated while the other is cross-saturated.
Then the orientation and the internal outside-trace degrees are forced:

* C6 is T-saturated;
* the trace graph on C6 is exactly its opposite perfect matching, of degree 1;
* the long cycle is cross-saturated;
* the trace graph induced on the long cycle has degree `q-5`.

In particular the reversed mixed orientation is impossible uniformly in q.

## Proof

Let `F` be the graph of outside two-point traces.  It is `(q-2)`-regular,
every F-edge joins opposite alternating signs, and `[H,F]=0`.  Write `r` and
`s` for the internal F-degrees on C6 and the long cycle.  Commutation with
each connected cycle makes these degrees constant: applying the block
commutator to the all-ones vector puts each degree vector in the simple
eigenvalue-2 eigenspace of its cycle.

Cross-edge balance is therefore

```text
6(q-2-r) = (2q-6)(q-2-s).                  (1)
```

Inside an alternating C6, the only opposite-sign pairs are its six cycle
edges and its three opposite pairs.

If C6 were cross-saturated, its cycle edges would all lie in F, so `r=2` or
`r=3`.  For `r=2`, equation (1) would require

```text
q-2-s = 3(q-4)/(q-3) = 3 - 3/(q-3),
```

so `q-3` divides 3.  For `r=3`, it would require

```text
q-2-s = 3(q-5)/(q-3) = 3 - 6/(q-3),
```

so `q-3` divides 6.  Neither is possible for a power of two `q>=8`.

Hence C6 is T-saturated and its six cycle edges are absent from F.  Its only
possible internal F-edges are the opposite matching, so `r=0` or `r=1`.
If `r=0`, equation (1) gives

```text
q-2-s = 3(q-2)/(q-3) = 3 + 3/(q-3),
```

again impossible because `q-3` does not divide 3.  Thus `r=1`.  Substituting
in (1) and cancelling `2(q-3)` gives

```text
q-2-s = 3,
```

so `s=q-5`.  Since the orientation is mixed, the long cycle is the
cross-saturated one.

## Scope and use

This is q-generic structural progress beneath SIZE-TWO-EIGENLINE, not an
order-64 endpoint.  At q=8 it recovers the forced orientation/degrees in the
6+10 shape; at q=16 it explains uniquely the C6-T/C26-cross reduced witness.

The same quotient method applies to arbitrary two-cycle lengths `ell` and
`2q-ell`:

```text
ell(q-2-r_1) = (2q-ell)(q-2-r_2).
```

For cycles of length at least eight the admissible degree intervals often
contain the universal solution `r_i=length_i/2-2`, so the quotient law alone
does not force synchronization.  The C6 case is special because its
opposite-sign chord space consists of only one matching.  Excluding the
surviving orientation still requires the full integral exterior placement or
an additional reciprocal constraint.

## Forced hole reduction in the surviving orientation

The surviving degrees determine the cross trace block completely.  Every
C6 vertex has `q-3` cross-trace neighbors, and every long-cycle vertex has
three.  Alternating signs leave exactly `q-3` eligible long vertices for each
C6 vertex and exactly three eligible C6 vertices for each long vertex.
Therefore the cross block is forced to be

```text
K_(3,q-3) disjoint-union K_(3,q-3),
```

one complete bipartite graph for each opposite-sign pairing.

On the long cycle, reorder vertices by alternating sign.  The complete
opposite-sign graph is `B=K_(q-3,q-3)`.  The internal trace graph `Z` has
degree `q-5`, so its complement `P=B-Z` has degree two.  Moreover:

* `P` is bipartite and 2-regular;
* `P` avoids every long-cycle edge because that cycle is cross-saturated and
  hence contained in `Z`;
* `P` commutes with the long-cycle adjacency.  Both `Z` and the long cycle
  commute by the block K-law, while `B` commutes with every 2-regular
  bipartite graph on these equal sign classes; hence `P=B-Z` commutes too.

Thus the entire surviving component-side problem reduces to a commuting
2-factor `P` of holes on the long cycle, plus the exterior realization.  In
the q=16 control, `P` is the step-3 C26.  This is the disconnected-sector
analogue of the banked reflection-circulant hole classification for a single
connected internal cycle; that theorem does not apply directly because the
ambient internal graph here has two components.  Classifying these commuting
long-cycle hole 2-factors is the next algebraic consumer before the full
exterior exact cover.
