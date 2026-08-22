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

## Commuting-hole classification

The remaining component-side classification is nevertheless uniform.  The
following elementary centralizer lemma is the useful formulation.

> **Cycle centralizer with edge avoidance.**  Let `W` be a symmetric real
> matrix commuting with the adjacency matrix of `C_N`.  If `W` vanishes on
> every cycle edge, and vanishes whenever its two indices have the same
> parity, then `W` is circulant.

Here is a proof that also records why no connectedness assumption on `W` is
needed.  In the Fourier basis of `C_N`, the eigenvalue at frequency `a` is
`2 cos(2 pi a/N)`.  Two such eigenvalues agree exactly when their frequencies
are equal up to sign.  Consequently every matrix in the cycle centralizer has
the form

```text
W_(x,y) = c_(y-x) + r_(x+y),
```

with a circulant part `c` and a reverse-circulant part `r` (the harmless
overlap at frequencies `0` and `N/2` can be assigned to either part).  The
cycle-edge zeros give

```text
0 = W_(x,x+1) = c_1 + r_(2x+1),
```

so `r` is constant on the odd residues.  The same-parity zeros similarly give
`0=c_d+r_s` for every even difference `d` and even sum `s`, so both terms are
constant on the even residues.  Thus on the only possibly nonzero positions,
those of odd difference, `r_(x+y)` is a single constant and can be absorbed
into `c_(y-x)`.  Hence `W` is circulant.

Apply the lemma to the hole adjacency matrix `P` on `C_(2q-6)`.  Symmetry,
degree two, and bipartiteness now force a single odd step pair

```text
P = Cay(Z/(2q-6), {+t,-t}),
```

where `t` is odd; avoidance of the long-cycle edges says `t` is not congruent
to `+1` or `-1`.  In alternating-sign grid coordinates of size `q-3`, this is
exactly the rotation-circulant row support

```text
Q(i) = {i+s, i-1-s}.
```

Therefore the apparent odd-grid classification gap is closed: every survivor
is parametrized by one cyclic step, not an arbitrary commuting two-factor.
This does **not** itself exclude the survivor.  The q=16 step-3 witness is one
member of the classified family, and the unresolved obstruction remains the
integral exterior placement (in particular the disjoint-trace codegree laws,
which were absent from the feasible fractional control).

## Why the linear exterior spectrum forgets the step

There is a sharp limit on the next consumer.  Let `M` be the incidence matrix
of the trace graph `F`, and let `K` be any exterior completion.  The trace
graph in the surviving orientation is connected, bipartite, and
`(q-2)`-regular, with alternating sign vector `s`.  Hence

```text
M M^T = (q-2) I + F
```

is positive semidefinite with kernel exactly `span{s}`.  The cross-block
square equation and its transpose are

```text
H M + M K = J,             M^T H + K M^T = J.
```

If `x` is orthogonal to `1` and `s`, the second equation gives

```text
K (M^T x) = -M^T(Hx),
```

and `M^T x` is nonzero.  Thus `M^T` injectively intertwines `-H` with `K`
on the `(2q-2)`-dimensional space `{1,s}^perp`.  In particular every
nonprincipal internal-cycle eigenmode other than the alternating kernel is
inherited by the exterior adjacency with its eigenvalue negated.

Crucially, this inherited operator is the restriction of `-H`; it is
independent of the cyclic hole step `t`.  The step changes the Gram form
`M M^T`, hence the embedding of this subspace, but not its exterior
eigenvalues or any trace-moment contribution obtained merely by summing those
eigenvalues.  Therefore characteristic-polynomial divisibility and scalar
spectral-moment routes cannot distinguish the classified steps.  A terminal
must use the entrywise `0/1` placement of `M^T x` or the nonlinear exterior
codegree constraints; simply transferring the cycle spectrum cannot select
or exclude `t`.

## Why every individual exterior row passes Hall

The first entrywise necessary condition also holds automatically.  For an
outside trace `r={u,v}`, the equation `HM+MK=J` says that the `K`-neighbors
of `r`, viewed as edges of the trace graph `F`, must form a perfect matching
on

```text
C minus (N_H(u) union N_H(v)).
```

Every trace joins opposite sides of the alternating bipartition.  The two
neighbors of `u` in `H` lie on one shore and the two neighbors of `v` lie on
the other.  After deleting them, the eligible graph is therefore balanced
with `m=q-2` vertices on each shore.  The original trace graph `F` is
`(q-2)`-regular, and deletion removes at most two neighbors of any retained
vertex, so the eligible graph has minimum degree at least

```text
q-4 = m-2 >= m/2                 (q >= 8).
```

A balanced bipartite graph with minimum degree at least `m/2` has a perfect
matching: for a shore subset of size at most `m/2`, minimum degree proves
Hall directly; for a larger subset, any vertex outside its neighborhood
would have all its at least `m/2` neighbors in a complement of size less than
`m/2`.  Hence Hall holds for every trace, uniformly in the cyclic step.

The reproducible checker `six_long_local_matching_audit.py` confirms this
for every admissible step at `q=8,16`, and through step 27 at `q=32`, but the
argument above is general and does not rely on the audit.  Thus neither a
single-row exact-cover obstruction nor local Hall deficiency can eliminate
the survivor.  The remaining problem is genuinely simultaneous: choose the
row matchings mutually so that exterior adjacency is symmetric and all
disjoint-trace codegrees are at most one.

## The shared-trace reciprocity layer always closes

There is also no obstruction in making all endpoint resolvers reciprocal.
Delete from `F` the long-cycle edges, which are precisely the edge-traces,
and call the resulting graph `F_0`.  Its edges are exactly the non-edge
traces.  At a short-cycle point its degree is `q-2`; at a long-cycle point
its degree is `q-4`.  Both are even.  Moreover `F_0` is connected: the two
complete short-to-long parity blocks are joined by the opposite matching on
the short `C6` (and all their vertices occur in those blocks).

Choose one Euler circuit of `F_0`.  At every component point, pair each
entering trace-edge with the trace-edge by which the circuit leaves.  Regard
each edge of `F_0` as its corresponding outside trace vertex and join paired
trace vertices in the exterior graph.  The result has the exact resolver
properties:

* every non-edge trace has one resolver through each endpoint, hence resolver
  degree two;
* every edge-trace has resolver degree zero;
* reciprocity is automatic because the local pairings are undirected;
* the resolver graph is one cycle on
  `q(q-2)-(2q-6)=q^2-4q+6` vertices.

The last number is greater than four for `q>=8`, so this resolver layer is
itself C4-free.  Simplicity is automatic because two distinct simple trace
edges cannot share both component endpoints.  Therefore even the simultaneous
shared-trace part of the exterior adjacency has a uniform integral
completion.  Any terminal must couple these resolver choices to the remaining
`q-4` or `q-2` disjoint-trace neighbors and their codegree-at-most-one laws;
resolver parity or reciprocity alone cannot exclude the survivor.
