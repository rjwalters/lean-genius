# NONBIP-CONNECTED: packing and code translation

Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.

Status: goal #36 literature verdict and bounded-probe cut, 24 August 2026.
This note does not close the node.

## Exact dictionary

Let `A` be a hypothetical symmetric, loopless, binary `q`-regular matrix on
`q^2` coordinates with no repeated row intersections.  Regard the support of
row `x` as a block `B_x`.  Then

```text
|B_x| = q,
|B_x intersect B_y| in {0,1} for x != y,
each coordinate lies in q blocks.
```

Thus the rows have three equivalent interpretations.

1. They are `q^2` binary constant-weight-`q` words of length `q^2`, with
   Hamming distance `2q` or `2q-2`.
2. They are a regular `2-(q^2,q,1)` packing with `q^2` blocks.
3. Their block cliques give an edge-disjoint `K_q`-decomposition of
   `K_(q^2) \ D`, where the leave `D` joins exactly the disjoint block pairs.

For each block there are exactly `q(q-1)` other blocks meeting it once and
exactly `q-1` disjoint blocks.  Hence the constant-weight distance
distribution is forced:

```text
A_(2q-2) = q(q-1),      A_(2q) = q-1.                 (P1)
```

The missing ingredient in any generic packing or code translation is the
polarity: the block labels are the same set as the coordinates, `A` is
symmetric, and looplessness says `x notin B_x`.

## What the code-rank literature does and does not give

Xiang's survey, *Recent results on p-ranks and Smith normal forms of some
2-(v,k,lambda) designs* ([arXiv:math/0407425](https://arxiv.org/abs/math/0407425)),
records the Hamada--Klemm rank and Smith-normal-form machinery.  Its general
strong bounds use the design Gram identity with **constant concurrence**
`lambda`.  For example, the quoted Klemm bound applies to a genuine
`2-(v,k,lambda)` design whose incidence Gram has one off-diagonal value.

Here the concurrence is the adjacency indicator of `complement(D)`, so it
has both values zero and one.  Applying the design theorems would first
require filling the leave by new blocks so that every pair occurs once.
That completion is precisely the missing parallel-class theorem; the rank
literature does not supply it for free.  In particular, citing a symmetric
design p-rank bound directly for `A` would assume the hard step.

The exact binary code still has a useful Gram description,

```text
A A^T = A^2 = q I + adj(complement D)       over the integers,
A A^T = adj(complement D)                   over F_2.       (P2)
```

but generic hull/nullity statements applied to (P2) see only the modular
rank of the leave complement.  They do not turn connectedness of `D` into
the rational singularity of `A`; the existing mod-2/SNF audit explains the
same direction mismatch.

## Why packing regularity cannot be the missing theorem

Packing-leave theory treats nontrivial regular leaves as objects to
construct, not as automatic contradictions.  As a representative primary
source, Horsley and Pike, *Leaves for packings with block size four*
([arXiv:1905.12151](https://arxiv.org/abs/1905.12151)), construct maximum
packings with broad families of prescribed 2-regular leaves.  Their block
size is fixed at four, so this is not a counterexample at our parameters.
It is a scope warning: regularity or connectedness of a leave alone is not a
standard completion hypothesis.

Our additional self-polar labeling must therefore enter any successful
completion argument.  This agrees with the exact `q=4` fixed-free control,
which already satisfies the packing laws while its leave has two non-affine
components.

## A rigorous Delsarte/Johnson-scheme no-go

The inner distribution of the constant-weight code is completely determined
by (P1).  The classical affine-plane-minus-one-parallel-class control has
the same distribution: its leave is `q K_q`, so every word again has `q-1`
disjoint mates and `q(q-1)` one-intersection mates.

Consequently every linear-programming inequality depending only on the
Johnson-scheme inner distribution takes exactly the same value on

```text
the disconnected affine control, and a hypothetical connected candidate.
```

This eliminates the plain Delsarte distance-distribution probe before any
formalization.  Connectedness is not an inner-distribution statistic.
Higher distance-distribution wrappers cannot locate the obstruction.

## Wide divergence and cut

The literature translation suggested the following candidate currencies:

- partial-affine-plane completion or stability;
- Deza/two-distance constant-weight stability;
- binary hull or bicycle dimension;
- self-dual binary matroid circuit--cocircuit constraints;
- an even-lattice discriminant obstruction for the Gram matrix (P2);
- association-scheme or coherent-closure forced by the matching parity;
- a Smith/Lefschetz obstruction for the free part-swapping involution of the
  Levi graph;
- entropy stability for the near-Steiner packing;
- an algebraic-geometry/Frobenius constraint on the binary row variety;
- Pfaffian or perfect-matching divisibility;
- completion by `q` ideal blocks through a Hall/edge-colouring theorem.

The bounded cut is:

1. **STOP: Johnson/Delsarte inner-distribution LP.**  It is refuted by the
   identical affine control distribution above.
2. **STOP: parameter-only p-rank/SNF and generic packing regularity.**  The
   literature hypotheses either require constant concurrence (already a
   completion) or explicitly permit complicated regular leaves.
3. **LIVE, geometry owner:** a polarity-sensitive completion theorem, or a
   derivation of the extra semipartial uniformity hypotheses isolated in the
   self-polar configuration audit.
4. **LIVE, incidence owner:** coherent closure or a finer coordinate
   invariant using the cross-neighborhood matching parity from
   `Erdos85CrossNeighborhoodTransportLocation`; unlike (P1), that statistic
   can distinguish how leave edges are located.
5. **BOUNDED algebraic probe only:** test a 2-primary lattice discriminant
   form.  Stop if it yields merely the already-known lower valuation of
   `det A`, rather than a polarity-sensitive upper obstruction.

### Binary bicycle/matroid probe: stopped at the existing kernel interface

Let `C = row_F2(A)`.  Since `A` is symmetric,

```text
C^perp = ker_F2(A),
C intersect C^perp = im_F2(A) intersect ker_F2(A).       (P3a)
```

The latter is exactly the bicycle (code-hull) space.  The standard binary
matroid circuit--cocircuit theorem says that every circuit meets every
cocircuit evenly; in matrix language this is only the defining orthogonality
between `C` and `C^perp`.  The standard bicycle tripartition likewise depends
only on membership in the two spaces in (P3a).

Reducing the square identity modulo two (for even `q`) gives

```text
A^2 = I + J + D.                                        (P3b)
```

Consequently a bicycle word is precisely a vector `A y` for which
`(I+J+D)y=0`.  This is not a new constraint: it is the same binary-kernel
shore and one-step `A` transport already used in the Baer involution audit.
Conversely, the abstract matroid forgets the integer row weight `q`, the
exact `0/1` common-neighbour counts, and the location of the defect edges;
its circuit--cocircuit parity therefore cannot distinguish the disconnected
affine control from a connected candidate without adding those data back.

The bicycle/matroid candidate is **stopped**.  A useful code invariant must
retain coordinate-labelled higher products (for example individual
cross-neighbour matchings), not merely the row space, kernel, hull, or their
dimensions.

### Perfect-hypergraph-matching translation: exact terminal, no lower bound

Regard the `q^2` row supports as the edges of a `q`-uniform, `q`-regular
linear hypergraph on `q^2` points.  A hypergraph matching is exactly a clique
in the defect graph `D`.  Therefore a perfect matching of `q` rows gives a
`K_q` in the `(q-1)`-regular graph `D`; that clique is a whole connected
component.  In the NONBIP-CONNECTED branch, proving a perfect matching would
be terminal.

There is a useful exact maximal-matching ledger.  Let `M` be a maximal
matching of `t` rows, let `U` be their disjoint union, and for each row `B`
outside `M` put

```text
a_B = |{E in M : E meets B}|.
```

Maximality and linearity give `1 <= a_B <= t`.  Counting incidences between
the selected and unselected rows in two ways gives

```text
sum_(B outside M) a_B = t q(q-1),
sum_(B outside M) (t-a_B) = t(q-t).                (PM1)
```

At the penultimate value `t=q-1`, the total deficit is only `q-1`.  The
uncovered point set `W` has size `q`, and every unselected row meets `W`, with

```text
sum_(B outside M) (|B intersect W|-1) = q-1.        (PM2)
```

Thus `t=q-1` would reduce the branch to a `q`-point near-transversal with total
excess `q-1`.  The missing step is not the terminal but any theorem forcing
`t>=q-1`.

The matching literature does not supply it.  Pippenger--Spencer and later
linear-hypergraph results give nearly perfect matchings when uniformity is
fixed and codegree is negligible relative to a growing degree, or under
stronger minimum codegree hypotheses.  Here uniformity and degree are both
`q`, and general regular linear hypergraphs need not have perfect matchings.
The fixed-free `q=4` control already satisfies these same hypergraph
parameters without a size-`q` matching.  Hence a usable lower bound must
exploit the self-polar labelling beyond regularity and linearity; no such
published theorem was located.

The generic perfect-matching lane is therefore **stopped**.  `(PM1)--(PM2)`
identify an honest future entry point only if a polarity-sensitive argument
first reaches `t=q-1`; proving the ledger alone is not a chain to A-REG.

### Bounded lattice probe: stopped

Because `A` is symmetric with zero diagonal, it is the Gram matrix of an
even integral bilinear form whenever it is nonsingular.  The standard
signature congruence for an even lattice does not depend only on the order of
its discriminant group.  Its input is the full finite quadratic form

```text
q_A : Z^(q^2) / A Z^(q^2) -> Q / 2Z,
q_A([x]) = x^T A^(-1) x.                              (P3)
```

The square-root and matrix-tree identities determine the group order
`|det A| = q^2 sqrt(tau(D))` and hence its 2-adic valuation.  They do not
determine (P3): evaluating it requires `A^(-1)`, equivalently the full
coordinate-level square root rather than the spectrum, determinant, or leave
degree data.  Even the underlying abelian group is not fixed by its order;
the earlier nonsplitting Smith audit exhibits the same obstruction.

Therefore a Brown/Milgram or discriminant-form calculation cannot currently
produce a signature restriction without assuming information at least as
strong as the unknown integral square root.  The probe reaches its declared
stop condition: at the available interface it reduces to the already-banked
determinant valuation, with no polarity-sensitive upper bound.  No lattice
formalization should be opened unless a future theorem first determines a
nontrivial primary component of (P3) from entrywise incidence.

The main lesson is negative but decision-relevant: the natural coding and
packing projections erase exactly the connected-vs-parallel-class datum.
Any successful theorem must retain the self-polar coordinate labels or the
nonlinear cross-neighborhood matching locations.
