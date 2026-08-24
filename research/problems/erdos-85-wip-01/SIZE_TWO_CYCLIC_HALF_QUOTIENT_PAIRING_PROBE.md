# Half-quotient parity pairing probe

Date: 2026-08-24

Owner: codex-sol-1

Scope: `BinarySizeTwoCyclicPackingBound`; divergence-round #7 binary descent

## Verdict

Reducing a `q=2m` routing block modulo `m` and then modulo two produces an
exact four-point boundary: two consecutive odd row vertices and two
consecutive odd column vertices.  This is a useful concrete form of the
first augmentation quotient.

Crucially, the projected graph has maximum degree two: every quotient row
and column has only two lifts in the original partial permutation.  Hence it
is a disjoint union of paths and cycles, with exactly four degree-one
vertices.  Their connected components define a **canonical three-valued
pairing invariant**: row--row plus column--column, or either of the two cross
pairings.

This corrects the first version of this note, which treated the projection
as an arbitrary binary 1-chain and falsely declared the pairing
noncanonical.  The surviving gap is global: reciprocity reverses each dart
into a generally different block, so it does not transpose one whole folded
block or automatically transport its pairing.  The next theorem must show
that the scattered reverse paths recombine coherently across at least three
fibers.

## Exact projection

Fix `(x,t)` and use relative absolute coordinates for its partial
permutation:

```text
row coordinate     r = y-x,
column coordinate  p = z-x.
```

There is one edge in every row except `t,t+1`, and one edge in every column
except `0,-1`.  Let `pi : Z/q -> Z/m` be reduction, and define the binary
matrix

```text
B_(x,t)(i,j)
  = #{ routing edges with pi(r)=i and pi(p)=j } mod 2.
```

Every residue modulo `m` has two lifts.  A row residue different from
`pi(t),pi(t+1)` retains both lifts and therefore has even projected degree.
Each of the two hole residues loses one lift and has odd degree.  Since
consecutive residues remain distinct when `m>1`,

```text
rowBoundary(B_(x,t)) = e_(pi t) + e_(pi(t+1)).
```

The identical column calculation gives

```text
columnBoundary(B_(x,t)) = e_0 + e_(-1).
```

This uses only the exact two-punctured permutation law.  It is independent
of the locations of the surviving entries and agrees with the valuation-one
calculation in `SIZE_TWO_CYCLIC_AUGMENTATION_FILTRATION_PROBE.md`.

There is more structure than the boundary vectors alone record.  A quotient
row has two original lifts.  If it is not a hole residue, its two surviving
edges either project to distinct columns, giving binary degree two, or to the
same column and cancel, giving degree zero.  A hole residue has one surviving
lift and therefore degree one.  The same statement holds on the column
shore.  Thus every vertex has degree at most two, and precisely the four
boundary vertices have degree one.

## The canonical pairing type

Regard `B` as a 1-chain in the complete bipartite graph with row shore
`R=Z/m` and column shore `C=Z/m`.  Since its maximum degree is two, each
nontrivial connected component is a path or a cycle.  Exactly two path
components have odd endpoints, and they pair the four boundary vertices in
one of

```text
RR | CC,
R_t C_0 | R_(t+1) C_(-1),
R_t C_(-1) | R_(t+1) C_0.
```

Here `R_t,R_(t+1)` denote the two row holes after reduction and `C_0,C_(-1)`
the column holes.  No path-decomposition choice is involved: connectedness
inside a maximum-degree-two graph determines the pairing.  Cyclic components
are irrelevant to it.

The boundary vectors do not determine which of the three types occurs.
Cycle-space modifications can change the pairing when they are realized by
another maximum-degree-two folded permutation.  Thus the pairing is genuine
additional information carried by the projected support, not a consequence
of the four holes alone.

## Reciprocity does not repair the loss at first level

For an original route

```text
(x,t) --r--> (y,s),       y=x+r,
```

the point in the absolute partial-permutation block is `(y,z)` with
`z=y+s`.  Reversal puts the point `(x,x+t)` in the block indexed by `(y,s)`.
Thus reciprocity couples individual lifted entries of different blocks.  It
does not send all edges of `B_(x,t)` to one other block.  The `q-2` reverse
darts scatter among blocks indexed by `(y,s)`, with both indices depending
on the entry.  Consequently block transpose does not prove equality of
pairing types, and a path in one folded block need not reverse to a path in
one folded block.

This scattering is now the exact interface rather than a reason to discard
the invariant.  A successful proof must follow a paired boundary path dart
by dart and show that its scattered reversals recombine into paths whose
pairing types obey a global parity or cocycle law.  The lift bit of each edge
over its modulo-`m` projection is a likely necessary part of that transport.

## Stop condition

The three pairing types are valid and canonical for every folded routing
block.  Do not claim that reciprocity transports them blockwise.  The next
bounded probe should retain one of:

1. the lift bit / second augmentation coefficient of every routed dart;
2. a dartwise path-following relation showing how reverse path fragments
   recombine across blocks;
3. an exact reciprocity equation on the global collection of pairing types
   and lift cocycles.

Merely counting the four odd vertices adds no coupling, but the connected
pairing type is a real finite quotient which survives the bounded probe.
