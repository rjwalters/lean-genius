# Weight-two mixed-cycle hole decomposition

## Statement

Let `C` be a weight-two alternating-eigenline component at parameter `q`.
Write its internal ambient two-factor as a disjoint union of even cycles

```text
H = disjoint-union_i C_(2a_i),             sum_i a_i=q,
```

and suppose every cycle has propagated to either the T-saturated orientation
(none of its `H`-edges is an exterior trace) or the cross-saturated
orientation (all of its `H`-edges are exterior traces).  Let `F` be the graph
of exterior two-point traces on `C`.

Then the global hole complement

```text
P = K_(q,q) - F
```

is a bipartite 2-factor commuting with `H`.  More precisely:

* every T-saturated cycle of `H` is an isolated component of `P`, equal to
  that cycle itself;
* `P` has no edge of a cross-saturated cycle;
* after deleting the T-saturated cycles, the restriction of `P` to the union
  of cross-saturated cycles is a 2-factor commuting with their cycle union
  and avoiding every internal cycle edge.

Equivalently, every T-saturated cycle is complete in `F` to every other cycle
on the eligible opposite-sign pairs, and has internal trace graph
`K_(a_i,a_i)-C_(2a_i)`.  All remaining freedom is concentrated in one
commuting hole 2-factor on the cross-saturated sector.

## Proof

The alternating eigenline makes every exterior trace join opposite signs.
There are `q` vertices of each sign, and `F` is `(q-2)`-regular.  Therefore
its complement in the complete opposite-sign graph is 2-regular:

```text
degree(P)=q-(q-2)=2.
```

The exact cross-block equation implies `[H,F]=0`.  The complete bipartite
graph `K_(q,q)` also commutes with `H`, because `H` has degree two on both
sign shores.  Hence `[H,P]=0`.

If a cycle is T-saturated, both `H`-neighbors of each of its vertices are
absent from `F` and therefore present in `P`.  They already exhaust degree
two in `P`.  No vertex of that cycle can have any further `P`-neighbor, so
the whole cycle is an isolated component of `P`.  Complementing back inside
`K_(q,q)` proves both cross-completeness and the stated internal trace graph.

If a cycle is cross-saturated, all of its `H`-edges lie in `F`, hence none
lies in `P`.  Removing the isolated T-cycle components leaves every remaining
vertex with degree two, preserves commutation with the corresponding block of
`H`, and leaves precisely the asserted cross-saturated hole sector.

## Important special cases

* If exactly one cycle is cross-saturated, the remaining hole sector lies on
  one cycle.  The reviewed cycle-centralizer lemma makes it
  `Cay(Z/(2b),{+t,-t})` for an odd `t` not congruent to `+1` or `-1`.
  Thus every such mixed profile is completely classified by its cycle
  lengths and this one step.
* For two cycles this recovers
  `WEIGHT_TWO_TWO_CYCLE_MIXED_CLASSIFICATION.md` immediately.
* If two or more cycles are cross-saturated, the unresolved component-side
  problem is no longer an arbitrary trace graph: it is exactly a commuting
  2-factor between a specified disjoint union of cycles, with all diagonal
  cycle edges forbidden.  This is the rectangular-intertwiner frontier.

## Scope

This is a q-generic reduction beneath `A-REG-NONBIP`.  It does not exclude
the cross-saturated hole sector or solve exterior completion.  It does remove
all T-saturated cycles from that algebraic problem and shows that mixed
orientation data are encoded exactly as isolated versus edge-avoiding
components of one global commuting 2-factor.

## Rectangular length-ratio law

The remaining cross-saturated sector has a strong arithmetic restriction.
Take two of its H-cycles `C_(2a)` and `C_(2b)`, and let `Q` be the rectangular
block of `P` between them.  Blockwise commutation says

```text
C_(2a) Q = Q C_(2b).
```

Multiplying by the all-ones vector shows that the row-degree vector `Q 1` is
a 2-eigenvector of the connected cycle `C_(2a)`, hence is constant.  Applying
the transpose gives constant column degree as well.  Write these two degrees
as `r,s`.  Since the whole hole graph `P` has degree two,

```text
r,s in {0,1,2}.
```

Counting the entries of `Q` by rows and columns gives

```text
2a r = 2b s,              equivalently a r = b s.
```

If the block is nonzero, the only cases are

| `(r,s)` | forced half-length relation |
|---|---|
| `(1,1)` | `a=b` |
| `(2,2)` | `a=b` |
| `(1,2)` | `a=2b` |
| `(2,1)` | `b=2a` |

Thus a commuting degree-two hole factor can connect distinct H-cycles only
when their half-lengths differ by exactly a factor of two.  All other pairs
have zero rectangular block.  This turns the formerly arbitrary
rectangular-intertwiner frontier into components supported on equal-length
classes and adjacent levels of the doubling graph on the half-lengths.

The law is necessary, not a full block classification.  In the `(1,1)` case
`Q` is a cycle-intertwining perfect matching (hence a dihedral cycle
isomorphism); in the factor-two cases it has the margins of a two-fold cycle
cover.  Proving that these descriptions are forced entrywise, and classifying
how several such blocks can share the degree-two budget, is the next
component-side consumer.

## Factor-two blocks are the standard cycle covers

The factor-two description is in fact forced entrywise.  Suppose `a=2b` and
the block from `C_(4b)` to `C_(2b)` has row degree one and column degree two.
Write its unique 1 in row `x` as column `f(x)`.  The column margins say that
`f` is two-to-one.  The intertwining equation, evaluated at `(x,y)`, is

```text
1[f(x-1)=y] + 1[f(x+1)=y]
  = 1[y=f(x)-1] + 1[y=f(x)+1].
```

Thus the multiset of images of the two neighbors of `x` is exactly the two
neighbors of `f(x)`.  In particular `f` is a locally bijective graph map

```text
C_(4b) -> C_(2b).
```

Choose the image `c=f(0)`.  The image of `1` is `c+epsilon` for one
`epsilon in {+1,-1}`.  At vertex `1`, one neighbor has already mapped back to
`c`; local bijectivity forces the other to map to `c+2epsilon`.  Induction
around the connected long cycle gives

```text
f(x)=c+epsilon*x  (mod 2b).
```

This is the standard two-fold cyclic covering; each short-cycle vertex has
the two preimages differing by `2b`.  Conversely these maps plainly satisfy
the margins and intertwining law.  Transposing classifies the `(2,1)` case.

Therefore every unequal-length rectangular block of the commuting hole
factor is a dihedral translate of the canonical two-fold cycle cover.  The
only unclassified rectangular case is degree `(2,2)` between equal-length
cycles; degree `(1,1)` is already a dihedral cycle isomorphism.
