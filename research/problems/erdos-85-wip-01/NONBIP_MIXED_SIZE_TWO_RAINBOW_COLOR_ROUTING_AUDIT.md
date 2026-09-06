# Rainbow color routing: scalar cut and remaining labels

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: the proposed missing-color scalar pressure is an identity. Three
orthogonal proper colorings, even with the near-minimal row profile, are
feasible at an abstract interface. The full labeled realization stays open.

## Exact missing-color partition

Use the notation and hypotheses of
`NONBIP_MIXED_SIZE_TWO_RAINBOW_CENTER_SELF_INDEX.md`, in particular
`H=H_C`, `R_i=N_L(c_i)`, `W_i=N_H(c_i)`, `W=union W_i`, and `X=C\W`.
Every edge of `G=L[X]` is a rainbow center. Color it by its unique leaf in
`S_i`, or equivalently by that leaf's companion in `R_i`.

Each of the three colorings is proper: two edges through `x` with the same
leaf would give two ambient common neighbors of `x` and that leaf. The
colorings are pairwise orthogonal: two centers with the same two leaves
would give those leaves two common neighbors. Thus each ordered pair of
colors identifies at most one edge.

Fix `x in X`. There are `n-deg_G(x)=deg_L(x,W)` missing colors in system
`i`. Equation (11) of the self-index document splits them into:

1. Companions `r in R_i intersect N_H(x)`, for which no exterior endpoint
   route exists at all.
2. Colors routed through selector edges `xy` with `y in W\W_i`.

For the second assertion, the selector-star identity gives
`deg_H_F(v,S_i)=1-|N_B(v) intersect W_i|`. Hence an edge from `x` to `W_i`
has no `S_i` leaf, while one from `x` to either other hole has exactly one.
Equation (11) ensures these routed colors are distinct and disjoint from
the colors already used on `G` and from class 1.

But the count of class 1 is already forced by commutation:

```text
deg_H(x,R_i) = (HL)_(x,c_i) = (LH)_(x,c_i)
             = deg_L(x,W_i).                              (1)
```

Thus the two missing-color counts are exactly
`deg_L(x,W_i)` and `deg_L(x,W\W_i)`. Their sum is the original missing
degree. This is an equality of counts; it does not produce a canonical
bijection between forbidden companions and edges to `W_i`.

Consequently the proposed inequality
`deg_H(x,R_i) <= deg_L(x,W)` is simply `W_i subset W` after (1).
Summing it, or combining its three versions, supplies no new pressure.

## What the colors still have to satisfy

The genuine remaining condition is labeled. For a rainbow edge `ab`, its
color in system `i` must belong to

```text
R_i \ (N_H(a) union N_H(b)).                              (2)
```

Moreover the color `r` must extend, over all selector edges avoiding
`W_i`, to a matching whose uncovered vertices are exactly
`W_i union N_H(r)`. Adding the prescribed pair `N_H(r)` makes a perfect
matching on `C\W_i`; the two pairs are disjoint because `c_i r` is a
selector edge and cannot have an internal common neighbor.

This follows directly by applying the block identity at every `(x,f)`,
where the leaf `f` has selector `{c_i,r}`. These matchings must coexist for
all colors and fibers, retain orthogonality, and ultimately come from one
symmetric exterior adjacency matrix `H_F`. Mere properness does not
impose that last requirement. No converse to full ambient realizability is
claimed here.

## A dense orthogonal-coloring counterledger

The weaker interface consisting of properness, pairwise orthogonality,
rainbow edge count, and unlabelled row-profile counts has explicit models.
The following construction works for every prime `p>=11`. Set
`n=p+1`, `q=p+3`, and let `X` be two disjoint copies of `F_p`.
Join left `x` to right `y` unless `y-x` is 0 or 1. Then

```text
|X|=2(n-1),   deg_G=n-3,
|E(G)|=p(p-2)=n(n-4)+3.                                  (3)
```

Start with the three colorings `c_a(x,y)=x+a*y`, for `a=1,2,3`.
They are proper; any two jointly determine `x,y`, so are orthogonal.
Each original color has exactly `p-2` edges: its intersections with the two
deleted diagonals are distinct singletons, since `1+a` is nonzero.

Choose three distinct slopes `t_a` outside
`{0,1,-1,-1/2,-1/3}`. At least `p-5>=6` choices exist. On the line
`y=t_a*x`, exactly `p-2` edges remain after the two deletions. Choose any
`p-3` of them and recolor them in system `a` with a new color `infinity`.

Each selected line is a matching. Every original color of every system
occurs at most once on it, because `1+b*t_a != 0` for `b=1,2,3`.
Thus properness survives. Orthogonality survives as well: pairs with no
new color retain their old injectivity; pairs with exactly one new color
are injective along the corresponding line; and pairs with two new colors
occur at most once, since the two distinct lines intersect in at most one
edge.

There are now exactly `n` used colors in each system. The new color has
`p-3=n-4` edges. Of the `p` old colors, `p-3` each lost one edge and exactly
three retain size `p-2=n-3`. Consequently each system has:

```text
n-3 color classes of size n-4;
3 color classes of size n-3.                             (4)
```

This also matches the scalar owner profile (22)--(23) in the diagonal Gram
document with all `gamma_ij=1` and `u=0`: assign the three distinct larger
classes to the one `g_j` mark, the one `g_k` mark, and the one slack mark.
Every vertex has exactly three missing colors. No actual companions,
`H`, `D`, `W`, or exterior matrix are asserted by this assignment.

The companion script checks edge counts, properness, orthogonality, all
color-class sizes, and these scalar profiles directly. Its examples include
`p=13,29,61`, hence binary `q=16,32,64`; these are explicit abstract
constructions, not ambient existence evidence or a finite UNSAT census.

## Literature and disposition

The relevant language is orthogonal colorings of the line graph: see
[Ballif, Upper Bounds on Sets of Orthogonal Colorings of Graphs](https://arxiv.org/abs/1110.2237).
For regular graphs with perfect color classes, the corresponding notion is
orthogonal one-factorizations; its relation to Howell designs is described
by [Meszka and Tyniec](https://link.springer.com/article/10.1007/s10623-018-0504-3).
Here the color classes are punctured matchings with prescribed companion
holes, so those unrestricted existence results do not settle our problem.
The explicit construction above is proved here, rather than inferred from
either reference.

Cut the missing-color scalar inequality and the owner-free orthogonal
coloring route. Retain (2), the prescribed matching holes, and symmetric
exterior realization as the missing links. This is not a countermodel to
the complete incidence interface and does not close A-REG-NONBIP.
