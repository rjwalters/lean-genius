# H7 block-spectral decomposition audit

Date: 2026-08-26

## Setup

Order the canonical H7 adjacency matrix by the seven high and forty-two low
vertices:

```text
A = [ 0  B ]
    [ B' C ].
```

The `7 x 42` matrix `B` is fixed by the empty/singleton/pair support pattern;
`C` is the unknown low graph.  Each high has degree 8, every pair of highs has
exactly one common pair-support low, and every high/low pair has exactly one
common low neighbor.  Therefore

```text
B B' = 7 I + J,             B C = J.                 (1)
```

These identities are independent of the chosen empty-sector mask.

## Forced invariant subspaces

For every `x perpendicular 1` in the six-dimensional high difference space,

```text
A (x, 0)    = (0, B' x),
A (0, B'x)  = (7x, 0).
```

Since `BB'` is 7 on this space, `B'` is injective there.  Thus `A` has six
copies each of `sqrt(7)` and `-sqrt(7)`.

The three-dimensional space spanned by

```text
H = (1_7, 0),   L = (0, 1_42),   S = (0, B'1_7)
```

is invariant, with columns in the basis `(H,L,S)`

```text
Q = [ 0  8 14 ]
    [ 0  7  7 ]
    [ 1 -1  0 ].
```

Its characteristic polynomial and real roots are

```text
q(x) = x^3 - 7x^2 - 7x + 42,
-2.5026715827, 2.3444445032, 7.1582270794.
```

Finally

```text
W = ker(B) intersect 1_42^perp
```

has dimension 34 and is invariant under `C`, because (1) gives `BCy=0` and
`<1,Cy>=<C1,y>=0` for `y in W`.

For `C` itself, the six-dimensional space `B'(1^perp)` is a zero eigenspace.
The span of `1_42` and the support-size vector `s=B'1_7` is invariant, since

```text
C 1 = 7*1 - s,             C s = 7*1,
```

and has characteristic polynomial `x^2-7x+7`.

## Exact characteristic-polynomial factors

Let `r(x)` be the characteristic polynomial of `C|W`, a monic integral
polynomial of degree 34.  The decomposition forces

```text
charpoly(C) = x^6 (x^2 - 7x + 7) r(x),
charpoly(A) = (x^2 - 7)^6 (x^3 - 7x^2 - 7x + 42) r(x).       (2)
```

This is the nonregular replacement for the missing scalar relation between
the full adjacency matrix and its deficiency graph.

## Residual moments

Write `T` for the number of all-low triangles and
`R = tr(A D^2)`, using the deficiency relation from
`H7_FIFTH_MOMENT_PIVOT_AUDIT.md`.  Subtracting the fixed factors in (2) from
the full adjacency moments gives the first five power sums of the 34 roots of
`r`:

```text
p1 = -7,
p2 = 203,
p3 = 6T - 196,
p4 = 1379,
p5 = R + 72T - 2233.
```

Newton identities give the first coefficients of `r`:

```text
e1 = -7,
e2 = -77,
e3 = 2(T+294),
e4 = -7(2T-411),
e5 = (R - 698T - 116991)/5.
```

Because `r` is integral, this yields the exact new congruence

```text
R = 3T + 1  (mod 5).                                  (3)
```

Equation (3) is the first concrete arithmetic consumer exposed by the block
decomposition.

## Bounded contradiction probes

The degree-four residual Hankel determinant is

```text
-12 (102 T^2 - 5243 T - 27979).
```

Positive semidefiniteness permits

```text
-4.8742... <= T <= 56.2762...,
```

which contains every combinatorially plausible all-low triangle count.
The localizing matrix for residual eigenvalues in `[-6,6]` is weaker.  Thus
moments through degree four do not exclude H7.  The seven-vertex empty-mask
principal subgraphs have spectrum inside `[-3,3]`, so bare Cauchy interlacing
against the much wider residual window also gives no mask exclusion.

## Verdict

The block decomposition **passes** as new exact structure: (2) and congruence
(3) hold for every H7 completion and directly address the nonregularity that
killed the scalar fifth-moment transfer.  The bounded scalar-moment and bare
interlacing endgames are **cut**.

The next legitimate consumer is not another moment bound.  It is a
combinatorial evaluation of `R mod 5` from the colored deficiency degrees and
the fixed empty mask, tested across all 43 masks.  If any mask forces a residue
different from `3T+1`, (3) excludes it with a short arithmetic proof.  A second
possible consumer is a finite-field factor/rank obstruction derived directly
from (2).  Formalizing the full invariant-subspace decomposition should wait
until one of these bounded consumers changes a mask's status.

