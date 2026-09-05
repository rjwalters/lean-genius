# NONBIP-MIXED exterior self-index transport audit

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED`, with emphasis on the
two-component strata at `q=8`.

Status: exact q-generic transport identified; no terminal claimed.

## The block which the internal relaxation omits

Let `C` and `F` be distinct components of the defect graph, of orders
`qm` and `qn`.  Write

```text
H_C = A_G[C,C],       H_F = A_G[F,F],
B   = A_G[C,F],       D_C = A_D[C,C],       D_F = A_D[F,F].
```

Every row of `B` has sum `n` and every column has sum `m`.  Moreover the
global commutation `A_G A_D=A_D A_G`, restricted to the `(C,F)` block,
gives the exact intertwiner

```text
D_C B = B D_F.                                             (1)
```

This is stronger than requiring an internal selector graph on `C` whose
neighborhoods are disjoint across `D_C`-edges.  It couples those selectors
to the *same labeled vertices* in a second connected defect component.

When `C,F` are the only two components, the off-diagonal block of
`A_G^2=(q-1)I+J-A_D` is

```text
H_C B + B H_F = J.                                        (2)
```

Thus both defect and ambient adjacency are transported by the same binary
rectangular block.  Equation (2) is the matrix form of the simultaneous
exterior rectangles; treating its rows independently loses the shared
middle labels.

## An odd-cycle carrier

Reduce modulo two.  Let `Q` be the vertex set of an induced odd cycle of
`D_C`, let `x=1_Q`, and put

```text
y = B^T x  in F_2^F,
z = D_C x  in F_2^C.                                      (3)
```

The coordinate `y_f` is the parity of the number of neighbors of the
exterior label `f` on the displayed odd cycle.  Since every row of `B` has
sum `n`,

```text
1^T y = n |Q| = n                         (mod 2).          (4)
```

Consequently, if the exterior component has odd weight, `y` has odd
Hamming weight and in particular is nonzero.  This is the first unavoidable
exterior carrier produced directly by an odd internal defect cycle.  The
q=4 `[2,2]` control has even exterior weight, so (4) correctly gives no
contradiction there.

Because `Q` is an induced cycle, its two internal cycle neighbors cancel at
every point of `Q`; hence `z` is supported on `C\\Q` and records precisely
the odd defect boundary of the cycle.  Transposing (1) gives the pointwise
boundary transport

```text
D_F y = B^T z.                                             (5)
```

In the two-component case, transposing (2) and applying it to the odd vector
`x` gives the complementary ambient transport

```text
H_F y + B^T H_C x = 1_F.                                  (6)
```

Equations (4)--(6) are simultaneous: the same odd-weight vector `y` carries
the defect boundary and pays the all-ones residue in the ambient equation.
Neither equation is visible in a probe which keeps only `D_C`, a symmetric
internal selector graph, codegree at most one, and disjoint selector
neighborhoods on `D_C`-edges.

The identities can also be read cellwise.  For `c in C` and `f in F`, the
unique common-neighbor array partitions `C x F` into the self-indexed
rectangles

```text
(N_G(w) intersect C) x (N_G(w) intersect F),    w in V.
```

The vector `y` is the parity shadow of exactly those rectangles whose
`C`-side meets `Q` oddly.  Equation (6) says their `F`-side cannot be chosen
independently of the diagonal blocks indexed by the same ambient labels.

## What this buys at order 64

For the two-component partitions:

```text
[6,2] : the small exterior weight is even;
[5,3] : both directions have an odd exterior carrier;
[4,4] : both exterior weights are even.
```

Thus the immediate load-bearing case is `[5,3]`.  Every induced odd cycle
in either component produces a nonzero odd vector in the other component,
with its two images constrained by (5) and (6).  This is genuinely stronger
than the scalar mixed-owner triangle polynomial and than internal
self-indexing alone.

It is not yet a contradiction.  Odd weight by itself is compatible with a
connected 7-regular target, and (5) without (6) is only the already-banked
defect-block intertwiner.  A terminal consumer must combine both equations,
or equivalently show that no `0/1` biregular block of row degree `3` and
column degree `5` can carry the odd-cycle boundary while satisfying the
self-indexed ambient blocks and C4 uniqueness.

The next bounded probe should therefore target `[5,3]` and retain all of:

1. symmetric loopless `H_C,H_F` and connected 7-regular `D_C,D_F`;
2. the actual `0/1` `(3,5)`-biregular cross block `B`;
3. `D_C B=B D_F` and `H_C B+B H_F=J` over the integers, not only modulo two;
4. the diagonal square/Gram blocks and C4 common-neighbor caps; and
5. one induced odd cycle in `D_C`, with the derived carrier (3) retained as
   named output rather than existentially projected away.

SAT at that interface would cut the entire block-linear odd-cycle route and
force a three-block or owner-resolved argument.  UNSAT with a small core
would identify the first credible consumer of the exterior carrier.  No Lean
atomization is warranted before that test.
