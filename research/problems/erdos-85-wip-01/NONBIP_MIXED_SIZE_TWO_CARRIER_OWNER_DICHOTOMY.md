# Size-two triangle carrier: exact owner dichotomy

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: exact q-generic consequence of the second exterior block identity;
no terminal claimed.

## Setup

Use the notation of `NONBIP_MIXED_EVEN_EXTERIOR_CARRIER_AUDIT.md`.
The weight-two defect component is `C`, the other component is `F`,

```text
B=A_G[C,F],  H_C=A_G[C,C],  H_F=A_G[F,F],
```

and the simultaneous ambient block identity is

```text
H_C B + B H_F = J.                                      (1)
```

Let `{c_0,c_1,c_2}` be the defect triangle supplied by the size-two
component theorem, and put `S_i=N_B(c_i)`.  The carrier audit proves that
the `S_i` are disjoint, each has cardinality `n=q-2`, and every `f in S_i`
has exactly two `B`-neighbors.  Write them as

```text
N_B(f)={c_i,r_f}.
```

The companions `r_f` are distinct as `f` varies in `S_i`: two equal
companions would make `c_i` and that companion have two common ambient
neighbors, violating the C4/common-neighbor cap.

## The self-part dichotomy

Evaluate (1) at `(c_i,f)`.  Since `H_C` is loopless and the two
`B`-neighbors of `f` are exactly `c_i,r_f`,

```text
(H_C B)_(c_i,f) = 1_{H_C(c_i,r_f)},
(B H_F)_(c_i,f) = deg_H_F(f,S_i).
```

Consequently

```text
1_{H_C(c_i,r_f)} + deg_H_F(f,S_i) = 1.                 (2)
```

This is an exclusive alternative, not just a bound.  In particular
`H_F[S_i]` has maximum degree one.  If

```text
a_i = #{f in S_i : H_C(c_i,r_f)},
```

then the other `n-a_i` vertices form the endpoints of a matching in
`H_F[S_i]`, so

```text
e_H_F(S_i)=(n-a_i)/2,       a_i = n (mod 2).            (3)
```

At `q=8`, every `a_i` is therefore even.  This parity is owner information
which is invisible in the defect-only support statement.

## Cross-part owner balance

For `j != i`, the same entrywise calculation gives

```text
1_{H_C(c_j,c_i)} + 1_{H_C(c_j,r_f)}
  + deg_H_F(f,S_j) = 1.                                 (4)
```

Thus if `c_i c_j` is an ambient edge, then there are no ambient edges from
`S_i` to `S_j` and no companion `r_f` is adjacent to `c_j`.  If it is not
an ambient edge, each `f in S_i` chooses exclusively between one ambient
neighbor in `S_j` and the companion incidence `H_C(c_j,r_f)`.

Let

```text
h_ij = 1_{H_C(c_i,c_j)},
b_ji = #{f in S_i : H_C(c_j,r_f)},
e_ij = e_H_F(S_i,S_j).
```

Summing (4) over `f in S_i` gives

```text
e_ij + b_ji = n(1-h_ij).                                (5)
```

Swapping `i,j` leaves `e_ij` and `h_ij` unchanged, hence also yields the
non-obvious companion balance

```text
b_ji=b_ij.                                              (6)
```

Ambient edges on a defect triangle form a matching, so at most one of its
three pairs has `h_ij=1`.  Equations (3), (5), and (6) give a small integer
owner ledger for both canonical triangle cases (zero or one ambient edge),
while the first block identity simultaneously requires defect cross-degree
one or two between every pair `S_i,S_j`.

## Disposition

The carrier is now constrained in both diagonal blocks:

* `D_F[S_i]` is empty and every vertex has defect cross-degree one or two;
* `H_F[S_i]` is a matching selected by the complementary companion
  incidences (2);
* every cross-part ambient edge count is exactly balanced against companion
  incidences by (5)--(6).

This does not yet contradict `[q-2,2]`.  The next honest test is whether the
combined integer ledger plus the diagonal Gram blocks permits either of the
two triangle cases.  A scalar parity argument using only (3) is insufficient:
for even `n`, all values `a_i in {0,2,...,n}` remain arithmetically possible.
