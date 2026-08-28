# Countermodel to the bare tile-intertwiner interface

Node: `A-REG-NONBIP / all size-two`; follow-up to divergence round 102.

## Construction

Let `q=2^k`, `q>=8`, put `G=Z_(2q)`, and let

```text
S = {q} union {+/-1, ..., +/-(q/2-1)}.
```

The Cayley graph `D=Cay(G,S)` is a simple `(q-1)`-regular graph on `2q`
vertices.  It is connected because `1 in S`, and it is nonbipartite because
`0,1,2` is a triangle.

For `g in G`, let `P_g` be the translation permutation matrix.  The `2q`
matrices `P_g` have disjoint supports and sum to `J`; every one commutes with
the circulant adjacency matrix of `D`.

Partition `G` into the consecutive four-sets

`Q_e={4e,4e+1,4e+2,4e+3}`

and put

`Y_e=sum_(g in Q_e) P_g`.

Then each `Y_e` is a zero--one four-regular matrix and

```text
sum_e Y_e = J,
D Y_e = Y_e D.
```

For the reverse ordered component pair use

`Y_e^rev=Y_e^T=sum_(g in Q_e)P_(-g)`.

Thus any number of copies of `D` admit reciprocal partitions of every
complete bipartite component pair into `q/2` disjoint four-regular integral
fractional isomorphisms.  The construction is uniform in binary `q`.

Moreover, every tile already has a local two-factor square root of the same
shape as an intermediate route product:

```text
Y_e = (P_0+P_1)(P_(4e)+P_(4e+2)).
```

Both factors are zero--one matrices with row and column sum two, and their
product is zero--one because the four resulting translations are distinct.
Thus even a theorem which classifies one tile together with its labeled
`K_2,2` rectangle factorization cannot close the branch.

The dependency-free verifier
`verify_size_two_tile_intertwiner_countermodel.py` checks the construction at
`q=8,16,32`, including simplicity, degree, connectivity/nonbip witnesses,
zero--one supports, the `J` partition, commutation, and reciprocal transpose.
It also verifies the displayed two-factor factorization for every tile.

## Consequence

The exact refinement

```text
Y_e^(c,d) is 0/1 and 4-regular,
sum_e Y_e^(c,d)=J,
D_c Y_e^(c,d)=Y_e^(c,d)D_d,
(Y_e^(c,d))^T=Y_e^(d,c)
```

is not contradictory, even with connected nonbipartite defect graphs.  It
cannot by itself supply an association-scheme or polarity terminal.

The actual graph has the additional coherent factorization

`Y_e^(c,d)=X_ce X_ed`

by the **same** reciprocal two-regular blocks across every ordered triple,
with symmetric diagonal cycle blocks and the within-component Gram leaves.
The Cayley construction supplies square roots **tile by tile**, but it does
not reuse one common block `X_ce` consistently as the other endpoint `d`
varies.  Therefore the next terminal must use factor compatibility among at
least three tiles; classifying sparse fractional-isomorphism partitions, or
their individual rectangle factorizations, is another relaxation and should
be stopped.
