# NONBIP-CONNECTED projector-leverage audit

Date: 27 August 2026. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **projector-only route cut; an entrywise cross-sector identity is still required**.

## Terminal scale

For a designated primary sector of dimension `m` carrying adjacency trace
`-q`, the banked growth theorem reduces the desired contradiction to

```text
2 (q-1) m^2 <= q^2.                                  (T)
```

Thus a useful coordinate argument must give `m = O(sqrt(q))`.  This audit
checks whether the diagonal and row identities of a spectral projector do so.

## Exact leverage identities

Let `P` be the orthogonal projector onto an adjacency eigenspace with root
`lambda`, and put `p_x=P[x,x]`.  From `P^2=P`, `AP=lambda P`, and the fact
that every ambient row has `q` ones,

```text
sum_y P[x,y]^2 = p_x,
sum_{y in N_A(x)} P[x,y] = lambda p_x.
```

Cauchy--Schwarz therefore gives the pointwise inequality

```text
lambda^2 p_x^2
  <= q sum_{y in N_A(x)} P[x,y]^2
  <= q p_x,
```

and hence, when `lambda != 0`,

```text
p_x <= q/lambda^2.                                   (A)
```

The square identity on `1^perp`,

```text
A^2 = (q-1)I-D,
```

puts the same projector in the defect eigenspace with
`mu=q-1-lambda^2`.  Since `D` is `(q-1)`-regular, the identical calculation
gives

```text
p_x <= (q-1)/mu^2                                    (D)
```

when `mu != 0`.  Summing `p_x` over the `q^2` coordinates only yields

```text
m <= q^2 min(q/lambda^2, (q-1)/mu^2).                (1)
```

## Why this cannot reach the terminal

The designated-factor hypotheses give an *upper* bound
`lambda^2 < 2(q-1)`, not a positive lower bound of order `q`.  In
particular, (A) becomes weakest precisely for small designated roots.  The
defect companion (D) does not repair this: for a small adjacency root,
`mu` is close to `q-1`, and (1) is still of order `q`, whereas (T) needs
order `sqrt(q)`.  Near `mu=0`, the roles reverse and (A) is again only of
order `q^2`.  At the blind factor `mu=-1`, (D) is vacuous at scale `q^3`.

The same obstruction persists for a primary factor containing several
conjugate roots.  Applying the calculation root by root and adding ranks
cannot improve its order, and discards the signed trace information which
made the factor designated in the first place.

## Precise surviving target

Diagonal leverage, `AP=lambda P`, and `DP=mu P` are therefore not the
missing ambient-coordinate multiplicity theorem.  A viable successor must
couple at least two spectral sectors through the *same zero-one entries* of
`A`; for example, it would need a signed cross-sector identity before
Cauchy--Schwarz, not separate absolute-value bounds after projection.

Concretely, the next claim must state an inequality involving two distinct
projectors `P_i,P_j` and the common neighborhood mask whose summation
retains the trace imbalance.  Repeating (A)/(D), adding higher projector
moments (`P^r=P`), or using only `0 <= p_x <= 1` cannot imply (T).

## Verdict

**CUT:** single-sector projector/leverage methods miss the required rank
scale by at least `sqrt(q)` even in their favorable spectral range.  The
designated-dimension route remains open only through genuinely entrywise,
cross-sector zero-one incidence information.
