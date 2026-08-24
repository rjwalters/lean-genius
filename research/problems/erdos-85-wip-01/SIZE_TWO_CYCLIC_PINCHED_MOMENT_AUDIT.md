# Pinched fourth-moment audit for the no-empty packing target

This is a bounded falsifier for divergence round 15, candidate 1.  It keeps
the actual interface of `SizeTwoCyclicSameDifferenceCode`: there is no empty
fibre hypothesis.

Let `q` be the cyclic order, `d = q - 2`, and let `K` be the symmetric
adjacency matrix of a reciprocal code on the `q d` allowed cells.  For an
allowed-difference fibre `t`, write `P_t` for its coordinate projector and

```
G_t = P_t K^2 P_t = (K P_t)^T (K P_t).
```

Each source has degree `d`, so every diagonal entry of `G_t` is `d`.  The
same-difference cap says every off-diagonal entry is either zero or one.
Consequently the exact cap upper bound is

```
sum_t ||G_t||_F^2 <= d * (q d^2 + q(q - 1))
                         = q d (d^2 + q - 1).             (U)
```

This is the strongest bound supplied by the cap alone: every permitted
off-diagonal entry may contribute one.

## What positivity and pinching actually give

For every `t`, `G_t` is positive semidefinite, has size `q`, and has trace
`q d`.  The rank/trace inequality gives

```
||G_t||_F^2 >= (q d)^2 / rank(G_t) >= q d^2.
```

After summing over the `d` fibres this is only

```
sum_t ||G_t||_F^2 >= q d^3.                               (L0)
```

The gap between (U) and (L0) is `q d (q - 1)`, exactly the entire
off-diagonal cap budget.  Regularity, self-adjointness, and generic matrix
pinching therefore give no pressure at all toward a contradiction.

Even a *new* proof of one linear dependence among the `q` columns of every
`K P_t` would not close the estimate.  Replacing the rank by `q - 1` gives

```
(q d)^2/(q - 1) <= q(d^2 + q - 1)
```

for `d=q-2`: after cancellation this is equivalent to
`q(q-2)^2 <= (q-1)((q-2)^2+q-1)`, whose right-minus-left side is
`2q-3 > 0`.  Two dependencies would reverse the inequality already at
`q=4`, contradicting the known satisfiable `q=4` instance.  Thus the hoped
for pair of quotient dependencies cannot follow from the exact-hit laws.
The row/column hit equations specify marginal sums of edge blocks; they do
not provide null vectors of each individual column matrix `K P_t`.

## Verdict

The unweighted pinched fourth-moment / fusion-frame sandwich is **cut**.
Its universal lower bound is just the forced diagonal contribution, while
the cap upper bound leaves all off-diagonal mass available.  Any viable
spectral argument must introduce a genuinely code-specific weighted or
pair-rooted operator whose lower bound couples different fibre labels; a
scalar sum of the diagonal blocks of `K^2` cannot prove
`SizeTwoCyclicPackingExclusion`.

This cut applies equally with or without an empty fibre and does not weaken
the corrected no-empty target.
