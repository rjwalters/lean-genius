# Local countermodel to diagonal transport

Node: `A-REG-NONBIP / all size-two`; divergence round 104.

Status: q-generic falsifier to the one-pair endpoint-tile/no-square condition.

## Construction

Let `n=2q`, where `q` is binary and `q>=8`, and let `P` be the translation
permutation on `Z_n`.  Define

```text
S_c=P+P^(-1),
S_d=P^3+P^(-3),
X=I+P^(n/2).
```

The two diagonal matrices are symmetric zero--one two-regular matrices.
Because `n` is a power of two, both shifts `1` and `3` generate `Z_n`; hence
each diagonal matrix is one connected cycle.  The cross block `X` is also
zero--one and two-regular (a union of small incidence-cycle components).

The endpoint tiles have translation supports

```text
supp(S_c X)={1,-1,n/2+1,n/2-1},
supp(X S_d)={3,-3,n/2+3,n/2-3}.
```

For `n>=16` these are disjoint four-sets.  Therefore both products are
zero--one four-regular matrices and

```text
supp(S_c X) intersect supp(X S_d)=emptyset.           (1)
```

This is exactly the local diagonal endpoint-tile disjointness forced by the
absence of an ambient four-cycle.

The dependency-free verifier
`verify_size_two_diagonal_transport_local_countermodel.py` checks the
construction at `q=8,16,32`, including symmetry/looplessness/degree,
connectedness of both diagonal cycles, binary four-regular products, and
support disjointness.

## Scope

The construction is not a complete all-color block family and does not
partition `J` through the remaining via colors.  It proves that a
no-commuting-square or diagonal-transport argument on one component pair is
insufficient even when both self-indexed diagonal factors are connected
cycles.

Any viable transport complex must use at least a third component and the
reuse of one cross factor in the complete intermediate-color tilings.  Local
monodromy around `S_c--X--S_d` alone has this uniform escape.
