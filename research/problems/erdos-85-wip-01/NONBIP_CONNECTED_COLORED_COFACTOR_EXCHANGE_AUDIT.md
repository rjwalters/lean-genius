# NONBIP-CONNECTED colored cofactor-exchange audit

Status: bounded falsification after divergence round 74, 26 August 2026.
The natural colored-monomer refinement repairs the raw sign-count imbalance,
but its local cycle-exchange graph still violates Hall.

## Why colors are necessary

In `M=A_K-diag(t)`, a diagonal coefficient `-t_v` is naturally the sum of
`t_v` negative loop choices, one for each triangle owner at `v`.  Therefore a
Leibniz term of magnitude 256 represents twice as many colored monomials as a
term of magnitude 128.  Sol3's raw counts

```text
|128|: +52 / -46       |256|: +42 / -45
```

become exactly balanced after this expansion:

```text
positive colored units = 52 + 2*42 = 136
negative colored units = 46 + 2*45 = 136.
```

The common factor 128 records owner-color choices shared by every term and
can be divided out without changing Hall ratios.

## Exact exchange test

`nonbip_connected_colored_cofactor_exchange_q4.py` enumerates all 185 nonzero
cofactor terms for the first faithful q4 triangle `(0,1,5)`.  Each cofactor
minor term is embedded as a full permutation by sending its deleted row to
its replaced root column.  Opposite-sign colored units are joined when their
permutations differ by one alternating cycle.  This is the direct rooted
analogue of the positive Levi matching-exchange mechanism.

```text
expanded signs                         136 / 136
single-cycle exchange edges                 4,336
isolated colored units                           0
maximum matching                         132 / 136
```

Thus local availability again does not imply Hall.  Allowing up to two
simultaneous nontrivial cycles raises the edge count to 8,640 but leaves the
same `132/136` maximum matching.  The four-pair deficit is therefore not
repaired by the first multi-cycle relaxation.

## Verdict

Expanding diagonal weights into owner-colored monomials refutes the claim
that the numerical 2-to-1 cancellation by itself forbids a term involution:
the colored shores really are equinumerous.  Nevertheless, neither a single-
cycle nor a two-cycle exchange proves the cofactor cancellation, even on the
smallest exact control.  A surviving proof must use a more global packet
transport or a pre-expansion algebraic identity.  This does not weaken the
reviewed target `H^T adj(M)1=0`; it cuts another proposed mechanism for it.
