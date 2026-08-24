# Extremal positive-variance audit

This is the bounded test of divergence round 17's proposed first positive
variance stratum.  The full probe exposes it as `--minimal-block-variance`.

For a source `(x,t)`, let `b_tu(x)` count its neighbours in target fibre
`u`.  The extremal profile is

```
one b_tu(x)=0, one b_tv(x)=2, and every other block load equal to 1.
```

It has squared deviation two, the smallest value above the already excluded
zero-variance profile.  The audit also imposes full internal support, so the
missing fibre is never `t`.

## Fixed-difference law

For `4 | q`, the sum of the allowed differences is

```
sum_(u in D) u = q/2 + 1  in Z/q.
```

The general weighted hit identity

```
sum_u u*b_tu(x) = 2(t+1)
```

therefore pins the doubled fibre `s` relative to the missing fibre `r`:

```
s-r = c_t := 2t+1-q/2.                                  (1)
```

The residue `c_t` is odd and hence nonzero for binary `q>=8`.  Thus (1) is
an exact q-generic description of every source's block-load defect.

## Solver calibration

At q8 the entire extremal stratum is already impossible under exact hits,
full internal support, and reciprocity, with **no cap constraints**:

```
q8 a=1: reciprocal/no-caps UNSAT; directed/no-caps SAT
q8 a=2: reciprocal/no-caps UNSAT
q8 a=3: reciprocal/no-caps UNSAT
```

The q8 a=1 grouped reciprocity shrink retains the sufficient,
order-dependent block set

```
{33,34,37,45,47,57,77}.
```

The same reciprocal/no-cap query is UNSAT at q6 and q10.  At q10 the
directed source constraints are already inconsistent, so it is not a clean
control for the binary mechanism.  At q12 the directed query is SAT while
the reciprocal query is UNKNOWN at 120 seconds.  No claim is made from the
q12 timeout.

These controls show that at q8 the first positive-variance stratum contains
a real entrywise-transpose obstruction, stronger than a cap collision.  A
descent theorem reaching this stratum would therefore finish without a
second owner-cap argument at the endpoint.

## The proposed second pin does not pin locally

The square-sum identity

```
sum_edges (2*y*u + u^2) = 2(t+1)(2*x+t)
```

is automatic from a single source's exact row and column margins.  It does
not determine the two target bases in the doubled fibre.  Exhaustive q8
single-source matching enumeration gives, depending on `(a,t,r,s)`, between
four and eight different unordered doubled-base pairs.  For example at
`q=8,a=1,x=t=0`, the profile `(r,s)=(2,7)` admits eight different doubled
base pairs.

Therefore the extremal contradiction cannot be a per-source “second moment
pins both bases” lemma.  It must use simultaneous entrywise transpose
consistency around several blocks (or a global symmetric-trade argument).

## Remaining chain

The terminal-sized route is now:

1. prove any full-support capped code can be normalized, without increasing
   cap collisions, until every source has the extremal profile; and
2. prove q-generically for `4|q` that (1), the two affine matching laws, and
   entrywise block transpose admit no simultaneous realization.

Step 2 is strongly supported at q8 but is not yet a theorem; step 1 remains
the positive-variance descent gap.
