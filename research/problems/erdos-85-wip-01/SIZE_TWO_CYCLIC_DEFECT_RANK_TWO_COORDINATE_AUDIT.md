# Defect-rank two-coordinate dependency audit

Node: `BinarySizeTwoCyclicPackingBound` under A.5.3 / A-REG-NONBIP.

## Question

The cap-free q8 reciprocal system forces total defect rank

```text
sum_p r(p) >= q^2,
```

where `r(p)` is the number of target fibres missed by source `p`.  This
audit asks whether that amplification is already forced by either exact-hit
family separately:

* target-row hits: each source meets every allowed target base exactly once;
* absolute-column hits: each source meets every allowed absolute second
  coordinate exactly once.

The probe now exposes the diagnostic flags `--drop-row-hits` and
`--drop-column-hits`.  It refuses to drop both, so every query retains the
degree law `deg(p)=q-2` and the defect-rank interpretation remains exact.

## Verdict

With loopless reciprocity and no common-target caps, both one-coordinate
relaxations attain the pointwise minimum `r(p)=1` at every source:

```text
q=8, a=1, drop row hits:     sum r <= 48  SAT
q=8, a=1, drop column hits:  sum r <= 48  SAT
q=8, a=2, drop row hits:     sum r <= 48  SAT
q=8, a=2, drop column hits:  sum r <= 48  SAT
```

The full system has 48 sources and minimum 64 at both `a=1,2`, so dropping
either family erases the entire extra `2q=16` defect charge, not merely part
of it.

## Consequence for a q-generic proof

The candidate lower bound is genuinely a simultaneous-routing theorem.  It
cannot follow from:

* one local Hall--Paige/near-complete-mapping obstruction;
* reciprocity plus only the row routing;
* reciprocity plus only the column routing; or
* a sum of independent row and column lower bounds.

In permutation coordinates, the proof must retain at once that `r` labels
permute the allowed target rows, `s=psi_p(r)` labels permute the allowed
target columns, and `u=-t-r-s` records their fibre sum.  Equivalently, the
extra `2q` charge is an incompatibility between two transverse punctured
matchings under the shifted-base reciprocal involution.

This also sharpens the proposed repair-orientation route.  Prescribed
indegrees for collision edges cannot be derived from one projection alone:
the demand vector has to be the discrepancy between the row and column
repairs.  Hakimi's orientation theorem can only enter after that
two-coordinate discrepancy is explicitly constructed.
