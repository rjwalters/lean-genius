# Size-two cyclic sharp-variance endpoint audit

## Role in the no-empty terminal

For each source cell `(x,t)`, let `b_tu(x)` be its number of neighbours in
target fibre `u`.  The exact degree law gives `sum_u b_tu(x)=q-2`.  At the
minimum positive block-row variance, every source has the sharp profile

```text
one target fibre of load 0,
one distinct target fibre of load 2,
all other target fibres of load 1.
```

This is the first positive-variance endpoint above the already impossible
uniform-load stratum.  A variance descent would need this endpoint dead.

## Exact bounded verdict

The full arbitrary-base probe now exposes `--sharp-fibre-loads`.  With exact
row and absolute-column hits and undirected reciprocity, but **no agreement
caps**, the verdicts are:

```text
q=4,  a=1: SAT
q=6,  a=1: UNSAT
q=8,  a=1: UNSAT
q=8,  a=2: UNSAT
q=10, a=1: UNSAT
```

The q8 directed control is SAT, so reciprocity is essential.  One sufficient,
deletion-order-dependent q8 reciprocity core is

```text
33 34 37 44 45 47 57 77.
```

The q4 exception is mandatory calibration: the endpoint is not a tautological
inconsistency of the local sharp profile.

## Consequence

The proposed use of same-fibre caps to kill the sharp endpoint is unnecessary
at the tested orders.  The correct prospective chain is stronger:

1. prove q-generically that exact hits plus reciprocity exclude the sharp
   one-zero/one-double profile for q>=6;
2. construct a cap-preserving descent from any higher positive variance to
   either this sharp endpoint or uniform loads;
3. both endpoints are then impossible without spending another cap.

The finite core shows that aggregate defect circulation is not enough: its
banked count relaxation is SAT.  A proof of step 1 must retain base positions
inside the reciprocal blocks, plausibly through the existing sharp-repair
sign/checkerboard interface or a base-resolved near-transversal parity law.
