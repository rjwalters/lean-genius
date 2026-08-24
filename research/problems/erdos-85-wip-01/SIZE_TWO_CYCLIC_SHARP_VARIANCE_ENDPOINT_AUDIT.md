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

The first DIMACS encoding of this flag used auxiliary integer load variables.
Z3's Boolean CNF exporter treated the surviving arithmetic equalities as
independent propositional atoms, producing a spurious q8 SAT verdict under
kissat.  The probe now encodes the profile entirely with pseudo-Boolean
implications and rejects any non-Boolean theory atom left after CNF
conversion.  With the repaired encoding, native Z3 and kissat both return
UNSAT at q8 a=1.  Earlier sharp-profile DIMACS verdicts are invalid; the
native Z3 verdicts listed above are unaffected.

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

## Quantitative sharp-source census

The probe option `--min-sharp-sources N` requires the sharp profile at at
least `N` source cells and leaves every other source unrestricted.  At q=8,
with exact hits and reciprocity but no caps, the exact threshold is

```text
a=1: N=32 SAT, N=33 UNSAT
a=2: N=32 SAT, N=33 UNSAT.
```

Thus the all-sharp contradiction is not brittle: reciprocity forces at least
16 of the 48 source cells above the minimum block-row variance.  At q=6,
a=1, even `N=1` is UNSAT although the unrestricted instance is SAT; q=4
allows all 8 sources to be sharp.  q10 threshold runs were inconclusive and
stopped.

For q8, any non-sharp positive deviation vector has squared energy at least
4 instead of the sharp value 2.  The census therefore improves the cap-free
block-row variance lower bound from 96 to at least 128.  This is still below
the same-fibre cap ceiling 336, so it is an amplification datum rather than
the terminal contradiction.  A q-generic proof must determine whether the
16-source loss is a constant fraction or only a two-hole `2q` correction.
