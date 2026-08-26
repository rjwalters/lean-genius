# H7 proof-producing preprocessing audit

## Question

Can a separately budgeted, certificate-compatible preprocessing pass turn one
of the 29 missing canonical H7 parents into a qualitatively easier proof job?
This is a different operational mechanism from further cubing: simplify a
whole canonical parent, restart on the residual CNF, and retain a proof route
back to the original formula.

CaDiCaL 3.0.1 was used because it supports initial preprocessing (`-P`), a
simplified DIMACS output (`-o`), an extension stack (`-e`), and native LRAT.
The upstream tool descriptions are the
[CaDiCaL 3.0 tool paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2026.40)
and the [CaDiCaL 2.0 paper](https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24.pdf).
The latter explicitly covers preprocessing/inprocessing together with DRAT,
FRAT, LRAT, and VeriPB proof support.

## Bounded experiment

The probe used missing parent `F7/type2`, materialized by the canonical compact
encoder:

```text
variables  17,633
clauses   720,825
SHA-256   3115dee58497c9c92b4b9d58699cadc755f3630deb52dade1be27d360cb29c60
```

One CaDiCaL process received a strict 60-second budget, ten requested initial
preprocessing rounds, and emitted a simplified CNF, extension stack, and DRAT
trace:

```text
cadical -t 60 -P10 -o F7_t2.simp.cnf -e F7_t2.extend \
  F7_t2.cnf F7_t2.drat
```

It returned `UNKNOWN`.  The written residual had the same declared variable
ceiling and 269,311 clauses.  Solver statistics reported 12,548 eliminated
variables (71.16%), 1,289 fixed variables, 517,498 subsumed clauses, and
135,323 strengthened clauses.  The trace was 131 MiB and the extension stack
1.6 MiB.  Thus the syntactic reduction is real and substantial.

The decisive restart ran native proof-producing CaDiCaL on that residual for
another 60 seconds:

```text
cadical -t 60 --lrat --no-binary --checkproof=3 \
  F7_t2.simp.cnf simp.lrat
```

It again returned `UNKNOWN`, after 1,118,686 conflicts, 2,144,077 decisions,
and 181,357,969 propagations.  The unfinished LRAT stream was already 456 MiB.
For reference, an equal-budget stock run on the original parent also returned
`UNKNOWN`.

## Certificate boundary

An UNSAT result from one uninterrupted native-LRAT CaDiCaL run is already
covered by the repository's `run_h7_cadical_lrat.py` plus independent
`lrat-check` path.  A standalone UNSAT proof of the emitted residual is not by
itself a certificate of the original CNF: the preprocessing derivation and
residual proof would have to be composed or replayed in one proof-aware run.
No result from this audit is entered into the 43-parent manifest.

## Verdict

**Cut.**  Preprocessing removes most variables and clauses on paper, but a
fresh proof-producing solve of the residual does not change the 60-second
verdict and generates proof data faster than the original run.  CaDiCaL's
ordinary inprocessing already exploits the same transformations; exporting
and restarting them is not a new H7 proof mechanism.  Do not repeat this over
the remaining parents or turn it into a preprocessing fleet.  Reconsider only
if a genuinely different certified preprocessor supplies parity/cardinality
reasoning that CaDiCaL itself lacks.
