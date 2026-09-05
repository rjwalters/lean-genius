# `[5,3]` induced-C5 CNF audit

Status: 78 reviewed carrier orbits encoded and independently reviewed;
uniform short Kissat triage is **UNKNOWN** on every orbit.

`cnf_nonbip_mixed_53_c5_carrier.py` reuses the reviewed full-graph core from
the displayed-triangle CNF and imposes, for one of the 78 dihedral carrier
representatives:

* the five edges and five chords of vertices `0..4` as an induced defect C5;
* the five ambient cycle-edge bits `h`;
* five size-three exterior fibers, consecutive-disjoint, with a distinct
  doubled exterior label exactly at each active chord-intersection bit `r`.

All other internal neighborhoods remain free.  The canonical exterior labels
are safe because no carrier label can occur in three fibers (that would hit a
consecutive pair), and two distinct chord intersections cannot share a label
for the same reason.  Review #1377 independently confirmed the reduction and
verifier.

The representative list reproduces 573 labeled forms, 78 dihedral orbits,
and serialized representative SHA
`82ae3fed44176ee0d14e513cc3ff7fb976d72d24f777b437aa793eedb56f733e`.
The shared-core refactor leaves both previously reviewed triangle CNFs
byte-identical.

Manifest mode emitted and hashed every C5 instance in memory:

```text
orbits             78
variables          313600 (every orbit)
clauses            997575 (every orbit)
byte range         17500525..17500530
manifest SHA-256   96361eb74e3a7995f40fa6369912b77725ba547505403cfc3247b0249efa177e
elapsed            68.984 seconds
```

For the first solver triage, four local workers each used Kissat 4.0.4 with
the identical `--time=3` bound, deleting its temporary CNF after the run.
All 78 cases returned exit code zero and `s UNKNOWN`.  The complete exact
table is `c5_kissat_triage_3s.tsv` (79 lines including its header, SHA-256
`e83aa893b146c6b25fad042fa1dea119ffad13505b1cfaa04f3bc3a65be322e4`);
its conflict/decision/propagation columns
are scheduling diagnostics only, not logical evidence or a sound total
hardness ordering.  Orbit 0 was separately rerun at ten seconds and remained
`UNKNOWN` after 30613 conflicts and 303302111 propagations.

No SAT model or UNSAT certificate exists from these runs.  The next bounded
choice is either to deepen selected strata uniformly or first add sound
owner/Gram propagation.  The latter is preferable if the new consequences
can be expressed without importing assumptions absent from the `[5,3]`
displayed-C5 interface.
