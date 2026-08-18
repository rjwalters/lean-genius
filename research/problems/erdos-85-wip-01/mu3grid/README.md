# Order-64 `mu = 3` exterior-grid certificates

`generate_alltf_cnf.py` deterministically generates the exact row/column-hit
and C4-free CNF for either all-triangle-free internal two-factor shape.

The C16 instance was audited on 2026-08-18 with Z3 4.15.4, Kissat 4.0.4, and
`drat-trim` from the repository's `erdos85-sat49` artifact toolchain:

```text
p cnf 76656 1342448
CNF  cb40a87a44d62313ffb8c8d5dfa16a845eda0eef96528d351fc01a7ef15c0a77
DRAT 25590ee8b5b64c540156e42a326cb5162c56d5a0c384beb0f6533a210c31c260
LRAT 24e5d616d292d5f2b80d1b26130f41d7bf116bd25127466c6eb019d479f29bbc
```

Kissat returned `UNSATISFIABLE`. Independent conversion/checking with

```sh
drat-trim mu3-c16.cnf mu3-c16.drat -L mu3-c16.lrat
```

returned `s VERIFIED`. The backward core contains 8,631 of 1,342,448 source
clauses and 12,124 of 857,435 lemmas, using 127,206 resolution steps. The raw
LRAT is about 11 MiB (20,989 lines), suitable for the existing compact/binary
Lean LRAT pipeline.

This certificate covers the all-triangle-free C16 sector only. C8+C8 is also
experimentally UNSAT and can use the same pipeline. The all-triangle mixed
models remain unresolved and must not be claimed as covered by these hashes.
