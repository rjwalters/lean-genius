# Order-64 `mu = 3` exterior-grid certificates

`generate_alltf_cnf.py` deterministically generates the exact row/column-hit
and C4-free CNF for either all-triangle-free internal two-factor shape.

All three possible C4-free bipartite 2-factor shapes were audited on
2026-08-18 with Z3 4.15.4, Kissat 4.0.4, and `drat-trim` from the repository's
`erdos85-sat49` artifact toolchain. Every CNF has 76,656 variables and
1,342,448 clauses.

```text
shape   CNF sha256                                                        DRAT sha256                                                       LRAT sha256
C16     cb40a87a44d62313ffb8c8d5dfa16a845eda0eef96528d351fc01a7ef15c0a77 25590ee8b5b64c540156e42a326cb5162c56d5a0c384beb0f6533a210c31c260 24e5d616d292d5f2b80d1b26130f41d7bf116bd25127466c6eb019d479f29bbc
C10C6   00c4f14c27296158b9c0005c10415d428e8ee31eaed9f992ef5991cbc75da91d a331c906b67d9fced417bc04636e206cd85833b7fbc50049e10a83c76c0a17a3 12c8feb3ddf3d589c3a6d816ccaf95d7dabba60ba4dc055f9740697dcea0ccb9
C8C8    5289dc4823f61e1a68c48d5e22130e18bef36b473ecc2cbbf7610db37f311037 031693ad1baeb01636156df409ba0ce8d276aaeb478b57f07e5f74cdcc4a61d3 6a651f984974dcce076d3d0951d2c8542cccb51a7ca0db42963251215ce266bc
```

Kissat returned `UNSATISFIABLE`. Independent conversion/checking with

```sh
drat-trim mu3-c16.cnf mu3-c16.drat -L mu3-c16.lrat
```

returned `s VERIFIED` for every shape. The backward-core statistics are:

| shape | source clauses | lemmas | resolution steps | LRAT lines |
|---|---:|---:|---:|---:|
| C16 | 8,631 | 12,124 | 127,206 | 20,989 |
| C10+C6 | 19,118 | 27,081 | 261,994 | 47,132 |
| C8+C8 | 13,143 | 18,051 | 144,759 | 31,339 |

The raw LRATs are 11--12 MiB each, suitable for the existing compact/binary
Lean LRAT pipeline. Regenerating the C16 CNF produced a byte-identical file.

Together these certificates cover the complete all-triangle-free sector. The
all-triangle mixed models remain unresolved and must not be claimed as covered
by these hashes.
