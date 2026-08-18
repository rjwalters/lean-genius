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
All nine proof artifacts are stored durably at
`/Volumes/Stripe/lean-genius/artifacts/erdos85-cayley-sidon/mu3grid/certificates/`.

The standard streaming compaction, binary encoder, and reproducible LZ4/7-bit
packing pipeline was also run on every LRAT:

| shape | actions | compact SHA-256 | binary SHA-256 | packed LZ4 SHA-256 |
|---|---:|---|---|---|
| C16 | 20,988 | `98c798df84b90a1927e9fcaf44915e344eeb3be7cb1d8a74f000d47b7c6b782c` | `13d2df2ada3e560b6510b9275ca7e8ee438d22b837fee0df98afa1f31425ae79` | `cd3f7101eac96d5a9fe223816e01d6bbd1889e5c046127803dab7cf1a636c7ad` |
| C10+C6 | 47,131 | `9a36f144b1e35bf13206289513221c4cc7d333ba0f27c6e42162db3a628adf23` | `cb711689af85b0ff8f41b9a960059ea1ffbbb143ca1293c2b8ae9f2c473b9553` | `d98eeb3c40828db936d0485a33bf8660857cdae066b621b8438e8fa097c66a8c` |
| C8+C8 | 31,338 | `9ffbca29db873910522bf5142bc3d777193ff037c725a911281eda2e400b852f` | `1fd0b68527892d63f73f3cb41118a07479a63b8748c61e71d6583a11d9beb475` | `da7c39348727008d4f4d8c2faa4a565c196ec5aed0f7ced02ee121f232a7b1ad` |

The final packed files are approximately 518 KiB, 1.1 MiB, and 652 KiB,
respectively. They live beside the raw proof triplets in the artifact folder.

Together these certificates cover the complete all-triangle-free sector. The
all-triangle mixed models remain unresolved and must not be claimed as covered
by these hashes.
