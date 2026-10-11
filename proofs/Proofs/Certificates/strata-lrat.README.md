# H7 (t >= 1) packed LRAT certificates

The thirteen modules `Erdos85OrderFortyNineSevenHighT{1..7}Rep*Certificate.lean` read their certificate with
`include_str "Certificates/strata-lrat/h7_tN_repK.packed.lz4p7"`. The files are too large for Git (2,574,916,357
bytes; the largest is 1.61 GB) and are published in the Requester Pays bucket
`s3://2am-erdos85-certs/public/erdos85-h7-positive-triple-lrat/`. Run `proofs/scripts/fetch-h7-certificates.sh`
before building; it verifies every file against `strata-lrat.MANIFEST.sha256` (these hashes also equal the
`packed_lz4_sha256` recorded in each module's header comment).
