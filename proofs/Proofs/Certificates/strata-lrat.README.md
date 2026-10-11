# H7 (t >= 1) packed LRAT certificates

The thirteen modules `Erdos85OrderFortyNineSevenHighT{1..7}Rep*Certificate.lean` read their certificate with
`include_str "Certificates/strata-lrat/h7_tN_repK.packed.lz4p7"`. The files are too large for Git (2,574,916,357
bytes; the largest is 1.61 GB) and are published in the Requester Pays bucket
`s3://2am-erdos85-certs/public/erdos85-h7-positive-triple-lrat/`. Run `proofs/scripts/fetch-h7-certificates.sh`
before building; it verifies every file against `strata-lrat.MANIFEST.sha256` (these hashes also equal the
`packed_lz4_sha256` recorded in each module's header comment).

## Download prerequisites

From the repository root, with the AWS CLI installed and an authenticated
profile permitted to make Requester Pays S3 requests:

```sh
AWS_PROFILE=your-profile proofs/scripts/fetch-h7-certificates.sh
```

The script supplies `--request-payer requester`. Request and transfer
charges may apply; anonymous HTTP downloads are unavailable. Allow space
for 2,574,916,357 bytes of packed inputs as well as compiler outputs.
Already-present files with the correct hash are reused; every file is
checked against [the SHA256 manifest](strata-lrat.MANIFEST.sha256).

[The retained download check](../../../research/problems/erdos-85-wip-01/release_cold_build_20261011/public-fetch-local.log)
verified all thirteen files using bucket-owner credentials. Access from a
separate AWS account has not been tested. The
[cold-build procedure and current status](../../../research/problems/erdos-85-wip-01/release_cold_build_20261011/README.md)
describe compilation and the separate terminal audit; a successful download
is not a completed build.
