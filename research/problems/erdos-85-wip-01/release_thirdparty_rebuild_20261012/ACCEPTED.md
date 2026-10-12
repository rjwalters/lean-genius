# Third-party-path cold rebuild: ACCEPTED (2026-10-12)

- Job: `20261012T143935-commit-47e1755cb9e2-6732`; execution commit
  `47e1755cb9e21389348d78fe7c07ad60bd41cab3`; plan SHA256
  `1eee4968a7a37adaa64e05058c4908bdbfa7a0c4192aa8dd4d9f63c9e2f61ce0` (see `THIRDPARTY.md`).
- Inputs: a fresh host worktree with no `proofs/Proofs/Certificates/strata-lrat/` directory;
  `proofs/scripts/fetch-h7-certificates.sh` run by the builder as
  `assumed-role/Erdos85LeanBuilder` fetched all 13 packed certificates (Requester Pays)
  in 16.6 s, each `OK` against the committed manifest
  (`evidence/fetch-job/`, job `20261012T143725-commit-47e1755cb9e2-4815`, exit 0).
  The runner then rehashed all 32 inputs against the plan (read-only preflight
  `20261012T143905-commit-47e1755cb9e2-5944`, then execution).
- Fresh empty volume `lean-build-e85-thirdparty-20261012`. Start 14:39:35 UTC; exit 0;
  elapsed 13,114 s; 893/893 modules compiled from source.
- Capture: `COLD_PROJECT_BUILD_ACCEPTED`; audit `COLD_PROJECT_BUILD_AUDIT_PASS`,
  893 sources, endpoint axiom lists exactly the accepted 601/607/604;
  RUN.json sha256 `6010394fdd4257ea9168990d9954c6a78854965c951205d52c2429ddda097379`.
- Archive (not in Git): `/Volumes/Stripe/lean-genius/artifacts/erdos85-cold-build-thirdparty-20261012/run-output.tar.gz`,
  2,389,489,668 bytes, sha256 `0b6491bda21337ae6eae21def3a279d4621819a5291b27a3578ef1228b23b1e9`;
  per-file hashes in `evidence/full-bundle-manifest.json` (2,692 files).
- Reproducibility: all 893 compiled `.olean` objects are byte-identical (same SHA256) to
  those of the accepted attempt-2 cold build, and all 893 axiom exports match
  (`evidence/reproducibility-vs-attempt2.json`).

Scope unchanged: fresh project closure over pinned Lean/Mathlib package caches; no
external SAT replay (H1 and H7 t=0 remain cake_lpr-checked hypotheses). Limitation:
the fetch ran under the bucket-owner account (221082181346); access from a separate
AWS account is still untested.
