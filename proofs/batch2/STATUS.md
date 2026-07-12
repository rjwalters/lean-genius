# Batch 2 verification state (2026-07-12)

- results-A.txt: bigop-root wave COMPLETE (25 targets: 4 PASS / 21 FAIL, residuals in diag-A.txt)
- results-B.txt: doc-comment-root wave PARTIAL (44 of 200 targets checked: 4 PASS / 40 FAIL;
  container stopped at batch wrap — remaining 156 of targets-B.txt plus all 230 of
  targets-C.txt unverified)
- targets-D.txt: NOT RUN (164 targets: import-fix files, exists-binder roots, rename roots)
- All edits were applied ONLY to files already FAIL in proofs/spike-logs-full/results-full.tsv,
  so no previously-passing file can have regressed.
- Verification recipe: docker run with lean4-arm64:v4.31.0 + -v431 volumes,
  bash batch2/runner.sh batch2/targets-X.txt batch2/results-X.txt
