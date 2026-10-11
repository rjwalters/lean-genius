# H7 cost sample: independent receipt and arithmetic review

**Receipt identity and point-estimate arithmetic pass. The recorded bootstrap
interval is not reproduced under the committed estimator's default settings.**
`AUDIT.json` reports these components separately; it is not an unconditional
pass of the complete forecast or evidence for full campaign completion.

Reviewed H7 commit: `f995bd5f7a417dce8d7ea8d6e694b31f95120e45`.
The independent audit ran on the existing builder, job
`20261008T084139-erdos85__h3-triple-formal-20261007-348672`, at
`9a1995108b9c0ac7edc658f5be19fef545c03902`, and exited zero with status
`COST_SAMPLE_AUDIT_WITH_REPRODUCIBILITY_FINDING`. It did not run a solver,
checker, Lean build or new fleet.

## Verified sample

The 1,428 distinct primary receipts comprise all 28 covers and exactly 50
sampled leaves per cube. Independent reconstruction of the deterministic
selection with seed 20261008 matches every sampled leaf and sample index.

- All 28 covers and 1,398 leaves have consistent recorded UNSAT/verified
  markers, solver/checker return codes and approved binary hashes.
- Two leaves timed out: `cube_F7_t6:119` and `cube_F7_t0:2061`. Neither has
  an UNSAT or verified marker. Neither is counted as certified.
- Every sampled CNF hash and byte count was independently reconstructed
  from the pinned canonical body, mask units, hsb clauses and cover bytes.
  Each leaf's positive units match its exact blocking clause in line order.
- The reviewed input manifest is
  `f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c`.
  The recorded total campaign size remains 377,776 leaves plus 28 covers.
- The primary sampler job `20261008T050835-commit-50a06c7c033a-210080`
  has authoritative exit zero. Its raw receipts, log, spec and exit are
  retained here. The helper is retained as a snapshot of 146 duplicate
  receipts; this review does not claim terminal success of the helper job.

Proof streams were checked and discarded by the producer. This review checks
receipt identity and internal consistency, not those discarded streams again.
It neither admits external UNSAT evidence into Lean nor completes the campaign.

## Archival transformation

The committed sample equals the primary receipts under exactly this verified
transformation: add `sampler=main`; add `duplicate_runs_same_proof=1` for the
146 items whose helper CNF/proof hashes match; keep only the last 1,500
characters of each timeout diagnostic value. Both original solver tails have
4,000 characters and both checker diagnostics have 43 characters. No solver,
checker, timing, formula, proof or status field changes. The original records
are retained without truncation in `raw-primary.jsonl` and
`raw-helper-snapshot.jsonl`.

The first audit (`344998`, exit 1) assumed only the sampler label had been
added. Its source and raw failure evidence remain in `first-failure/`.
The revised audit explicitly verifies the actual archival transformation.

## Forecast arithmetic and unresolved reproduction

| Quantity | Independently calculated |
|---|---:|
| Stratified main-pass solver + checker CPU-hours | 3,855.8494 |
| Expected capped leaves under the sampled proportions | 719.88 |
| CPU-hours already counted for capped leaves | 766.2861 |
| Estimated streamed proof volume | 20.1323 TB |
| Cost at the stated $0.0147/vCPU-hour and 85% utilisation assumptions | $66.68 |

These reproduce the published point figures after rounding. The cost row is
conditional arithmetic; current prices, utilisation and final spend were not
verified here. The capped cases are censored observations, so this is not a
complete-run cost estimate.

The independent 5,000-replicate stratified bootstrap, with `random.Random(1)`
and the committed sample order, gives rounded 5%–95% endpoints **2,867–5,208**
CPU-hours. `estimate.json` instead records **2,864–5,216**. The second audit
(`346714`, exit 1) stopped at that comparison; its source and raw evidence are
in `second-failure/`. The final report preserves the mismatch explicitly and
does not accept the recorded interval as reproduced. The original generation
command, replicate count and sample ordering were requested from the owner.
Small Monte Carlo differences may explain it, but that is not established.

The empirical bootstrap is not a completion-time bound and cannot observe
the uncensored costs of the two timeout leaves. A Hill estimate from this
finite, censored sample does not establish infinite population variance.

## Related runbook findings sent to the owner

The proposed canary limit has a reservation race; see
`../h7_canary_limit_review_20261008/` for its reproduced failure and tested
patch. Separately, the full manifest starts with all 28 cover rows, so an
eight-batch canary would exercise only covers, not the advertised roughly
500 leaves. A pinned mixed cover/leaf canary manifest is needed to test both
paths. If a watcher completes such a restricted manifest, its `stop()` writes
persistent `control/STOP`; the transition to the full pass must handle that
explicitly without silently clearing an alarm or budget stop. The current
bounded-node canary against the full manifest does not make `watch` complete
automatically. These operational findings remain for integration and review.

`SOURCE.json` pins the reviewed files. `audit-job.*` retains the final audit
execution. Five local mutation tests exercise identity, process/binary pins,
timeout promotion and the exact archival transform without solver or Lean work.
