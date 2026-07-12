# Batch 2/3/4/5 verification state (updated batch 5, 2026-07-12)

## BATCH 5 NUMBERS (final Mechanic batch)

- Wave T (zero-edit re-verify of the 333 transitive-dep-failed inventory files; 72 already
  GREEN in ledger were skipped → 261 targets): results in `results-T1/T2.txt`, merged.
- Wave S (singleton unknown-const renames, 68 files edited + NapoleonsTheoremOQ02 = 69
  targets): results in `results-S1/S2.txt`.
- 24 never-compiled files (single-letter free vars in def bodies) reclassified
  `PRE-EXISTING` / `never-compiled:*` in the ledger — excluded from migration counts.
- Merge command (idempotent, safe to re-run):

```
cd proofs/batch2 && python3 merge_results.py \
  --results results-T1.txt results-T2.txt results-S1.txt results-S2.txt \
  --diag diag-T1.txt diag-T2.txt diag-S1.txt diag-S2.txt
```

Final totals: see the close-out comment on #38064 and the seeding comment on #38065.

## Backlog → Doctor (#38065)

1. Residual classes (ledger `verify-results.tsv`, RESIDUAL rows): instance-synth,
   type-mismatch, proof-drift, parse survivors, remaining unknown-const singletons
   (true removals: `Nat.nth_prime_*`, `Complex.abs_cpow_mul_exp_log_re`, PartENat
   in ChebyshevPNTBridgeOQ01, project-local missing names).
2. AbelRuffini remaining: OQ10 (native_decide×noncomputable catch-22), OQ04OQ01
   (3 deep drift sites), InverseGalois (module name `InverseGalois`),
   LagrangeTheoremOQ01OQ01OQ01ApproachB (unitToAddAut arg rename + instance-synth).
3. Never-compiled files (PRE-EXISTING rows): route to a separate rewrite/cleanup issue,
   not #38065 — they never compiled on v4.26 either.

## Verification recipe (unchanged)

docker run --rm --memory 8g \
  -v "<worktree>:/workspace" \
  -v lean-mathlib-packages-v431:/workspace/proofs/.lake/packages \
  -v lean-mathlib-cache-v431:/workspace/proofs/.lake/build \
  -w /workspace/proofs lean4-arm64:v4.31.0 \
  bash batch2/runner2.sh batch2/targets-X.txt batch2/results-X.txt batch2/diag-X.txt

≤2 containers concurrently. NEVER lake build on the host.
All edits are applied ONLY to files already FAIL in proofs/spike-logs-full/results-full.tsv,
so no previously-passing file can have regressed.
