# Batch 2/3/4 verification state (updated batch 4, 2026-07-12)

## BATCH 4 NUMBERS (waves F/G merged; wave H = bad-import repair, results in results-H1/H2)
- verify-results.tsv: 658 tracked files — 190 GREEN / 468 RESIDUAL (before wave H merge)
- Wave F 159 (repo-wide orphan-doc sweep 129 + double-binder 4 + autoImplicit 11 + import-Mathlib 16): 47 green
- Wave G 8 (AbelRuffini): 2 green (OQ03, OQ03OQ01 via Nat.card retype)
- Wave H 298 COMPLETE: 74 green (38 H1 + 36 H2, 25%); MERGED into tsv: 928 tracked, 264 GREEN.
- fails-D.txt (134) DIAGNOSED: diag-D1/D2.txt, classes merged into tsv. Mostly Doctor-class
  (instance-synth 27, proof-drift 25, type-mismatch 19, parse 9, singleton drift ~30).

## Key batch-4 discoveries (details in rename map §6 batch-4)

1. **BAD-IMPORT CLASS**: 294 not-yet-green files import Mathlib modules removed in v4.31
   (BigOperators.Group.Finset, Data.Rat.Basic, Order.Filter.AtTopBot, Data.Set.Finite, ...).
   Repaired wave H: bad imports dropped + umbrella `import Mathlib` prepended.
   Module list: `docker run --rm -v lean-mathlib-packages-v431:/pkgs alpine sh -c "cd /pkgs/mathlib && find Mathlib -name '*.lean'"`
2. **NEVER-COMPILED CLASS**: single-letter unknown-identifier files (ι/n/p/k/A/B/X/V) have free
   vars in def BODIES — `set_option autoImplicit true` does NOT fix (0/11). Landed unverified
   in ENOSPC eras; never compiled on v4.26. Doctor/out-of-scope tier.
3. Nat.card migration (alternatingGroup lemmas), Fintype.ofFinite for subgroup/quotient,
   convert→convert! Archive drift — see map.

## Backlog for batch 5

1. Merge wave-H results if not merged (command above); fix its near-misses — files whose only
   remaining error is a shallow rename now that imports resolve.
2. AbelRuffini remaining: OQ05+OQ10 (layer-3 check pending in wave H), OQ04OQ01 (3 deep drift
   sites), InverseGalois (re-target module name `InverseGalois`, NOT AbelRuffiniInverseGalois),
   LagrangeTheoremOQ01OQ01OQ01ApproachB (unitToAddAut arg rename + instance-synth — Doctor).
3. Residual-class work is now predominantly Doctor-tier: instance-synth 110, type-mismatch 48,
   proof-drift 43, unclassified 44 → hand off to #38065 unless wave H unmasks new mechanical
   classes.

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
