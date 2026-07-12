# Batch 2/3 verification state (updated batch 3 FINAL, 2026-07-12)

## BATCH 3 FINAL NUMBERS
- verify-results.tsv: 586 tracked files — 141 GREEN / 445 RESIDUAL
- Wave D 164: 30 green | Wave B2 158: 35 green | Wave C 230: 49 green
- Wave E 25 (batch-3 fixes): 18 green | E2: Erdos13 green | E3: Erdos683 green
- Cumulative batches 1-3: ~195 verified green (55 batch-1 + 141 tsv − 1 overlap)
- The ENTIRE queued verification backlog (targets A/B/C/D) is now verified.

## Verification waves (all results merged into verify-results.tsv)

- results-A.txt: bigop-root wave COMPLETE (25 targets: 4 PASS / 21 FAIL, diag in diag-A.txt)
- results-B.txt: doc-comment-root wave, first 44 of 200 (4 PASS / 40 FAIL)
- results-D1/D2.txt: wave D COMPLETE (164 targets: import fixes + exists-binder +
  rename roots — 30 PASS / 134 FAIL, fail list in fails-D.txt, NOT yet diagnosed)
- results-B2.txt: remaining 157 doc-comment-B roots (+Erdos1Wip01) — COMPLETE/see file
- results-C.txt: 230 doc-comment-C roots — COMPLETE/see file (diag-B2.txt / diag-C.txt
  hold first-5-error diagnostics for every FAIL, captured inline by runner2.sh)
- results-E.txt: batch-3 fix re-verification (25 targets: 22 trailing-orphan doc-comment
  demotions + KummerTheorem emultiplicity + Erdos521 pi-import + Erdos683 one_lt removal)

## Running tally: proofs/batch2/verify-results.tsv (file <TAB> GREEN|RESIDUAL <TAB> class)

Regenerate/extend with: `python3 merge_results.py --results <res...> --diag <diag...>`

## Backlog for batch 4

1. fails-D.txt (134) has NO diagnostics yet — run `diagnose-fast.sh` (60s cap; classifies
   the fast-failing = mechanically fixable subset, marks slow ones TIMEOUT-60s).
2. Doctor-class residual classes tallied in verify-results.tsv column 3
   ("doctor-unclassified" = not yet diagnosed).
3. New sweepable class found in batch 3: double set-binder `∀ x y ∈ S` → split
   (see rename map §6 batch-3 discoveries). Only Erdos174Problem hit so far in diags.
4. AbelRuffini 5 residuals from batch 1 still open (hypothesis-retype recipe in #38064
   batch-1 comment); GaloisExtensionsOQ05 exists-binder fix did NOT flip it (re-FAILed
   in wave D — needs real diagnosis).

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
