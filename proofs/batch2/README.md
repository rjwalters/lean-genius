# proofs/batch2/

Ledger and tooling for the Lean v4.26 → v4.31 / Mathlib migration (epic #37508,
Doctor waves #38065). `research/migration/README.md` describes the workflow that
consumed it.

| File | Role |
|------|------|
| `verify-results.tsv` | Ground-truth ledger, one row per module: `<BareModuleName>\tSTATUS\tclass` (GREEN / RESIDUAL / PRE-EXISTING) |
| `STATUS.md` | Append-only log of every Doctor batch, newest first |
| `runner.sh` … `runner5.sh` | In-container bulk verifiers (each is the previous one plus diag capture, chunking, or per-chunk logs) |
| `merge_results.py`, `reclassify.py`, `extract_diags.py`, `extract_diags_b.py` | Merge wave results and diag files into the ledger; recompute RESIDUAL classes |
| `add_open_classical.py`, `dr6_fix.py`, `dr7_natdegree.py`, `dr7_noprogress.py`, `fix_noncomputable.py`, `sweep_modifier_in.py`, `sweep_orphan_binder.py` | Mechanical repair sweeps driven by diag output |
| `diag-DR*.txt` (10 files) | First-error diagnostics kept for the waves still cited by `STATUS.md` |
| `failsD-shard-aa`, `failsD-shard-ab` | Module lists for the sharded wave-D runs |

The rest of the raw wave output (several hundred `diag-*.txt` and per-chunk logs)
was parked out of the repo on 2026-09-29 at
`/Volumes/Stripe/lean-genius/attic/retired-20260929/proofs/batch2/`.
