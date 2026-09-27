# Erdős 85 — pause handoff (2026-09-27)

Written for whoever reopens this work after a pause of months. Board goals #42–#47.
Operator: Robb. Authors of record: Claude Fable and GPT Sol (goal #45 ruling). Everything
below points at receipts; nothing here is a claim in its own right.

## 1. What is proved (Lean 4.31.0, repository-pinned Mathlib)

| Statement | Lean name | Axioms |
|---|---|---|
| Theorem B: A-REG ⇒ ¬ Erdős 85 | `Erdos85.not_erdos85Question_of_binarySquareRegularExclusion` (`Proofs/Erdos85BinarySquareRegularCapstone.lean`) | propext, Classical.choice, Quot.sound |
| f(48) ≥ 8, f(49) ≥ 7 (explicit witnesses) | `Erdos85.minDegreeForC4_fortyEight_eq_eight_checked`, `Erdos85.seven_le_minDegreeForC4_fortyNine_checked` (`Proofs/Erdos85FiniteDropWitnesses.lean`) | standard three plus six `native_decide` axioms |
| Conditional finite drop | `Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_checked`, `…_fortyNine_lt_fortyEight_checked` | as above; take `hno49 : ¬ C4FreeMinDegreeWitness 49 7` as hypothesis |

Literal `#print axioms` output: preliminary overlay audit `AXIOM_AUDIT_OVERLAY_20260916.md`; cold
rebuild `AXIOM_AUDIT_COLD_20260927/` (fresh build volume, pinned image `sha256:a5ca6c4e…`).

## 2. What is computational (Result A)

The one unproved hypothesis, `hno49`, splits into strata H1, H3, H5, H7 (the split is the Lean
consumer's interface). H3, H5, H7: closed by written arguments plus reviewed computation
(`H7_CLOSURE_20260915.md`, `PHASE_B_H5_H7_INVENTORY_20260910.md`). H1: 1,257 SAT instances,
96 with drat-trim-verified certificates (2026-08 overlay) and **1,161 residual roots all UNSAT under
two solvers** (1,160 whole-instance, 1 by a 36-leaf cube partition), receipts in
`phase_b_h1_census_20260927/` (read `CENSUS.md` first). The capacity-grid framing (1,288 gap
slots) additionally needs the 34 outside-frozen slots (`phase_b_h1_gap130/`, run 2026-09-27).

Trust boundary, in order of weight: (1) encoding fidelity — the H1 emitter is the Lean program
`Proofs/Erdos85OneHighV2CnfEmit.lean` compiled to the native `v2cnf` (sha256 `4bd9604c…`), with a
check mode and historical hash identity, but the CNF-to-graph semantic bridge is instantiated in
Lean only for H3/H5, not yet H1; (2) verdict-only solving (no certificates); (3) the H7 Lean
capstone `orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors` is uninstantiated.

## 3. What is open

- A-REG (`BinarySquareRegularExclusion`) is a live hypothesis, not a conjecture we endorse; the
  operator's plane-order reading is the rival. The negative map (cuts ledger rows 1–186,
  `CUTS_LEDGER_DRAFT.md`, `FINAL_PROOF_OUTLINE.md`) records every failed route. Do not re-run a
  ledger row without new mathematics.
- Certificates and Lean bridges for Result A: priced in the manuscript's cost-to-verify section;
  the cube-partitioned route is the cheaper idea (projection, not built).
- Parked: q = 8 / order-64 probes of any kind (board #30); exact-extremal route (cut 2026-09-08).

## 4. Where everything lives

| Artifact | Location |
|---|---|
| Branch of record | `erdos85/integration` (tag `erdos85-pause-2026-09` once cut); `main` receives paper, outline, handoff, punchlist, small Lean core only |
| Manuscript | `manuscript/DRAFT.md`, `manuscript/ERDOSPROBLEMS_POST_DRAFT.md`, `manuscript/FIRST_DROP_LITERATURE_CHECK.md` |
| Punchlist | `WRAPUP_PUNCHLIST_20260921.md` |
| Census receipts (small) | `phase_b_h1_census_20260927/` |
| Census logs, CNF snapshots, run dirs (large) | Stripe `artifacts/erdos85-sat49/h1-verdict-cloud-20260921/{,pass2,pass3,pass3b}/`, `h1-cube-pass4-20260926/`, `h1-gap34-20260927/`; checksum manifest `artifacts/erdos85-sat49-MANIFEST-20260927.sha256` |
| Cloud tooling | `phase_b_h1_verdict_cloud_20260921/` (README; controller, node scripts, cube tools) |
| Certificate bank (6 TB gz) | `s3://2am-erdos85-certs/sat49/campaign-20260825/`; working prefix `sat49/verdict-only-20260921/` (deletable after the manifest) |
| Board / room | squad room `.squad/squad.db`; goals #15, #23, #37, #38, #41–#47 |

## 5. How to resume

1. `git fetch && git checkout erdos85/integration`; read `CENSUS.md`, then this file, then the punchlist.
2. Lean: `./proofs/scripts/docker-build.sh Proofs.Erdos85FiniteDropWitnesses` (never `lake build` on the host).
3. Solvers: Kissat 4.0.4 and CaDiCaL 3.0.1 at `/opt/homebrew/bin`; cloud recipe in the cloud README (pinned image, emitter, S3 claim protocol, launch-template gotchas).
4. To extend the census: `sat49/dispatch_verdict_only.py --case-id …` with a banked config; cube tools for rows that defeat every cap.

## 6. What not to retry

Spot instances for rows longer than a few hours (six reclaims in this campaign); fixed-depth cube
splits on top-occurrence variables (27/32 trivial cubes, uninformative); solver caps above 86,400 s
without changing the reviewed dispatcher; any A-REG route already in the cuts ledger.
