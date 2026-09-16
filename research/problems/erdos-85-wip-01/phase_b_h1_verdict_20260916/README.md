# H1 residual verdict-only host queue

Goal #42, 2026-09-16. This is a **zero-cloud-spend** host dispatch configuration for the 1,161 fresh Phase B H1 roots. It makes no certificate or Lean replay claim. The frozen combined index remains 1,416 cases: H1 1,257, H3 2, H5 129, H7 28. The reviewed historical overlay accounts for 96 H1 cases. The wrapper requires the exact H1-only complement `1,257 − 96 = 1,161`; its sorted selected-ID SHA-256 is `8c741b733a27ab75b49bc07e2a5ed7c42658c22ded2c4753a106fb93f5a7adb8` and its historical-ID SHA-256 is `04097bb4dec4c381ed614d17937a2d011127ffa6debb1db79f2de85a4cad64f3` (each ID followed by newline). A changed count, ID set, tool hash, index, historical overlay or source manifest fails before input generation.

`config.draft.json` requires independent Kissat and CaDiCaL UNSAT verdicts for each selected row, each with a 14,400-second cap. A primary UNKNOWN does not launch CaDiCaL and remains open. A CaDiCaL UNKNOWN after primary UNSAT also remains open. SAT candidates, solver disagreement, input errors and dependency drift stop new submissions and retain their receipts. The proof-logging flag is false. Existing all-sector configs retain their previous behavior and their four-worker maximum.

`pilot-24.json` pins 24 distinct residual IDs, stratified across the five profiles (5/5/5/5/4) and spread across source-index ranks. It is a scheduling sample, not a claim of random hardness sampling. The pilot runs with four concurrent workers while measuring total host RSS, swap, Docker memory, disk use and elapsed time. The reviewed v1 dispatcher caps concurrency at four. Any later increase toward 24 simultaneous workers needs a separate reviewed scaling revision and measured headroom; the H1 input container allows up to 8 GiB per worker and native solvers have no memory cap. Do not launch the full queue until the pilot receipts, resource profile and H1 census/config change receive independent review.

Read-only census check from the repository root:

```sh
python3 -B research/problems/erdos-85-wip-01/sat49/dispatch_h1_residual_verdict_only.py \
  --config research/problems/erdos-85-wip-01/phase_b_h1_verdict_20260916/config.draft.json \
  --workers 4
```

The result must report `inventory_cases=1416`, `selected_cases=1161`, `historical_evidence_cases=96`. Add `--pilot research/problems/erdos-85-wip-01/phase_b_h1_verdict_20260916/pilot-24.json` for the read-only 24-case pilot selection. Execution additionally requires `--execute`, the exact pushed config commit and a new empty output directory. The wrapper and underlying dispatcher refuse unbanked or changed dependencies; the wrapper passes only the selected residual IDs. Each job writes preparation and solver receipts; UNSAT requires both solvers to agree, while a cap hit remains UNKNOWN and never enters an UNSAT total. Use distinct output directories for pilot and full queue, and use receipt-based coverage review before including any row in the manuscript.

The capacity-grid's 1,288 missing-metadata slots and these 1,161 Phase B roots are overlapping decompositions, not interchangeable row counts. The independently checked join puts **1,158 selected roots in the gap set and three selected roots on listed-object tags** (`dba11866daee2215`, `df21cf066affa6f4`, `e7c1dfc9654d954c`). The other **130 gap slots** are 96 historically verified Phase B tags lacking listed objects plus 34 tags outside the frozen Phase B set. This pilot includes none of the three listed-object tags. The 130 slots need a separate CNF/receipt route before 1,288/1,288 dual-verdict coverage can be claimed.
