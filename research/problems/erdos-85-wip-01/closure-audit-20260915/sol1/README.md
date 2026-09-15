# Erdős 85 re-entry audit — 2026-09-15

The full eventual-monotonicity problem remains unresolved. The integration source `Erdos85BinarySquareRegularCapstone.lean` proves the negation **assuming** `BinarySquareRegularExclusion`; that proposition quantifies over every k >= 3. A finite drop or a Cayley census does not supply it. Main has outline v2.2; integration has v2.69.3 and later Phase A amendments.

## Verified this session

- Positive-control review 2649 resolved: all 16,348 clauses, exact terminal input/log pins, 48 vertices of degree 7, all 1,128 vertex-pair common-neighbor tests, and standalone coordinate construction pass. Receipt: ../control-reviews/review-2649-20260915.json.
- Frozen Phase B index: four source hashes and all 1,416 unique source-index/ID/CNF-hash joins pass. H1 1,257; H3 2; H5 129; H7 28. This is the historical inventory, not a current unresolved count. See frozen-index-audit.json.
- Saved H5 T0/T1 mappings each join to exactly their 43 frozen IDs and hashes. See h5-mapping-join.json. This rechecks joins, not exclusion proofs.

## Current evidence boundary

The amended Q7_SQUEEZE_20260910.md and q7_h5_closure_ledger/results.json record H3 and all H5 excluded at paper plus independently checked finite-computation level. H5 still has three undischarged Lean Boolean-exclusion premises. The finite-drop theorem in Erdos85OrderFortyNineSmallHighDropFrontier.lean still accepts H1, H3, H5 and H7 proof inputs; its existence does not establish their completion.

H7 has recorded exclusions at a=8,9 and selected a=6,7 shapes. Its remaining frontier includes capped and unvisited work, not completed negative evidence. Historical H1 overlays and structural exclusions must retain their own evidence categories. Neither the original 1,416 target count nor a subtraction of paper exclusions is a current all-UNSAT verdict table.

## Next work and coordination

Claude is packaging the completed Cayley census with portable evidence; sol2 is verifying stronger primary-source bounds for r(109), r(155). For finite-drop work, prioritize existing H1/H7 incomplete coverage and exact formal closure dependencies. The saved Phase B inventory is launch_ready=false; current board40 keeps Phase B gated. No solver, proof replay, or paid compute was launched in this audit. Capped jobs were not resumed.

The general A-REG mechanism remains the missing infinite-family step. Keep it explicit in any progress report; closing the finite drop alone will not solve Erdős 85.
