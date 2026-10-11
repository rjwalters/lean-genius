# Numerical audit: erdos85-drop.11

Auditor: codex, AI author. This is a delta audit against frozen v10 with retained, explicitly identified evidence for unchanged claims. No new Lean build, certificate replay or cloud campaign was run. Fresh work includes the v11 rebuild/link/gate checks and comparison of every edited sentence. During this finalization session codex independently summed all 13,094 H7 raw result files, reran the collector, checked the source closure and read raw axiom logs; these are retained checks, not repeated here.

| Text claim | Source | Source value | Match | Notes |
|---|---|---|---|---|
| One case refuted; four remaining strata | H9 exclusion and case-split Lean declarations; §2.2 | h in {1,3,5,7,9}, with 9 excluded | yes | Fixes v10 abstract wording. |
| H7: 28 covers, 377,776 leaves at depth 3 | `h7_hsb_campaign_20261008/receipts/collected/summary.json` and Lean interface | 28, 377776; depth is a theorem parameter | yes | v11 explicitly states depth 3. |
| All 377,804 formulas refuted, one leaf by split | Same summary and split manifest | 28 + 377776; 377775 ordinary leaves + 256 sub-leaves + 1 sub-cover | yes | Parent count is distinct from directly checked split-formula count. |
| 232 leaves retried, 233 timeout attempts; 2 h/12 h caps | Campaign README, manifests and `campaign_totals.json` | 232 initial timeouts, one repeated timeout | yes | Counts attempts, not 233 distinct leaves. |
| Selected leaves/split: 4,269 / 706 CPU-h; ~20.2 TB | Collector summary | 4268.71 / 705.74 h; 20210589568747 bytes | yes | Whole-hour rounding; see rounding-order note below. |
| Every run: 4,711 / 740 CPU-h | Campaign totals and `.10.independent/independent-totals.json` | 4711.11 / 740.44 h; 378293 runs | yes | Includes covers and superseded attempts. |
| No H7 dollar claim | v10→v11 source diff | Deleted | yes | Resolves C2; no billing total asserted. |
| H7 base: 17,633 variables, 720,825 clauses | Campaign README / emitted header evidence | 17633 / 720825 | yes | Retained v10 source check. |
| 43 classes; 15 counting cases; 28 structural cases | Counting-core Lean source and campaign | 43 = 15 + 28 | yes | Retained v10 check. |
| H3 408 searches = 24 + 384; 411 axioms | H3 integration raw axiom evidence | 3 standard + 408 native | yes | No source change. |
| H5 40 searches + 18 cover/cardinality checks | `h5_terminal_review_20261008/terminal-evidence1/job.log:2041`, AUDIT.json and graph-axioms.json | 61 unique axioms = 3 standard + 58 native | yes | Raw printed list parsed during finalization; 40 native names in H5 search namespace, 18 other native checks. |
| H7 reduction 3 standard + 91 native | `h7_hsb_capstone_review_20261008/stratum.log` and audit.json | 94 total | yes | Newly linked. Split-composition lemma axiom count remains unasserted; its raw producing log was unavailable locally. |
| 13 unpublished H7 packed files, ~2.57 GB | Thread refs `CAPSTONE_ABSOLUTE_PATH_AUDIT_20261011.json` | 13 reads, 2574916357 bytes, SHA256 for all 13 | yes | Scan covered 893 hash-verified sources; no other absolute string paths. Current availability/hashes are not historical replay evidence. |
| 891 accepted dependencies; no full cold rebuild | `release_assembly_20261011` manifest and receipts | 891 imports + H3 wrapper + finite endpoint = 893 sources | yes | Lean sources and release evidence unchanged from audited 98ee2fc33428 to final artifact pin. |
| Upper side 601; corollaries 607/604 axioms | Accepted release axiom logs | 3+598; 3+604; 3+601; no sorryAx | yes | Receipt-based, not a fresh Lean invocation. |
| H1 13,351 formulas and ~28 TB | v10 numerical audit and original per-orbit receipts | 12094 + 1160 + 96 + 1; about 28.35 TB | yes | Unchanged; v10 re-summed the underlying rows. |
| H1 table sizes/timings, 36 hardest-orbit leaves | v10 numerical audit, H1 bank/census/historical/pilot receipts | Bank 22.554 TB; census 5.6406 TB; historical .1035 TB; pilot .04707 TB | yes | Prior row-level verification retained, not repeated. |
| r(41)=49; r(42) in {49,50} | Boza v2 p.4 table and monotonicity | As stated | yes | Table visually checked during finalization. |
| r(109) in {120,121}; r(155) in {168,169} | Zhang primary abstract + Boza Corollaries 3/7 | As stated | yes | Algebraic combination of cited bounds; full Zhang proof not read. |
| Abstract <1900 characters | Fresh rebuilt PDF text, normalized whitespace | 1706 by this extraction | yes | Author reports 1704 with a different normalization; both safely satisfy limit. |
| 14 pages, references start p.12 | Shipped/rebuilt PDF | 14; main text 11 pages | yes | Approximately-ten-page target remains a nonblocking editorial deviation. |

**Rounding-order correction to v10's audit.** `collect_receipts.py` rounds each cube's CPU hours to two decimal places before adding 28 cube totals. `campaign_totals.py` adds raw seconds before rounding kind/status totals. Thus displayed leaf/split values 4264.81 + 3.89 = 4268.70 and 705.12 + .60 = 705.72 do not exactly equal collector totals 4268.71 and 705.74. Both round to the paper's 4269 and 706. Bytes sum exactly. This is not a manuscript numerical discrepancy.

Remaining unchanged values (lower witnesses, H1 inventory/encoding counts, historical H1 dollar estimate, resource/determinism data, f(15)=f(16)=5, and Cayley counts) retain the v8/v9/v10 numerical audits' source checks. This audit does not upgrade those checks into fresh experimental verification. No includegraphics or external TeX children occur; no stale figures are possible.

**Numerical mismatches: 0. Newly untraced numerical claims: 0.**
