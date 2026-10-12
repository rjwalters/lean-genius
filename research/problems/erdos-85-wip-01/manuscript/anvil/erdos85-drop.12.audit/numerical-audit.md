# Numerical audit: erdos85-drop.12

Pinned source: `fa2b41268df024128ed4738b3bb500637cf1ec12`. All reads used `git show fa2b41268df:<path>`. `RP` = `research/problems/erdos-85-wip-01`. This audit ran no Lean build, Lean compilation, `lake` invocation or SAT replay. The table separates fresh checks made in this audit against pinned or retained bytes from values carried over from the v11 audit.

## New or changed claims in v12 (fresh checks)

| Text claim (main.tex line) | Source | Source value | Match | Notes |
|---|---|---|---|---|
| Cold rebuild of the 893-module project closure, every module compiled from source (L111, L226, L232) | `RP/release_cold_build_20261011/ACCEPTED.md`; `attempt2-evidence/RUN.json`; `CAPTURE.json` | "893/893 project modules compiled from source"; RUN.json `completed`=893, `unfinished`=0; audit `source_count` 893 | yes | Scope caveat present in text ("pinned Lean and Mathlib package caches"), matching ACCEPTED/README scope. |
| Fresh build volume (L93, L111) | ACCEPTED.md; RUN.json | "Dedicated volume ... (empty before preflight)"; `initial_project_objects` = []; isolation probe `PASS_EXPECTED_MISSING_FRESH_OBJECT` | yes | |
| Pinned Lean 4.31.0 (L93, L111, Table 2 caption) | `proofs/lean-toolchain`; RUN.json `lean_version` | `leanprover/lean4:v4.31.0`; "Lean (version 4.31.0, aarch64...)" | yes | The container image itself is not named in the evidence. "pinned Lean 4.31.0 image" is supported by the toolchain pin. |
| Upper side prints 601 axioms = 3 standard + 598 native_decide, no sorryAx (abstract, L111, Table 2) | PLAN.json `expected_exports` (bound to the accepted axiom plan); CAPTURE audit `axiom_counts` [601,607,604] | 601 total; 3 standard; 598 `native_decide`; no other axioms | yes | Counted directly from PLAN.json. |
| Corollaries print 607 and 604 (604 and 601 native_decide) (L111) | PLAN.json `expected_exports` | exact: 607 = 3 + 604; lt: 604 = 3 + 601 | yes | The differences (+6 and +3) are the `boza48Graph*` (3) and `orderFortyNineDegreeSixGraph*` (3) witness axioms, consistent with "three per-declaration axioms per witness" (L93). |
| The cold rebuild printed exactly these three axiom lists (L111) | CAPTURE.json `audit.status` | `COLD_PROJECT_BUILD_AUDIT_PASS`, axiom counts 601/607/604 "(same as the release assembly)" | yes | |
| Read-only audit checked every source hash, object hash, compile log, dependency order (L111) | `release_cold_build_20261011/README.md` §"After a terminal success" | audit.py "checks every source, certificate, raw log, compile command, dependency order, object identity and endpoint axiom set" | yes | audit.py is an author-written deterministic checker. README: "A human/peer review ... remains distinct". See flags.md M1. |
| Earlier attempt failed in the build runner before completion (L111, L280) | `FAILURE.md` | exit 1 after 460/893 modules; wrong plugin initializer name (`initialize_proofs_Proofs_...` vs `initialize_Proofs_...`) | yes | The paper does not state 460 or the cause. That is acceptable. |
| Second rebuild from a checkout without the certificate files, using the published download script; byte-identical compiled objects for all 893 modules; same axiom lists (L111) | `RP/release_thirdparty_rebuild_20261012/ACCEPTED.md`; `evidence/reproducibility-vs-attempt2.json`; `evidence/fetch-job/job.log` | fetch log: `ls ... strata-lrat: No such file or directory`, then 13 × `OK`; JSON: modules 893, identical_object_sha256 893, identical_exports 893, identical_source_sha256 893; audit 601/607/604 | yes | The JSON is a summary of counts with no per-module list. Per-file hashes are in `evidence/full-bundle-manifest.json` (2,692 files). "Second cold rebuild" means the second successful one and the third attempt overall (minor wording note). |
| Thirteen packed H7 certificate files, about 2.57 GB (L87, L280) | `proofs/Proofs/Certificates/strata-lrat.MANIFEST.sha256`; `fetch-h7-certificates.sh`; PLAN.json `artifacts` | 13 manifest lines; script header 2,574,916,357 bytes; PLAN.json byte sum of the 13 `.lz4p7` artifacts = 2,574,916,357 | yes | All 13 manifest sha256 values equal the PLAN.json artifact sha256 values (13/13). 2.57 GB is decimal. |
| Script downloads to the relative paths read by the Lean modules and verifies against the manifest (L280) | fetch script; the 13 `Erdos85OrderFortyNineSevenHighT*Rep*Certificate.lean` | dest `proofs/Proofs/Certificates/strata-lrat/`; each module `include_str "Certificates/strata-lrat/h7_t*_rep*.packed.lz4p7"`; per-file sha256 compare against the manifest | yes | |
| Requires AWS CLI and authenticated credentials, Requester Pays; exercised only with bucket-owner credentials (L280) | fetch script (`aws s3 cp --request-payer requester`); third-party ACCEPTED.md limitation; fetch log ARN `221082181346:assumed-role/Erdos85LeanBuilder` | matches | yes | The script header comment says "any AWS credentials work". That is broader than tested. It is outside the paper (non-critical note). |
| 2.39 GB output bundle retained outside the repository; per-file hash manifest committed beside it (L280) | ACCEPTED.md; `attempt2-evidence/full-bundle-manifest.json` | 2,389,485,055 bytes, sha256 `842425...021b2` | yes | **Fresh check:** the local archive at the recorded path has exactly that size and sha256. The attempt-1 archive (206,100,022 B, `1d28b1...6211`) and the third-party archive (2,389,489,668 B, `0b6491...b1e9`) also match their records. |
| Cold rebuild replayed all thirteen certificate checks from the published files (L121; Table 2 H7 t≥1) | README "Inputs and isolation"; PLAN.json artifacts; third-party fetch log | the 13 certificate modules are in the 893-module closure; inputs hash-verified against the manifest; the third-party run fetched from the public bucket | yes | For attempt 2 the bytes are hash-identical to the published files. The third-party run actually downloaded them. |
| h=9 checks 18 certificates (L97, Table 2) | PLAN.json exports | `orderFortyNineT{2,3,4}Rep*_check` = 2 + 5 + 11 = 18 | yes | |
| H3: 408 native_decide parts (24 + 384) (L117, Table 2) | PLAN.json exports | `H3Pair` 24, `H3TripleCompletion` 384 | yes | |
| H5: 40 search parts + 18 cover/cardinality checks = 58 (L119, Table 2) | PLAN.json exports | `H5` 40; fiveHigh* cover/card = 4 + 1 + 1 + 10 + 2 = 18 | yes | |
| H7 t≥1: 13 certificate checks among the capstone's native_decide axioms (L121) | PLAN.json exports | `sevenHighT{1..7}Rep*_check` = 1 + 2 + 3 + 3 + 2 + 1 + 1 = 13 | yes | |
| H1 cover: 23 native_decide (L145, L153, Table 2) | PLAN.json exports (oneHigh*/finEight/finFive/card_filter/enumerate families) | 23 | yes | |
| 28 + 377,776 = 377,804 H7 t=0 formulas (abstract, L78, L85, L153, Table 2) | arithmetic | 377,804 | yes | Unchanged from v11. |

## Carried from v11 (unchanged text; not re-derived in this audit)

The H1 table values (12,094 / 1,160 / 96 / 1 = 13,351; 22.55 TB, 5.64 TB, 0.10 TB, 47.1 GB; about 28 TB), the H7 campaign totals (4,269 solver / 706 checker CPU-hours, about 20.2 TB), the 13,541 − 190 = 13,351 inventory, the census of about 5,700 core-hours, the $225 estimate, and the clause and variable counts are unchanged from v11. The v11 audit and `.11.numeric` traced them. `scope_lint.py` traced every 4+-digit number and every decimal-with-unit to the refs corpus (38 numbers: PASS). Internal sums checked again here: 12,094 + 1,160 + 96 + 1 = 13,351; 13,541 − 190 = 13,351.

## Figures

There are no `\includegraphics` and no `figures/` directory, so no stale-figure check applies.

## Mismatches

There are no numerical mismatches. One identifier mismatch is a factual inconsistency: the Availability text names commit `92ff6248033c`, while every link resolves at `fa2b41268df`. See flags.md C1.
