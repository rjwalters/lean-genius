# Phase B exact surviving input inventory

This inventory implements board goal 38 / operator goal 48 and editor message 46111. It identifies **1,416 current targets** across H1, H3, H5 and H7. It is not yet a launch-ready CNF queue and contains no new SAT verdict. The [Phase A master table](Q7_SQUEEZE_20260910.md) records the filter outcomes; the [host plan](PHASE_B_HOST_PLAN_20260910.md) specifies caps, concurrency and UNKNOWN reporting.

The machine-readable [combined index](phase_b_survivors_20260910.json) lists every unique ID, sector, source-array index and available CNF hash. Its four source files are SHA-256 pinned. Looking up the recorded array index must reproduce that exact ID; the sector source retains the full table, unit list, relabeling and generator provenance. This index deliberately uses a different schema from the executable solver manifest: unresolved materialization cannot silently become a runnable row.

| Sector | Exact current targets | Input identity | Remaining preparation |
| --- | ---: | --- | --- |
| H1 | 1,257 miss-table orbit rows; profile counts 283/346/388/198/42 | Each ID joins to all 24 compact-table values in the capacity-filtered 13,351-row universe | Known native-emitter pilot passed review 1992; bounded per-row emission/checking and dispatch hashes remain incomplete |
| H3 | 2 canonical base roots, `h3_t0_canonical` and `h3_t1_canonical` | Existing base hashes, 29,500 variables, 1,328,183 clauses each | Join with execution caps and input evidence; use as an independent solver cross-check of the earlier Python exclusion |
| H5 | 129 root cubes, 43 in each of t0/t1/t2 | Exact signed units and prospective hashes from three verified corrected 29,632-variable bases | Materialize one bounded root at a time; compare final byte count and SHA-256 before dispatch |
| H7 | 28 empty-support class roots; counts 7/12/7/2 at 6/7/8/9 edges | Exact parent IDs, 21 signed units, explicit vertex maps, and prospective hashes from the verified compact base | Materialize bounded roots and verify final hashes; do not add the alternative 232 adaptive leaves |

## Local DRAT, unreplayed

| Evidence subset (already within H1) | Exact rows | Input identity and availability | Closure status |
| --- | ---: | --- | --- |
| Local CUBE25 DRAT archive identified by the editor | 45: 20 historically verified, 25 historically not verified | All 710 retained cube CNFs across 38 tags reconstruct to their frozen base hashes after removing two trailing units; 18 tags have all 25 input and proof filenames present | **Local DRAT, unreplayed.** No new closed cases; proof validity, cube-cover justification and missing files remain unresolved |

The [45-row evidence package](phase_b_local_drat45/README.md) records exact tags, archive paths, hashes and limitations. These 45 tags have no overlap with the separately reviewed 95-case MONO historical overlay. Availability across directory copies is not a proof certificate; seven tags have no retained cube CNF in this scan. Counts above do not change the frozen 1,416-target index.

## Exact lists and provenance

H1/H3 evidence is in [PHASE_B_H1_H3_INVENTORY_20260910.md](PHASE_B_H1_H3_INVENTORY_20260910.md), independently reviewed in **1990**. H5/H7 evidence is in [PHASE_B_H5_H7_INVENTORY_20260910.md](PHASE_B_H5_H7_INVENTORY_20260910.md), independently reviewed in **1991**. Those reviews checked input/set identity and stated limitations, not solver outcomes.

| Sector | Exact instance source | Generator identity |
| --- | --- | --- |
| H1 | `phase_b_h1_h3/h1-frozen-candidates.json`, array `rows` | `Erdos85OneHighV2CnfEmit.lean` last change `1a15845782e7b503d01393649948aa3ee5b007ba`; `Erdos85OneHighV2Cnf.lean` last change `7ba8e52d8149ae869598529fe006585166cf1747`; full source hashes in the sector receipt |
| H3 | `phase_b_h1_h3/h3-inputs.json`, array `instances` | `generate_small_high_canonical_cnfs.py`, last change `ecd4d3ec203753d1a6cb9967c0497b78d1d37969`; source SHA and existing CNF hashes retained per row |
| H5 | `phase_b_h5_h7/h5-inventory.json`, array `jobs` | Current `generate_small_high_cube_jobs.py` last change `1241c1ae0af05cd3145de755dcac4b74e082c750`; historical freight Lean commit `38b15d484b22d205476baba9f4898c9ffc91044d`; approved manifest SHA starts `05381a1c` and is retained in full |
| H7 | `phase_b_h5_h7/h7-inventory.json`, array `survivors` | Current `generate_h7_empty_cube_manifest.py` last change `10d21dedc2e84b9bd9207669f5644c17d18ba83c`; original parent identity and compact-base hash retained |

“Last change” identifies the current source, not a claim that a historical input was generated at that revision. The sector manifests retain that distinction. No full historical environment was regenerated for this inventory.

## Why these counts differ from earlier planning estimates

H1 is the exact conservative set difference **13,351 − 11,954 − 140 = 1,257** at the retained snapshot. The first removed set uses earlier screened ledger rows whose positive-size objects remain present; the second uses freshly screened producer-success records. The 140 comprise 127 ordinary uploads and 13 multipart rescues. This pass did not download or kernel-check those certificates. Three historical object conflicts remain in the 1,257 candidates. Local names locate variants for only 222 tags; the other 1,035 have no located named CNF. A filename match is not canonical-input evidence.

H5 retains **174 − 45 = 129** roots after the historical direct-certificate inventory, 43 per cell. Later verdict absence was not freshly established. Corrected 29,632-variable bases are used throughout; the obsolete 29,500-variable H5 header is not accepted.

H7 starts with 43 class roots. The reviewed capacity argument excludes 15, leaving **28**. Every parent-to-classification relabeling was checked explicitly. All 14 historical direct certificates lie among those 15 exclusions; the additional removed missing root is `cube_F6_t2`. The 232 historical adaptive leaves subdivide the earlier 29 missing parents. They are an alternative cover and must not be counted alongside the tighter 28-root choice.

H3's two SAT bases are broad support-profile cross-checks. The paper/Python exclusion is already recorded separately; the banked formal remainder **full 261 / deficient 1554** counts Lean proof obligations and is not added to this SAT inventory.

## Dispatch boundary

The combined inventory has `launch_ready: false`. Before a target can be dispatched, its exact canonical CNF bytes, generator/input-validation evidence, primary and cross-check caps, cross-check requirement and banked start time must be joined into an executable manifest. H1 emission is a remaining preparation task. H5/H7 inputs have prospective identities but still require bounded materialization. H3 inputs have been independently streamed through a strict DIMACS count/bounds validator as well as hash checked.

The existing Lean H1 `check` command alone is not sufficient file validation: its parser skips headers and empty clauses and treats physical lines as clauses. Review 1994 demonstrated that a general streaming DIMACS validator plus matching header/count still accepts altered clause framing containing an injected empty clause. Require exactly one complete clause per physical data line, one final zero and no internal zero, and ASCII-space token framing. Then require header, variable-bound and clause-count agreement with `MATCH(count,top)`, plus the applicable exact byte hash. The repaired validator rejects the production counterexample and accepts the original canonical input. Do not accept old pinned/core variants merely because the comparator prints MATCH.

No host or cloud solve follows automatically from banking this document. Phase B starts under the host plan after the agreed Phase A close. The first three hard cases are a bounded calibration, not an implicit launch of all 1,416 rows. Any timeout or resource cap remains UNKNOWN. A future whole-split verdict table must also retain the provenance of prior screened exclusions; an all-UNSAT result on just this new queue is not a fresh kernel validation of those older results.
