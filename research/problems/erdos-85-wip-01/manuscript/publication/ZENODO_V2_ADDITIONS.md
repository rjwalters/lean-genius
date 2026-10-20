# Zenodo v1.1: additions to the receipts bundle

**Status.** These are the files that version 1.1 of the Zenodo record adds to `erdos85-receipts.zip`. The version
was written 2026-10-20 in response to external review (erdosproblemaday.com, jhpvtq). v1 (DOI 10.5281/zenodo.23325806)
and its file list are in `ZENODO.md`. The v1.1 zip holds every v1 path plus the paths below, all taken from tag
`erdos85-paper-v1.1`. Nothing is moved: every path is a repository path, and the zip keeps the directory structure,
exactly as in v1.

Blob hashes are `git rev-parse <commit>:<path>`. Every script blob below is identical at the pinned commit
`2029149d7e42b74036ff0e1e82af6d33c2e32748` (the paper's `\repocommit`) and at the release-assembly tip
`7ed33974bdb518ac22d75495456e9c5f86e4a4ab`, so the paper's links already resolve to these bytes.

## Why these scripts

cake_lpr exits with status 0 even when a check fails. A proof counts as accepted only because a wrapper script
parsed `s VERIFIED UNSAT` from cake_lpr's output (and, for solves, CaDiCaL exit 20 with `s UNSATISFIABLE`). So
the wrappers, and the code that fixes which CNF bytes were checked, are part of the evidence, not just tooling.
v1 included only the public checker kit (`e85-check`, `cube_check.py`, `ami_setup.sh`). v1 did not include the
wrappers that produced the published receipts, and the kit itself imports some of them (`cert_row.py`,
`bank_check_row.py`, `cube_verdict.py`).

Acceptance tests as written in the code:

- H1 (`cert_row.py`, `bank_check_row.py`, `check_leaves_cake.py`, `replay_historical96.py`): the substring
  `s VERIFIED UNSAT` must appear in the cake_lpr log. The bank pass also requires the streamed hashes to match
  the producer ledger, and the cert pass requires the checker not to have closed the stream early.
- H7 (`cert_item.py`): a line must equal `s VERIFIED UNSAT` exactly.

## Scripts to add (blobs at `2029149d7e42`)

### H1 census: per-row certifier and its cloud driver (1,160 rows)

| Path (under `research/problems/erdos-85-wip-01/`) | Git blob | Purpose |
|---|---|---|
| `h1_cert_full_20261001/cert_row.py` | `38bdbba807a77ec1fa4852de2e567d88a6cf15b1` | Certifies one census row: emits the CNF with the pinned v2cnf, requires sha256 = census `cnf_sha256`, streams CaDiCaL binary LRAT through a hashing relay into cake_lpr. Acceptance (`CERTIFIED`) = CaDiCaL exit 20 with `s UNSATISFIABLE` **and** `s VERIFIED UNSAT` in the cake_lpr log; the checker's exit code is recorded but not used. Also imported by `cube_check.py` and the H7 `cert_item.py`. |
| `h1_cert_full_20261001/cert_worker.py` | `ed741f6b9894d6ebb9ef359b552e4df3fdc45766` | Cloud node supervisor: S3 claim/ledger/STOP discipline, runs `cert_row.py` per slot, keeps receipts only. |
| `h1_cert_full_20261001/cert_controller.py` | `13f1358afed96d84b49a36cebac9e5160cdc91e1` | Mac-side controller (IAM, launch, watch, budget stop); completion requires a CERTIFIED ledger. |
| `h1_cert_full_20261001/cert_bootstrap.sh` | `a5d9cd50cd57415afdd33eac2ac701efd8eacfca` | Node bootstrap: hash-checks the pinned freight (image, v2cnf, CaDiCaL), builds cake_lpr at `a36874a8`, preflights a must-accept and a must-REJECT case. |
| `h1_cert_full_20261001/build_manifest.py` | `60dd3a194620ba621701629dca9523d4360b2d0b` | Builds the freight manifest (`receipts/h1_cert_full_manifest.jsonl`, sha256 `9d04a66c…31c2`) from the census table; requires table, preparation and solve result to agree on `cnf_sha256`. |
| `phase_b_h1_verdict_cloud_20260921/controller.py` | `a5b90e37191950928661c4d904d418f1af39a289` | Reviewed verdict-pass controller that the cert, bank and H7 controllers reuse (imported as `vc`). |

### H1 bank re-validation (12,094 archived proofs)

| Path (under `research/problems/erdos-85-wip-01/`) | Git blob | Purpose |
|---|---|---|
| `h1_bank_check_20261006/bank_check_row.py` | `e4daa8b4fbb96845715c4184bc5f029729ca4c9b` | Re-validates one bank row: rebuilds the orbit table from `h1_orbit_inventory.compact`, emits the CNF with the pinned v2cnf, streams the S3 proof into cake_lpr. `VERIFIED` only if `s VERIFIED UNSAT` is printed **and** the streamed gz/LRAT hashes match a producer-ledger candidate. |
| `h1_bank_check_20261006/bank_worker.py` | `0e4438e42725a145383bc5566f9a5dea0b39ed9b` | Cloud node supervisor for the bank pass (derived from the cert worker). |
| `h1_bank_check_20261006/bank_controller.py` | `32bc88b766430db4086fc6588c779ad867fc3b11` | Mac-side controller for the bank pass. |
| `h1_bank_check_20261006/bank_bootstrap.sh` | `658915c04d4540e94d27faf4f863e6f48d46534c` | Node bootstrap for the bank pass (same preflights as the cert bootstrap). |
| `h1_bank_check_20261006/build_bank_manifest.py` | `d27fe1b56abf3194a299cdd7fbf30bbdbf77f382` | Builds `bank_manifest.jsonl` (one row per bank object, with every producer-ledger candidate). |
| `h1_bank_check_20261006/bank_pilot_driver.py` | `df3092a26b013a0b8137f24224f6b93016678990` | Local driver running `bank_check_row.py` over a tag list. |

### H1 public checker kit (already in v1)

| Path (under `research/problems/erdos-85-wip-01/`) | Git blob | Purpose |
|---|---|---|
| `h1_checker_kit/e85-check` (in v1) | `d7b41ab9946e8ce674272bd935259eff40b1d916` | Third-party entry point (`bank`, `census`, `cube`, `summary`); calls `bank_check_row.py`, `cert_row.py` and `cube_check.py`. |
| `h1_checker_kit/cube_check.py` (in v1) | `1e171db3392a511f162d07d5c97343088d7f82ff` | Rebuilds the 36 cube CNFs of `h1_81494a6ef36d3ec9`, requires each sha256 = banked `cube_sha256`, then solves and checks each via `cert_row.solve_and_check`. |
| `h1_checker_kit/ami_setup.sh` (in v1) | `bd2eac1c0ecf31328adf5e5dd021fe0bd0b6f2cd` | Prepares an AL2023 arm64 host as a checker (what the public AMI was built with); self-test requires accept-valid and reject-corrupted. |

### H1 hardest orbit (cube tree) and the 96 historical certificates

| Path (under `research/problems/erdos-85-wip-01/`) | Git blob | Purpose |
|---|---|---|
| `phase_b_h1_verdict_cloud_20260921/cube_verdict.py` | `ec26c35f2b4ebdc9e4e4e715f6c826c740474307` | Defines the cube CNF bytes (`cube_bytes`: base CNF + unit clauses after the header) and `read_cnf`; the definition behind every `cube_sha256`. |
| `sat49/run_verdict_only.py` | `1f79de8f226db1be41543f6d1abbbb884fbeb6b0` | Imported by `cube_verdict.py` (`sha256`, solver identity helpers). |
| `h1_cert_pilot_20261001/solve_leaves.py` | `23c6e2a2b7690da7862e7f9ebc8dd2d87c2e97a0` | Proof-logged re-solve of the 36 leaves; refuses (`CUBE_SHA_MISMATCH`) a leaf whose regenerated cube hash differs. Wrote the five rows without `cube_sha_ok`. |
| `h1_cert_pilot_20261001/backfill_leaf_receipts.py` | `b021ffb7c931e2d511cd7cc78012fe084a3d9792` | Rebuilt the 31 receipts lost in the 2026-10-01 host crash from `cadical.log`; records `cube_sha_ok`. |
| `h1_cert_pilot_20261001/check_leaves_cake.py` | `f2b0506fd0440e1619a8f604c55c5d5b9f8a261e` | cake_lpr check of each pilot leaf; `CAKE_LPR_VERIFIED` = exit 0 **and** `s VERIFIED UNSAT`. |
| `h1_cert_pilot_20261001/check_leaves.py` | `e304aad2869461211d6f4ae8e71ae55cbff1e471` | Std `LRAT.check` (lratreplay, pinned image) of the pilot leaves (30 of 36). |
| `h1_cert_pilot_20261001/replay_historical96.py` | `ade3ccea45ab68b5ae589d1377704ecaac5fba70` | Replays the 96 historical certificates: checks the archived CNF sha256 against `historical-95/96.json`, drat-trim to LRAT, then lratreplay or cake_lpr (`CHECKER=cake`, same acceptance rule as above). |
| `h1_cert_pilot_20261001/gen_cube_tree_lean.py` | `62cc8a3eacd954be30d1885b4b8e8d3c9c70b4d2` | Emits the Lean `CubeTree` term and solver-side cube list from the banked tree (the Lean cover proof's input). |
| `h1_cert_pilot_20261001/gen_leaf_stubs.py` | `14bc11b61eb259780797599857db6f6dda745c2f` | Packs each leaf's binary LRAT and emits the Lean leaf modules and aggregate module. |
| `phase_b_historical_overlay/historical-95.json` | `151ebbe117a8dae013fc882e48c510ff87b11d64` | Expected CNF sha256 for 95 historical orbits (source of `cnf_sha256_expected`). |
| `phase_b_historical_overlay_96/historical-96.json` | `1f6d3541e108d96e7a5096139c99df33c868e8f6` | The 96th historical orbit (`extra_case`). |

### H7 (t = 0) certificate campaign (28 cubes, 377,776 leaves)

| Path (under `research/problems/erdos-85-wip-01/`) | Git blob | Purpose |
|---|---|---|
| `h7_hsb_campaign_20261008/h7_common.py` | `1c867619f5f215d5c3da68841ba4fc5d01693042` | Shared definitions: input layout, pinned cube bytes, how leaf/cover/split CNFs are assembled. |
| `h7_hsb_campaign_20261008/build_inputs.py` | `f2a93fe9bd05f9ea6bcb8b8beb90087bf0aa67fe` | Builds the pinned campaign inputs; every cube CNF must hash to the frozen root hash. |
| `h7_hsb_campaign_20261008/EmitCube.lean` | `b4cb207009268db065fcf9ce30acea79d488d06b` | Prints the Lean cube term as DIMACS (base-cube byte identity). |
| `h7_hsb_campaign_20261008/EmitSplit.lean` | `7b5e5aa6e0aea06dca38868520c2ab7c7e71f92d` | Prints the split-leaf tails from the Lean definitions, with `rfl` decomposition theorems. |
| `h7_hsb_campaign_20261008/check_base_identity.py` | `b7f67239ff514560e3c1e8c3762d10da4503e1c9` | Compares the Lean-printed cubes with the frozen Python root hashes. |
| `h7_hsb_campaign_20261008/check_base_identity.sh` | `b9e0a9455ebe14282126af977fc8b4383c82c2ad` | Runs the base identity check in the pinned Lean image. |
| `h7_hsb_campaign_20261008/check_split_identity.py` | `73851addfb1fd8a4211b9a3ae67136d4671d833b` | Compares Lean split tails with those `h7_common` appends. |
| `h7_hsb_campaign_20261008/check_split_identity.sh` | `8ee9d38357702c7438da5c9929ef793abf11984c` | Runs the split identity check in the pinned Lean image. |
| `h7_hsb_campaign_20261008/split_leaf.py` | `d8456851ba02c98e84e45a2bcf07f6dab923c6a0` | Splits hard leaves into sub-leaves plus a sub-cover. |
| `h7_hsb_campaign_20261008/leaf_tree.py` | `33caba6c4c4cd4d4841b43c5c75a804e71b0a8ce` | Position of each leaf in the generator tree, from the pinned inputs. |
| `h7_hsb_campaign_20261008/cert_item.py` | `3e9a7c28996d5fd4e8cc3811679710a1ed3e9bb4` | Certifies one leaf/cover/sub-leaf/sub-cover CNF: requires the file sha256 = expected, then CaDiCaL to cake_lpr through the H1 `cert_row` code. Acceptance requires a line exactly equal to `s VERIFIED UNSAT`; the exit code is ignored. |
| `h7_hsb_campaign_20261008/cert_batch.py` | `113b1f18867899bc307a4078e16dde76fb3625c2` | Certifies one claim unit (a batch of leaves, one cover or one split item); one CNF, proof and verdict per leaf. |
| `h7_hsb_campaign_20261008/cert_worker.py` | `d400ff790d7b4c09ab327cc7183083f259767b05` | H7 node supervisor (claims, STOP, ALARM on CHECK_FAILED or SAT). |
| `h7_hsb_campaign_20261008/cert_controller.py` | `b4ab01041ad545c7afca1ff70e8e8eed6c39a9e5` | H7 Mac-side controller. |
| `h7_hsb_campaign_20261008/cert_bootstrap.sh` | `397e653e8fc4208dbfe792e0a59007a689041559` | H7 node bootstrap (pinned inputs, CaDiCaL and approved cake_lpr binary). |
| `h7_hsb_campaign_20261008/campaign_totals.py` | `3d860319f3a2c41d0395a69a682eaeeac991bf4b` | Campaign-wide totals over every result file (`receipts/collected/campaign_totals.json`). |

### H7 generators

| Path (under `research/problems/erdos-85-wip-01/`) | Git blob | Purpose |
|---|---|---|
| `sat49/generate_h7_canonical_cnfs.py` | `46f2fc43ae22ebe063c3c874aee934615eafd982` | Emits the 14 canonical h = 7 order-49 classified CNFs (linear triple systems on seven points, canonicalized under the 7! relabelings). Needs `python-sat` (`pysat.card`, `pysat.formula`). |
| `sat49/generate_h7_lean_stubs.py` | `1b7da057f9e2c62632728c4326896d807029390c` | Generates the Lean certificate modules from the packed h = 7 strata manifests (the t >= 1 files listed in `strata-lrat.MANIFEST.sha256`). |

## Receipts and notes added in v1.1

These are new files, not at the pinned commit. The blob hashes in this table were taken at the commit that added them, and
they are unchanged at the tag.

| Path (under `research/problems/erdos-85-wip-01/`) | Git blob | Purpose |
|---|---|---|
| `h1_cert_full_20261001/receipts/h1_cert_full_manifest.jsonl` | `0a1751f2759c60eb2d09458110e5be99ba531ec0` | The census manifest cited in the receipts README (file sha256 `9d04a66c36497329ae594c5b0f2924c7055a8355651b223bef3c4d8a4fb231c2`, 1,160 rows, 345 KB). Before this branch it existed only on the project volume. |
| `h1_cert_full_20261001/receipts/pilot_h1_81494a_leaf_expected_sha256.tsv` | `ff0927fd6796b84339a4fb89b6b6e00a1f0244d9` | Expected and recomputed cube-CNF sha256 for all 36 pilot leaves; 36/36 match (file sha256 `3e1cc9ac…3e89`). |
| `h1_cert_pilot_20261001/recompute_leaf_cube_sha256.py` | `104579ef354ccc2c556d8266b9155e4a1617399d` | Produces the TSV above. |
| `h1_cert_full_20261001/receipts/README.md` | (changed; take the merged version) | Adds two sections: "Pilot leaf cube hashes" and "Census manifest". |

## Other v1.1 additions (take them at the tag)

- `H7_SOURCE_CNF_SHA256_NOTE.md`: what the `source_cnf_sha256` header of the H7 t >= 1 modules hashes (the pysat file,
  with IDPool variable numbering), with the renumbered hashes.
- `emitter_duplicate_bytes_20261020/`: diagnosis and reproducer for the "duplicated trailing bytes" docstring of
  `Erdos85OneHighV2CnfEmit.lean` (two writers on one redirected file, not Lean).
- `proofs/Proofs/Erdos85OneHighV2InventoryNonzero.lean`: Lean proof of the `nonzero` field over the whole inventory.
- `proofs/Proofs/Erdos85OrderFortyNineCapstoneH3UnsatOnly.lean`: the three capstone theorems restated on bare
  unsatisfiability of the H1 family.
- The emitter sources `proofs/Proofs/Erdos85OneHighV2CnfEmit.lean`,
  `proofs/Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalHsbEmit.lean` and
  `proofs/Proofs/Erdos85OrderFortyNineSevenHighT0CubeCnfEmit.lean`, and `proofs/lakefile.toml`. The emitters
  run pinned by binary hash (emitter sha256 `4bd9604c…bf6`, image `sha256:a5ca6c4e…6dff6`).

## Not included, noted for completeness

- `gen_leaf_stubs.py` imports `sat49/compress_h1_v2_binary_lrat.py`, and the H7 generators import other
  `sat49/generate_h7_*` modules. Add those if a later version aims to let readers re-run generation, not only read it.
- H3/H5 cell certification (`h35_probe_20261007/cert_cell.py`, `h35_pilot_20261007/launch_pilot.py`) also parses
  `s VERIFIED UNSAT`. The paper excludes H3 and H5 in Lean, so these are optional.
