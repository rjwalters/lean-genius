# H7 t=0 hsb3 certificate campaign: estimate and runbook (2026-10-08)

**Status: prepared, NOT launched.** No instance, role, launch template or S3 object of this
campaign exists. Everything below was measured on the existing cloud builder
(`i-04a61ff360a07bef2`, r7g.4xlarge) with at most 8 threads.

Goal: the external evidence for `SevenHighT0CanonicalHsbEvidence 3 F i` for each of the 28
structural cubes, which Lean turns into `OrderFortyNineStratumExcluded 7`
(`…HsbStratumCapstone.lean`). Per cube that is one checked cover CNF and one checked CNF per leaf:
377,776 leaf CNFs and 28 cover CNFs in total.

@@SUMMARY@@

## 1. What is certified, byte for byte

All files have the header `p cnf 17633 <clauses>`; Std.Sat variable `v` is DIMACS `v + 1`.

| file | bytes | Lean term |
|---|---|---|
| cube CNF | `canonical.body` ++ 21 mask units (720,825 clauses) | `orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i` |
| hsb CNF | cube ++ `h7hsb hsb 3 mask` | `orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf 3 F i` |
| cover CNF | cube ++ hsb ++ `h7hsb cover 3 mask` | `SevenHighT0CanonicalHsbCoverChecked 3 F i (leaves 3 mask)` |
| leaf `n` CNF | cube ++ hsb ++ one **positive** unit per literal of cover line `n`, in line order | `SevenHighT0CanonicalHsbLeafChecked 3 F i rows_n` (`cnfClauseNegUnits (clause rows_n)`) |

Identity receipts:

* **Base cube = Lean term, all 28 cubes** (`receipts/base_cube_lean_identity.json`, builder job
  `20261008T051026-…-211746`). `EmitCube.lean` prints
  `orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i` with interpreted `lake env lean --run`
  in the pinned image; each of the 28 outputs has the sha256 of the frozen root hash of the
  reviewed Python generator (`h7-frontier-map-20260915/results.json`), 15,151,828 bytes and
  720,825 clauses each. The sha256 values are the `cube_cnf_sha256` fields of
  `receipts/inputs.json`.
* **hsb and cover lines = Lean term** (`../h7_structural_pilot_20261008/receipts/hsb_lean_identity.json`,
  earlier job). `build_inputs.py` re-ran the native `h7hsb` (sha256 `dd0e2ab8…70d9`, the binary
  built by the builder from this branch) and requires the same sha256 values.
* `receipts/inputs.json` (sha256 `f2d2be89…cb6c`) pins every input file, the three derived CNF
  hashes per cube, the per-cube leaf-manifest hash and the batch-manifest hash
  (`27799edd…e785`, 5,945 claim units).

### Leaf manifest

Leaf `n` of a cube is line `n` (0-based) of `<cube>.cover`; its units are the negated literals of
that line. The full manifest (377,776 lines: cube, leaf, units, leaf CNF sha256; about 80 MB) is
not committed. It is regenerated deterministically:

```bash
python3.12 build_inputs.py --h7hsb <native h7hsb> --out <dir> --leaf-manifest   # writes <cube>.leaves.jsonl
```

and each `<cube>.leaves.jsonl` must hash to `leaf_manifest_sha256` in `inputs.json`. The worker
never trusts a precomputed leaf hash: `h7_common.Cube` re-hashes the pinned inputs when a batch
starts, and `cert_item.py` hashes the CNF file the solver and checker actually read and compares
it with the value recomputed from those inputs.

@@ESTIMATE@@

@@RUNBOOK@@
