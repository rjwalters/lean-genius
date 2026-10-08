# H5 stratum (cells T0, T1, T2): build receipt, 2026-10-08

All builds ran on the erdos85 cloud builder through `e85-remote build`,
branch `erdos85/h5-formal-20261008`. The log excerpt of the receipt build
(everything from the first H5 part to the end, including the full axiom
lists) is `logs/job-455708-h5.log`.

## Result

Built in job 455708 at commit `99bc3e3413008ca13d5efb29bee5e855af961976`,
exit 0, `Build completed successfully (8794 jobs)`:

| Theorem (namespace `Erdos85.H5`) | Statement | File |
|---|---|---|
| `fiveHighCanonicalRepresentativeExcluded_0` | `FiveHighCanonicalRepresentativeExcluded 0` | `Erdos85H5T0.lean` |
| `fiveHighCanonicalRepresentativeExcluded_1` | `FiveHighCanonicalRepresentativeExcluded 1` | `Erdos85H5T1.lean` |
| `fiveHighCanonicalRepresentativeExcluded_2` | `FiveHighCanonicalRepresentativeExcluded 2` | `Erdos85H5T2.lean` |
| `orderFortyNineTripleCellExcluded_five_zero` | `OrderFortyNineTripleCellExcluded 5 0` | `Erdos85H5Stratum.lean` |
| `orderFortyNineTripleCellExcluded_five_one` | `OrderFortyNineTripleCellExcluded 5 1` | `Erdos85H5Stratum.lean` |
| `orderFortyNineTripleCellExcluded_five_two` | `OrderFortyNineTripleCellExcluded 5 2` | `Erdos85H5Stratum.lean` |
| `orderFortyNineStratumExcluded_five` | `OrderFortyNineStratumExcluded 5` | `Erdos85H5Stratum.lean` |

No `sorry` in the H5 modules and no `sorryAx` in any axiom list. This is not
a kernel-only proof: see the axioms.

## Axioms (`#print axioms`, job 455708)

- `search_sound`, `parts_sound`, `model_of_constraints`,
  `fiveHighCanonicalRepresentativeExcluded_of_parts`, `searchF_sound`,
  `fiveHighCanonicalRepresentativeExcluded_of_partsF`:
  `propext`, `Classical.choice`, `Quot.sound`.
- `fiveHighCanonicalRepresentativeExcluded_0`: the standard three plus the 16
  axioms `Erdos85.H5.cellPartF_0_4_16_NN._native.native_decide.ax_1_1`,
  NN = 00..15.
- `fiveHighCanonicalRepresentativeExcluded_1`: the standard three plus the 16
  axioms `cellPartF_1_6_16_NN._native.native_decide.ax_1_1`, NN = 00..15.
- `fiveHighCanonicalRepresentativeExcluded_2`: the standard three plus the 8
  axioms `cellPartF_2_12_8_NN._native.native_decide.ax_1_1`, NN = 00..07.
- The three `orderFortyNineTripleCellExcluded_five_*` theorems: the axioms
  of the corresponding representative exclusion plus 18 `native_decide`
  axioms that were already in the imported graph-cover development and are
  not new here:
  `fiveHighCanonicalFiberCover_zero` (1), `_one` (1), `_two` (2),
  `fiveHigh_t0_mask_key_fiber_card` (1), `fiveHigh_t1_mask_key_fiber_card`
  (1), `fiveHigh_t2_mask_key_fiber_card` (2),
  `fiveHigh_t2_local_triple_card` (10: `ax_1_4` .. `ax_1_13`).
  All 18 appear in each cell theorem because each goes through
  `fiveHighCanonicalGraphCover_all`.
- `orderFortyNineStratumExcluded_five`: 61 axioms = the standard three, the
  40 part axioms and the same 18 graph-cover axioms.

Each part axiom asserts that compiled evaluation of `cellPartF c k m NN`
returns `true`.

## Jobs

| Job | Commit | Target | Exit | Notes |
|-----|--------|--------|------|-------|
| 409207 | 6e85c306db7 | `Erdos85H5Bridge` | 0 | Engine and Bridge built first try; standard three axioms |
| 413657 | bf7ebd8c26a | `Erdos85H5T2` (old `cellPart`, 8 parts) | none | Cancelled by me after about 45 min with no part finished; no verdict |
| 444749 | bf8123c969e | timing probes | 1 | Probe files were missing from the commit (my shell error) |
| 450285 | f7117ae8d26 | timing probes | 0 | `cellPart 2 4 8 2`: 209 s; `cellPartF 2 4 8 2`: 151 s; `Erdos85H5Fast` built, standard three axioms. Probe modules were then deleted |
| 454084 | 99bc3e34130 | `Erdos85OrderFortyNineFiveHighTwoFiber` | 0 | Existing graph cover, built before the parts |
| 455708 | 99bc3e34130 | `Erdos85H5Stratum` | 0 | Receipt build: 40 parts, three cell modules, stratum |

Engine, Bridge and Fast are byte-identical between the commits where they
were first built and 99bc3e34130.

## Timings (job 455708)

Eight Lean processes at a time (`--threads 8`, 48 GiB container limit).
Submitted 11:27:46Z, finished about 13:39Z: 2 h 11 min wall.

Per-part module build times in seconds (each includes a few seconds of
import; these are elapsed times of single-threaded processes, not
separately measured CPU time):

- T0 (`k = 4`, `m = 16`), sum 28,496, min 1,388, max 2,132:
  00 1894, 01 1388, 02 1875, 03 2087, 04 1732, 05 1806, 06 2132, 07 1692,
  08 1734, 09 1499, 10 1840, 11 1902, 12 1773, 13 1670, 14 1580, 15 1892.
- T1 (`k = 6`, `m = 16`), sum 15,595, min 788, max 1,172:
  00 961, 01 1021, 02 956, 03 1014, 04 788, 05 891, 06 873, 07 1001,
  08 855, 09 973, 10 1010, 11 814, 12 1142, 13 1097, 14 1172, 15 1027.
- T2 (`k = 12`, `m = 8`), sum 16,280, min 2,003, max 2,078:
  00 2035, 01 2048, 02 2003, 03 2042, 04 2045, 05 2011, 06 2078, 07 2018.

Total 60,371 s = 16.8 summed part-hours. The longest part took 36 min.

## Not used

Codex's precompiled "Runtime" module technique for `native_decide`
(`h3_runtime_split_20261008` on `erdos85/h3-triple-formal-20261007`) was
reported while job 455708 was running and on schedule; it was not used
here. It would apply to a re-run.

## Prototype (sizing only, not evidence)

See README.md. `h5proto.c` was run on the builder host; its node counts
were used to choose the split parameters and nothing else.
