# H3/H5 cube-and-conquer feasibility pilot (2026-10-07)

Question: is there a cube depth at which the Lean-exact H3/H5 cell formulas (see
`../h35_probe_20261007/`) split into pieces that solve in minutes? If so, what would certifying
all five cells cost?

**Answer: NO-GO under the $150 budget.**
- H5 splits well: depth-10 cubes solve in seconds to minutes. But the tree is too wide. Each H5
  cell needs about 2M cubes (at least $300–700 per cell with certification).
- H3 does not split at all with this rule: 0 of 24 H3 t0 cubes solved within 30 min at depths
  10, 14 or 18.
- The certificate path itself works: 2 of 2 cubes were CERTIFIED by cake_lpr.
- No certification campaign was started.

## Method

**Split rule** (`sample_walks.py`). The rule branches on the cell's *partition clauses*:
- There is one positive clause per (low vertex, high vertex) pair. Each has 7–8 edge literals.
- H5 cells have 220 of them; H3 cells have 138.
- These are the same selectors as the existing Lean grid `Erdos85OrderFortyNineSmallHighCubeCover`.

At each cube:
1. Unit-propagate the base units together with the cube.
2. Take the unsatisfied partition clause with the fewest non-falsified literals (fail-first).
3. Drop any literal whose assertion leads to a unit-propagation conflict.
4. Branch on each surviving literal.

**Why not the H1 method.** The H1 81494a tree was built by `phase_b_h1_verdict_cloud_20260921/cube_adaptive.py`:
- It made binary splits chosen by unit-propagation lookahead, using a greedy max–min count of
  forced literals.
- The pre-split went to depth 5, followed by Kissat probing and adaptive refinement.
- On these cells that lookahead is degenerate. A negative edge literal forces almost nothing
  (6196 vs 6190 base literals), so every binary split is one-sided.
- Positive partition-clause literals force about 200–260 literals each.

**Lean cover.** The tree is Lean-coverable by the same composition as H1:
- A k-way branch on clause (x1 … xk) is the binary `CubeTree` split x1 / (¬x1: split x2 / …).
- Its all-negative leaf is refuted by unit propagation from the partition clause.

**Sampling.** Knuth random walks (Knuth 1975):
- Each walk picks a uniform surviving literal at every level.
- W_d = ∏ branching factors over the first d levels. It is an unbiased estimate of the number of
  depth-d cubes.
- mean(W_d · t_d) estimates the total CaDiCaL time of the whole depth-d frontier.
- Walks that end early contribute 0. Timeouts contribute the cap, which makes the estimate a
  lower bound (marked `>=`).

**Run.** `launch_pilot.py` and `pilot_node.py`:
- One r7g.16xlarge spot instance (us-east-1a, max price $1.50), launched from the public checker
  AMI `ami-05697724475f2e748`.
- No IAM role: data moved through presigned S3 URLs under `s3://2am-erdos85-certs/sat49/h35-pilot-20261007/`.
- A pilot-owned no-ingress security group, deleted afterwards.
- Hard stop: `shutdown -P +170` plus a systemd poweroff timer, with
  InstanceInitiatedShutdownBehavior set to terminate.
- 64 concurrent CaDiCaL 3.0.1 jobs, cap 1800 s, no proof logging.
- Cube CNF layout: unit clauses sorted by variable and inserted after the header. This is
  `cube_verdict.cube_bytes`, the H1 layout.

## Results (`receipts/results.jsonl`, `receipts/summary.txt`)

| cell | depth | solved / sampled | median s | max s | cubes (est.) | CPU-h, verdict only (est.) |
|---|---|---|---|---|---|---|
| h5_t0 | 7 | 5/16 (11 UNKNOWN) | 1800 | 1800 | 5.8e4 | ≥ 2.3e4 |
| h5_t0 | 10 | 16/16 | 9 | 235 | 1.9e6 | 2.8e4 |
| h5_t0 | 13 | 16/16 | 2 | 7 | 3.4e7 | 1.8e4 |
| h5_t0 | 16 | 16/16 | 1 | 2 | 4.1e8 | 1.3e5 |
| h5_t1 | 13 | 7/7 | 1 | 17 | 2.9e7 | 1.7e4 |
| h3_t0 | 10 / 14 / 18 | **0/8 each** | 1800 | 1800 | 2e6 / 4e8 / 3e10 | ≥ 1e6 / 2e8 / 1e10 |

The depth-7 H5 times that did finish were 135–1337 s. The estimates have high variance: one
depth-10 walk at 235 s dominates that row.

**Certificate path.** Two cubes (H5 t0 at depths 10 and 13) went through CaDiCaL binary LRAT,
streamed through a FIFO into cake_lpr (`h1_cert_full_20261001/cert_row.solve_and_check`). Both
printed `s VERIFIED UNSAT`, so status is CERTIFIED.

| cube | proof size | solve CPU | check CPU |
|---|---|---|---|
| H5 t0, depth 10 | 15.2 MB | 4.9 s | 3.4 s |
| H5 t0, depth 13 | 13.3 MB | 4.3 s | 3.3 s |

Each cube took about 8 s wall. Most of that is the fixed cost of reading the 1.33M-clause CNF
twice, so every certified cube costs at least about 7.6 CPU-s.

## Extrapolation

Prices are at $0.0147 per vCPU-hour (r7g spot). The figures are estimates.

**H5 cells**

| depth | cubes per cell | verdict cost | with certification |
|---|---|---|---|
| 10 | about 1.9M | about 28k CPU-h (about $400) | about 1.5–2× more |
| 13 | about 3.4e7 | — | about 75k CPU-h, set by the fixed cost per cube alone |

- Best case is at least $300–700 per H5 cell, so the three H5 cells come to at least about $1–2k.
- H3: no depth up to 18 gives solvable cubes. The lower bound is at least $16k per cell at
  depth 10, and the real cost is unbounded with this split.
- Overall this is one to two orders of magnitude over the $150 budget.

**Lean cover effort.** Coverage itself is easy; the size of the tree is the problem.
- `cnf_unsat_of_cubeTree` (`Erdos85CubeTreeComposition.lean`, axioms `propext` and
  `Quot.sound`) composes any binary tree.
- The H1 pattern spells the tree out as a Lean term and checks coverage with kernel `decide`
  (36 leaves). That cannot scale to about 10^6–10^7 leaves per cell.
- A viable cover would need either of these:
  - a generic lemma that instantiates `cubes := T.cubes`. Coverage is then trivial, but the
    leaf CNFs must list their units in tree order rather than sorted order.
  - a tree-shaped partition-clause recursion lemma, with the tree kept as external data.
- Either way, each leaf certificate stays an external hypothesis, as in H1.

## Spend and cleanup

- Instance `i-015c6ca4497340af1`, r7g.16xlarge spot at $0.9423/h.
- Ran 18:49:33–19:21 UTC (about 32 min), about **$0.50**. EBS and S3 costs are negligible.
- The instance is terminated and its spot request closed. The pilot security group
  `sg-0cf33946ed7519362` is deleted.
- Of the pilot's S3 objects, only the `out/` receipts remain. The `in/` copies are deleted.
- No other bucket, AMI or public prefix was touched.

## Files

| file | role |
|---|---|
| `sample_walks.py` | splits on partition clauses and samples Knuth random walks |
| `pilot_node.py` | node side: walks, timing, then certification of the 2 fastest solved cubes |
| `launch_pilot.py` | `upload` / `launch` / `cleanup` |
| `analyze.py` | per-depth distribution and estimates |
| `receipts/` | `results.jsonl`, logs, `launch.json` |

Bulky artifacts are in `/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h35-pilot-20261007/`
(`cloud/out.tar.gz` holds every CaDiCaL log).
