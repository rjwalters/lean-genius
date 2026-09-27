# Erdős 85 artifacts on the Stripe volume — map (2026-09-27)

Root: `/Volumes/Stripe/lean-genius/artifacts/`. Sizes measured 2026-09-27. The sha256 manifest
`erdos85-sat49-MANIFEST-20260927.sha256` (194,620 files under `erdos85-sat49/`, taken 2026-09-27
17:40–18:05Z while `h1-gap34-20260927/` was still being written; regenerate after that run) is written
alongside; regenerate with `find erdos85-sat49 -type f -print0 | xargs -0 shasum -a 256`. Nothing
here is tracked in git; the repository holds the small receipts and points here for logs, CNF
snapshots, run directories and certificates. Directories are grouped by the manuscript section
they support. Directory names are the campaign's own; where a name is opaque the note says what
the contents are, not what they prove.

## Result A, H1 verdict-only census (manuscript: evidence table, §8, `phase_b_h1_census_20260927/`)

| Directory | Size | Contents |
|---|---:|---|
| `erdos85-sat49/h1-verdict-cloud-20260921/` | 6.1 GB | Passes 1–3b: `ledger/`, `results/` (one tar.zst per run), extracted `runs/`, node logs, controller state and logs, `census/` (summarizer tables), `pass2/ pass3/ pass3b/` with the same layout |
| `erdos85-sat49/h1-verdict-pilot-20260921-claude/` and `…-claude-monitor/` | small | The 24-root Mac pilot run directory and its resource monitors plus gate-input audit |
| `erdos85-sat49/h1-verdict-pilot-20260916-sol2/` | 52 MB | The interrupted 2026-09-16 pilot (disk emergency), kept as evidence |
| `erdos85-sat49/h1-cube-pass4-20260926/` | 131 MB | Pass 4: base CNF and materializer receipt, abandoned fixed split `run-k5/`, adaptive tree `run-adaptive/` (per-node receipts and solver logs) |
| `erdos85-sat49/h1-gap34-20260927/` | 168 MB+ | The 34 outside-frozen capacity-gap slots (three shards) |
| `erdos85-sat49/h1-capacity-gap-canary-20260916-…/` | small | One input canary for the 34-slot adapter |

## Result A, H1 certificate campaign of 2026-08 (manuscript: cost-to-verify; historical overlay)

| Directory | Size | Contents |
|---|---:|---|
| `erdos85-sat49/remote-sweeps/` | 410 GB | Synced sweep outputs of the AWS solver fleets (coordinator and spot hosts): verified certificates, verdicts, models, logs |
| `erdos85-sat49/cert-root/` | 159 GB | Certificate root: compact LRAT certificates and index for the H1 capacity grid |
| `erdos85-sat49/campaign-20260825.noindex/` | 116 GB | Host campaign state: `ledger/` (`h1.ledger` and friends), `h1fleet/` freight incl. the pinned emitter `v2cnf`, cube job manifests, H7 grid scripts |
| `erdos85-sat49/v2-lrat/`, `strata-lrat/`, `v2-tier1-work/` | 57 GB, 8.6 GB, 2.5 GB | LRAT proofs and working sets of the earlier certificate tiers |
| `erdos85-sat49/h1-profile1-all-even-reciprocal-5/`, `h1-profile2-reciprocal-78/`, `p2-reciprocal/` | 5.6 GB, 46 GB, 95 MB | Per-profile H1 solve and certificate outputs |
| `erdos85-sat49/overlay-snap-ad0b/`, `overlay-fable-3b71/` | 1.5 GB each | Compiled Lean overlays used for cold-integration verification of generated modules |
| `erdos85-sat49/h1-orbit-inventory*.jsonl`, `h1-identity-20260916/` | small | Orbit and CNF identity inventories |

## Result A, strata H3 / H5 / H7 (manuscript: evidence table rows H3/H5, H7; `H7_CLOSURE_20260915.md`)

| Directory | Size | Contents |
|---|---:|---|
| `erdos85-sat49/h3-lean-exact/`, `h3-dist1-b1c1/` | 384 MB, small | H3 exact inputs and receipts |
| `erdos85-sat49/h7-canonical/`, `h7-canonical-solve/`, `h7-receipts/`, `h7-recovery-F7.*`, `h7-portfolio.*` | 390 MB, 11 GB, 32 MB, 156 MB, 29 MB | H7 canonical instances, solves, banked receipt shards (> 10 MB shards live here, not in git) |
| `erdos85-sat49/small-high-canonical-audit/`, `family/`, `t3_*`, `t4_*` | ≤ 200 MB each | Small-high (H3/H5) canonical CNFs, DRATs and audits |

## Theorem B side and negative map (manuscript: §0 negative map, Cayley census)

| Directory | Size | Contents |
|---|---:|---|
| `erdos85-cayley-sidon/` | 1.9 GB | Cayley/Sidon census inputs and outputs (orders 80/120/168) |
| `erdos85-zerolayer/` | 51 GB | Zero-layer / plane-order probes |
| `erdos85-order64-fixedk/`, `-percell-d/`, `-ten-six/` | ≤ 200 MB | Order-64 (q = 8) probes, PARKED by board #30 |
| `erdos85-sat49/deepsix-scout/`, `migration-canary/` | ≤ 400 MB | Fleet scouting and migration canaries |

## Process evidence (not cited by the paper)

| Directory | Size | Contents |
|---|---:|---|
| `erdos85-pilot8-*`, `erdos85-conflict-v6-bootstrap-*`, `erdos85-ledger4*-sol1-*`, `erdos85-round113-sol1-private-*` | 26 GB total | Sol seats' private working sets from 2026-09-08/09 |
| `recovered-private-tmp-20260816/` | 27 GB | Recovery of `/private/tmp` after the 2026-08-16 incident |

## Home-directory scratch (`~/lean-genius-*`, 117 folders, 70 GB, punchlist E2)

Review folders of the Sol seats and claude from 2026-09-08 to 09-16; about 90 percent of their
files are byte-identical copies in the integration bank. Move to `attic/` here rather than delete.
