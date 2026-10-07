# Checking the H1 stratum of the Erdős 85 order-49 drop yourself

The paper's upper bound at order 49 reduces, in Lean, the one-high stratum H1 to 13,351 SAT formulas
(`orderFortyNineStratumExcluded_one_of_capacityInventory_checked` in
`proofs/Proofs/Erdos85OneHighV2CapacityCover.lean`). We checked every one of them with the
CakeML-verified LRAT checker `cake_lpr`. This page lets you repeat any part of that check on your own
AWS machine. Nothing needs to be downloaded to your computer.

## What you can check

| Set | Orbits | How `e85-check` checks it | Your cost |
|---|---:|---|---|
| Certificate bank | 12,094 | stream our published LRAT proof into cake_lpr | ~minutes per 100-row sample; whole bank ≈ 400 checker-hours (≈ $20 on spot) |
| Census + historical | 1,160 + 96 | re-solve with the pinned CaDiCaL and stream the proof into cake_lpr; for the 1,157 census orbits we solved on Linux, your proof's sha256 must also equal ours (the 96 historical orbits and 3 census orbits finished on macOS have no comparable Linux proof hash, so for them it is a fresh cake_lpr check) | small rows take minutes; the whole set ≈ 3,500 CPU-hours |
| Hardest orbit `h1_81494a6ef36d3ec9` | 1 (36 cubes) | rebuild each cube CNF, solve, cake_lpr; the cover is a Lean lemma | ≈ 8 CPU-hours |

For every row the formula is regenerated from the orbit's table by the pinned emitter `v2cnf` (a
compiled Lean program, sha256 `4bd9604c…`) inside the pinned Lean image, and must hash to the
published value before any proof is checked. A row passes only if cake_lpr prints `s VERIFIED UNSAT`.
**cake_lpr exits with status 0 even when a check fails** — never trust the exit code alone.

## Steps

1. **Launch the public checker AMI** in **us-east-1**: `ami-05697724475f2e748`
   (`erdos85-h1-checker-20261006`, Amazon Linux 2023, arm64). Use a Graviton instance with enough
   memory — `r7g.2xlarge` (64 GiB) for samples, `r7g.16xlarge` for the whole bank. A 40 GB root
   volume is enough: proofs are streamed, never stored.
2. **Give the instance read access to the certificate bucket.** It is a *Requester Pays* bucket:
   requests must be authenticated and you pay your own (in-region: free) transfer. Attach an
   instance role whose policy allows `s3:GetObject` on
   `arn:aws:s3:::2am-erdos85-certs/sat49/campaign-20260825/h1/*` and
   `arn:aws:s3:::2am-erdos85-certs/public/erdos85-h1-checker-kit/*`.
3. **Run checks** (as `ec2-user`; results go to `/scratch/e85-results/`):
   ```
   e85-check bank --sample 100          # or --all, or --ids tag1,tag2
   e85-check census --sample 5          # default: orbits whose original solve took ≤ 1 h
   e85-check cube --leaves 31,51         # or omit --leaves for all 36
   e85-check summary
   ```
4. **Read the result.** `summary` prints a tally:
   - `bank: PASS` — cake_lpr verified our proof and its sha256 equals the published receipt.
   - `census: PASS, proof byte-identical to published` — your solver run reproduced our exact proof
     (expected for the 1,157 census orbits we solved on Linux).
   - `census: PASS (proof differs …)` — the 3 census orbits we finished on a macOS build of CaDiCaL;
     your Linux proof is a different, equally valid proof, checked fresh by cake_lpr.
   - `census: PASS (historical orbit: no published proof hash …)` — the 96 historical orbits; our
     certificates for them came from archived Kissat DRAT, so there is no CaDiCaL proof hash to match.
   - `cube: CERTIFIED` per leaf.
   Anything else (`CHECK_FAILED`, `CNF_MISMATCH`, `HASH_MISMATCH`) is a real discrepancy — please tell us.

Without the AMI: on a fresh Amazon Linux 2023 arm64 instance run
`E85_COMMIT=<commit> bash research/problems/erdos-85-wip-01/h1_checker_kit/ami_setup.sh`, which installs
exactly what the AMI contains (and verifies the checker kit against its `MANIFEST.sha256`).

## What a pass establishes, and what it does not

A pass means: the formula your machine regenerated from the orbit's table is unsatisfiable, as certified
by a formally verified checker. That these formulas are exactly the ones Lean's cover theorem asks about
rests on the compiled emitter; that their unsatisfiability excludes H1 is the Lean theorem above (which
uses `native_decide` for a finite enumeration). The external checks are not themselves Lean proofs.
The other strata (H3, H5, H7) and the rest of the argument are described in the paper.

## Files

- Checker kit (Requester Pays): `s3://2am-erdos85-certs/public/erdos85-h1-checker-kit/` — manifests,
  orbit tables, our receipts, pinned binaries, `MANIFEST.sha256`.
- Bank proofs (Requester Pays): `s3://2am-erdos85-certs/sat49/campaign-20260825/h1/<tag>.compact.lrat.gz`.
- Receipts in this repository: `h1_bank_check_20261006/receipts/`, `h1_cert_full_20261001/receipts/`.
- Tooling: `h1_checker_kit/` (`e85-check`, `cube_check.py`, `ami_setup.sh`).
