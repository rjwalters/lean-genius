# Cold project build preparation

Status: **prepared, not launched**. This is a proposed bounded verification
of the finite endpoint's entire 893-source project closure after publication
of the 13 packed H7 certificates and the corresponding relative-path patch.
It is not a new SAT campaign, and it does not discharge the H1/H7 UNSAT
hypotheses. It may use pinned Lean/Mathlib external package caches; it does
not claim to rebuild Lean or Mathlib from source.

## Inputs and isolation

`prepare.py` discovers the import closure independently, requires the same
893 module names as the accepted release manifest, and hashes every source,
every `include_str` file and the toolchain/Lake configuration. It refuses
remaining absolute include paths. Only the 13 positive-triple certificate
modules may differ from accepted sources, and only their include path may
change. The three expected headline axiom sets are bound to the accepted
plan hash (601, 607 and 604 axioms).

`run.py` defaults to read-only preflight. Execution requires the exact plan
SHA256 and separate spending authorization. It creates a new output directory
with an empty `lean/Proofs` package root, puts that root first in `LEAN_PATH`,
and never copies or links accepted project objects. Before compiling any
module it tries to import the endpoint: this must fail specifically because
the endpoint object in the fresh root does not exist. A successful import,
timeout or different error stops the run. This checks the Lean package-root
isolation on the actual toolchain, even if the builder's default volume was
seeded. A new dedicated empty build volume is still preferred; do not delete
or modify an existing accepted volume to prepare one.

Modules are compiled in dependency order with at most six Lean workers,
`-j1` each, inside the 110 GiB / 16 CPU container. Large H7 certificate
modules reserve 64 of the scheduler's 96 GiB reservation budget, so only one
can run at a time. The cgroup, not those reservations, enforces the actual
memory bound. The H3 Runtime C and shared plugin are rebuilt from source
before the 384 triple-part native searches use them. The plugin is not copied
from accepted artifacts.

Each process records its exact command, raw log, exit status, elapsed time
and output hashes. Any failure, source/artefact drift, STOP, signal or overall
deadline stops further scheduling and kills running process groups. The run
never retries or resumes into an existing output directory. It compares the
endpoint's printed axiom sets with the accepted sets and rehashes sources,
certificates and objects at the end. Success is deliberately
`COLD_PROJECT_BUILD_COMPLETE_PENDING_AUDIT`; a separate read-only audit must
accept the evidence before manuscript claims change.

## Cost and time estimate, 2026-10-11

The existing builder was confirmed stopped by `ec2 describe-instances`.
AWS Pricing `get-products` for Linux, shared tenancy, r7g.4xlarge, us-east-1
returned **$0.8568/hour**, effective 2026-10-01. The proposed outer cap is
10 hours; the runner stops at 35,400 seconds to leave shutdown/capture time.
Ten running hours cost $8.568 in instance compute. This excludes already
provisioned EBS, network/download charges and request charges.

Planning estimate: **6–10 hours, roughly $5.14–8.57 compute**, not a completion
guarantee. Retained measurements on this builder:

| Work | Evidence | Measured duration |
|---|---|---|
| 24 H3 pair parts | `h3_pair_completion_review_20261008/README.md` | 31,238 summed process wall seconds (~8.68 worker-hours) |
| 40 H5 search parts | `h5_terminal_review_20261008/terminal-evidence1/AUDIT.json` | 60,371 summed process wall seconds (~16.77 worker-hours) |
| 384 H3 triple parts | sample/campaign/sweep AUDIT.json and residual RUN.json | 6,149.30 summed process wall seconds (~1.71 worker-hours), fresh runtime plugin |
| H7 positive-triple certificate build | `lean_builder/README.md`, measured Oct 7/8 | 2 h 35 min; largest certificate 8,149 s; reported peak ~20 GB |

These sums are **not CPU-hour measurements**. Six search workers give about
4.25 ideal hours for the pair/H5 work before dependency overhead. The largest
H7 certificate is a serial critical path. Dependency elaboration, memory
contention and scheduling can increase the total. The 10-hour cap may stop
an incomplete build; it does not license extensions, retries or resizing.

## Preparation and review

After the publication/path patch is merged and the 13 hash-verified files are
present at the relative include locations, generate a new plan (no Lean):

```sh
AWS_PROFILE=2am-admin proofs/scripts/fetch-h7-certificates.sh
python3 -B research/problems/erdos-85-wip-01/release_cold_build_20261011/prepare.py --output /tmp/erdos85-cold-plan.json
python3 -B -m unittest discover -s research/problems/erdos-85-wip-01/release_cold_build_20261011 -p 'test_*.py' -v
```

The builder must also run the fetch script before its input preflight; its
instance role needs requester-pays GetObject access. Do not assume the
builder's older absolute-path copies satisfy the new relative includes.

Review the plan, commit it with the runner, then pin that execution commit.
Prepare the cloud job using the existing builder with `--full --mem 110
--threads 6 --timeout 10h`. It must run `lake env python3 -B` on `run.py`
from `/workspace/proofs`, with the committed plan and a fresh output path.
First omit `--execute-plan` for preflight. An approved execution then adds
`--execute-plan <reviewed-plan-sha256>`. Do not invoke e85-remote merely to
inspect old logs while the builder is stopped: some commands auto-start it.

The normal builder watchdog has a UTC-day uptime limit. Before launch check
remaining uptime against the requested outer cap; do not silently raise the
wall or let the watchdog invalidate the estimate. Stop the host promptly
when this bounded attempt is terminal. Preserve failed evidence as well as
successful evidence. No local Lean build is needed for preparation/tests.

After a terminal success, run `audit.py --plan <plan.json> --output <run-output>`
and retain its JSON output. It checks every source, certificate, raw log,
compile command, dependency order, object identity and endpoint axiom set.
Its verification can run against a copied output bundle (the original command
paths remain in the receipts). A human/peer review of the runner and receipts
remains distinct from this author-written deterministic checker.

The current tests exercise nested-comment parsing, exact closure scope,
cycles, axiom admissions/duplicates, failed exits, STOP/timeouts, output
reuse refusal and scheduler reservations using only text fixtures and Python
children. Actual compilation, runtime-plugin behavior and cache isolation
remain cloud validation obligations, not claims established by these tests.
