# Consume both verified deficient pilots

Status: **cloud PASS and independently audited; 1,552 rejection hypotheses remain**.

`Deficient1552.lean` imports the audited `Deficient1553` reduction and the
verified U369/R11 rejection. It erases that pair from the remaining census
and connects the actual-graph witness to a set of 1,552 pairs. Its exclusion
theorem still requires rejection of every remaining pair. It does not close
the deficient H3 branch.

The first three exports (membership, count, input identity) use only
standard axioms. The fourth uses the existing U369/R11 native axiom; the
last two use exactly the existing U26/R2 and U369/R11 native axioms, together
with standard axioms. No new native search is part of this build.

`check.py` runs only in cloud Docker, from `proofs/`. It validates the full
203-module deficient prerequisite, the prior reduction's source, object,
log and command, the original membership objects, and both audited pilot
receipts. It refuses changed imported objects and refuses to target their
modules in a dependency build. It compiles only `Deficient1552` after the
library dependency check, then revalidates all prerequisites. The output
directory must be fresh. There is no automatic retry.

Pass `--prerequisites` for the original deficient reduction's prerequisite
directory, `--prior-build` for its successful `cloud-second` output,
`--second-object` for the hash-verified U369/R11 certificate object, and
`--output` for a new directory. The two census branches' import paths must
remain separate. The generated output passed independent source, object, log, receipt,
command, prerequisite, and exact-axiom auditing. `audit.py` performs the
read-only cloud-host audit, and `evidence/AUDIT.json` retains its PASS.

Cloud host prerequisite validation passed before submission. `staging.json`
records the U369/R11 object hash, copied bytes, and both audited receipt
hashes. The live FullU3/R3 job uses a different certificate object; the
U369/R11 source object was read only and hashed before and after copying.
Local checks passed for Python syntax, CLI loading, and refusal to run Lean
on the host. Those staging checks preceded the successful Lean build.

Job `20261008T063932-erdos85__h3-triple-formal-20261007-267864`
completed with exit zero at 06:40:49 UTC, at commit `c681798645dacbcd87e4e47eb3bc8661a5c7964b`,
with 16 GiB, one Lake thread, and a 15-minute cap.

Compilation took 26.954 seconds wall time, 69.999 seconds user CPU, and
8,777,188 KiB maximum RSS. The six exact reports match the expected trust
sets above. Sources, logs, individual receipt, raw job log, and independent
audit are retained in `evidence/`; compiled objects remain on the cloud.
RUN SHA-256: `017c494229d89f19295fef81e8b1d50a7571376eadf79ab53db310beb2d8bf26`.
