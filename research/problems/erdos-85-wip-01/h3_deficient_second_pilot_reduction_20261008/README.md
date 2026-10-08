# Consume both verified deficient pilots

Status: **source-only; cloud validation pending**.

`Deficient1552.lean` imports the audited `Deficient1553` reduction and the
verified U369/R11 rejection. It erases that pair from the remaining census
and connects the actual-graph witness to a set of 1,552 pairs. Its exclusion
theorem still requires rejection of every remaining pair. It does not close
the deficient H3 branch.

The first three exports (membership, count, input identity) must use only
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
remain separate. The generated output still needs independent source,
object, log, receipt, and exact-axiom auditing before a PASS is accepted.

Cloud host prerequisite validation passed before submission. `staging.json`
records the U369/R11 object hash, copied bytes, and both audited receipt
hashes. The live FullU3/R3 job uses a different certificate object; the
U369/R11 source object was read only and hashed before and after copying.
Local checks passed for Python syntax, CLI loading, and refusal to run Lean
on the host. No Lean proof result is claimed at this stage.
