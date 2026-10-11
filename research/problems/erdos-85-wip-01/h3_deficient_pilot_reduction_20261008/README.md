# Deficient census after the U26/R2 pilot

Status: **cloud proof PASS; six exports independently audited**.

`Deficient1553.lean` consumes the independently verified U26/R2 rejection,
its census membership and representative identity, and the verified
`Deficient1554` witness theorem. It erases that pair from the retained census,
proves that 1,553 pairs remain, and preserves the same distinct joint witness,
cross-domain condition, and external block capacity condition at another pair.
Exclusion of the deficient branch still requires the other 1,553 rejections.

The six requested axiom reports separate the three membership/cardinality/input
lemmas from the three certificate-consuming theorems. The latter should inherit
only the existing U26/R2 native-decision axiom alongside the standard three.
No native search is repeated and no new rejection certificate is introduced.

`check.py` requires cloud Docker, a fresh output directory, the audited
203-module deficient census, and an isolated copy of four existing objects:
the membership proof, both of its input dependencies, and the U26/R2 certificate.
It checks their hashes against the retained audited receipts before and after
compilation. It retains complete logs, source, object hashes, six exact axiom
reports, and wall/CPU/RSS measurements. The two live cloud refs are unchanged.

Cloud job `20261008T050920-erdos85__h3-triple-formal-20261007-210533`
uses source `41efcf17a72`, 32 GiB, four Lake threads (one per direct Lean
compiler), and a 30-minute cap. The 614 prerequisite files were hash-checked
before and after copying. `launch.json` records the submission provenance.

The first launch exited 2 before Lean because root-owned staging directories
blocked checkout. Its follower log and failed receipt are retained. Ownership
was corrected only for this new package, and its three committed source files
were restored exactly. Retry `20261008T051053-erdos85__h3-triple-formal-20261007-212516`
uses the same proof/checker bytes at `11d4ba4b3b3`; `retry-launch.json` records
the bounded submission. No native search was repeated.

The retry completed its 9,026-job dependency build in 643.13 seconds, then
failed immediately on import: the isolated partial `Proofs/` directory
shadowed the complete library namespace in Lean search paths. Its failed
follower log is retained in `first-check.log`. The checker now places the
three audited pilot objects in the complete library directory (refusing any
different existing object), and copies the membership object into the new
output root. No proof source or native certificate is changed.

The corrected check passed in job
`20261008T052325-erdos85__h3-triple-formal-20261007-220726` at `6e44e57cd83`,
exit 0 at 05:24:11 UTC. The module took 27.307 seconds wall, 71.374 seconds
user CPU, and 8,489,972 KiB wait4 peak RSS. This was one compiler process with
`LEAN_NUM_THREADS=1`; the recorded CPU use is not a one-core wall-time estimate.
Warm dependencies took 6.643 seconds. `evidence/` retains the exact executed
source, complete compiler/dependency logs, receipts, and independent audit.
The three structural exports use exactly the standard three axioms; the
three certificate consumers add only the already verified U26/R2 native axiom.
All four reused object hashes match their audited evidence, and the resulting
object hash was separately read from the cloud. No native search was repeated.
The finite obligation count is now 1,553 on this deficient branch, conditional
on the remaining rejection hypotheses; this does not close H3.
