# Deficient census after the U26/R2 pilot

Status: **cloud check submitted; not yet a passing proof receipt**.

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
