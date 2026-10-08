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
