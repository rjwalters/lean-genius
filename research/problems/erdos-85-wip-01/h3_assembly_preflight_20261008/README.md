# H3 conditional assembly preflight

Prepared for a bounded cloud compile. This checks the planned 384-case
composition with every native premise supplied as an explicit hypothesis.
It proves no new Boolean result and does not close the H3 triple cell.

`verify_source.py` checks an exact transformation from the immutable planned
production cell: replace the part imports with the soundness-bridge import,
use a distinct namespace, add 384 explicit parameters to each theorem, and
pass those parameters to the assembled-parts theorem. Case branches and
both bridge applications otherwise remain unchanged.

`run.py` uses the existing cloud builder with one Lean worker, 16 GiB,
a two-CPU quota, a 90-second compiler cap and a three-minute outer cap.
It checks all four audited prerequisite source/object hashes before and
after the compile, stages one temporary source, and retains the output.
No shared-library compilation or native search is involved.

`capture.py --job JOB --commit FULL_COMMIT` checks the terminal job, pinned
source, resource limits, prerequisites, raw axiom reports, compiled object
hash and creation time. The exports may use only the standard logical
axioms. All 384 Boolean premises remain explicit assumptions in the types.
Even a successful preflight does not verify production part imports or
remove the need to build and audit the final unconditional cell module.
