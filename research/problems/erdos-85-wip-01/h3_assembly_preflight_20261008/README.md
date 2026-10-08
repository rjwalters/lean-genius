# H3 conditional assembly preflight

The bounded cloud compile and independent artifact audit passed. This checks the planned 384-case
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

## Verified result

Job `20261008T122748-erdos85__h3-triple-formal-20261007-492954`, pinned to
`1e7db250cbfc656e4e26afcd877abcc1e0545e40`, exited zero.
Both conditional exclusion exports have exactly `propext`, `Classical.choice`
and `Quot.sound` as their printed axioms. The 384 native results are explicit
parameters, so they do not appear as global axioms.

`evidence1/AUDIT.json` records the independent source, prerequisite, resource,
log, object and timestamp checks. The exact 384-case composition and its
bridge applications elaborate successfully at the planned recursion limit.
The five accepted native residues remain unchanged; 379 are still unresolved.
A final unconditional build with all production imports remains necessary.

Compiler elapsed time: 7.624 seconds. Retained object: 768408 bytes; SHA-256 `2f4c644c5ff9a32d4e1a3f798bbb9a38d894d9be941672e72c5f7ed89beca1dc`.
