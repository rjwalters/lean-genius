# Bounded precompiled-runtime feasibility probe

This diagnostic compares two ways of evaluating the same standalone Lean
phase-two traversal: normal `native_decide`, and `native_decide` after loading
the runtime's generated C as a Lean plugin. It supplies no production graph
exclusion or equivalence theorem.

`H3NativeRuntime.lean` contains 45 executable declarations copied verbatim
from the current H3 triple Engine, Bridge and Split sources. `SOURCE.json`
records their original locations and hashes, plus the production source
hashes. The standalone file imports Std rather than Mathlib. It omits phase
three and all soundness proofs. `H3NativeProbe.lean` uses the same bucket-zero
phase-two traversal expression as the earlier `PhaseTwoOnly.lean` diagnostic.

Precompiling the original Engine directly would require its Mathlib import's
native library. Lake's module `dynlib` facet recursively fetches imported
library shared targets; the existing Engine C initializer explicitly calls
`initialize_mathlib_Mathlib`. This standalone probe avoids that large build.
It does not alter generated C, substitute initializers, or change any
production declaration.

`run_probe.py` runs only inside the existing cloud Lean image. It checks the
source hashes, stages uniquely named files, compiles the runtime to Lean/C,
builds a shared library with `leanc`, and evaluates the same probe with and
without the plugin. Stage caps are 60 + 60 + 90 + 90 seconds. The outer job
is capped at six minutes, two CPUs and 16 GiB. Logs and timing receipts stay
under `attempt1`; intermediates remain available for diagnosis.

No benchmark result is asserted until the job terminates and its evidence
is reviewed. Even a successful copied-runtime benchmark must be followed by
a sound production refactor before it can supply new exclusion credit.

## Attempt 1

Job `20261008T114617-erdos85__h3-triple-formal-20261007-466599` at
`301cc8b1c20237b7e36dc5f2440659678cb76416` exited 1. The standalone runtime
compiled in 1.57 seconds and its shared library in 1.02 seconds. The plain
traversal theorem compiled in 61.39 seconds with the expected two standard
axioms and its own native-decide axiom. Plugin evaluation did not begin:
the invocation incorrectly used `:` between the library path and initializer.
Lean 4.31's `Shell.lean` expects `--plugin=file=fn`.

`evidence1` retains this failed attempt. No plugin timing or speedup is
claimed. `run_plugin.py` reuses the exact successful runtime objects and
baseline, fixes the CLI separator, and compiles the library with
`-DLEAN_EXPORTING`, matching Lake's exported-object convention in
`Lake/Build/Module.lean`. It checks the initializer's exported symbol before
running one 90-second-capped plugin evaluation; the library compile cap is
60 seconds and the outer job cap is three minutes.
