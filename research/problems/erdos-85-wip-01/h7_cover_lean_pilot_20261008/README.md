# One retained H7 cover pilot

Status: **external certificate PASS; optional Lean replay PASS**.

The producer job `20261008T053625-erdos85__h7-lrat-adapter-20261008-228680`
exited successfully. CaDiCaL produced the proof in 3.26 seconds and cake_lpr
verified it in 1.91 seconds. The 9,870,017-byte proof, its packed copy, and
the exact CNF are retained outside Git at the path recorded in
`production-evidence/artifact-index.json`; all seven artifact hashes were
checked after retrieval. Small receipts, source, and raw logs are retained
in `production-evidence/`.

The separate cloud Lean job is recorded in `lean-launch.json`. It exited
zero at 05:49:19 UTC within its 16-GiB memory limit and ten-minute cap.
The concrete module used 577.113 seconds wall time, 575.686 seconds user CPU,
and 7,700,740 KiB peak RSS. `lean-evidence/AUDIT.json` records the independent
source, object, log, receipt, and axiom-report checks. Producer receipts
retain their historical `EXTERNAL_PASS_LEAN_PENDING` status; the later Lean
result is recorded separately.

This optional strengthening targets only the depth-three F6/t5 cover CNF,
SHA-256 `1cacfbaac58d988d4396fdf24c7169d1b6d70a8f22707ad83de2e66944d995bb`.
It is separate from the paper's external check-then-discard H7 campaign.
No leaf replay campaign is proposed or launched here.

`produce.py` reconstructs this one cover from pinned campaign inputs and
requires the prior verified hash. On the existing cloud host it runs the
pinned CaDiCaL binary with a 120-second solver cap, a 180-second process wall
cap, and a 64-MiB per-file limit. It requires UNSAT and then the pinned
cake_lpr checker's exact verified-UNSAT line. It retains the CNF, proof,
logs, timing/memory receipt, reversible seven-bit packing, and generated
Lean source. No automatic retry is performed. Five small packing roundtrips
were checked locally; no solver or Lean calculation ran locally.

`check.py` then runs inside cloud Docker with a fresh output directory. It
checks all producer hashes and the exact generated source before compiling.
The certificate is checked against the cover CNF constructed inside Lean,
using the existing preparation, extension-padding, and standard LRAT checker.
The second export applies the verified HsbLrat adapter to obtain
`SevenHighT0CanonicalHsbCoverChecked 3 6 5` for its generated leaf list.

Both exports report exactly the standard three axioms and
`Erdos85.HsbCoverPilot.F6T5.check._native.native_decide.ax_1_1` for the concrete
checker computation. The result proves only this cover;
all corresponding leaf certificates remain required for the parent cube.
Wall time, CPU time, peak RSS, source/object/log hashes, and exact axiom sets
are retained. An external check alone is not a passing Lean receipt.
