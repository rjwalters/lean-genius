# One retained H7 cover pilot

Status: **prepared; production and Lean check not yet run**.

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

Success should introduce one native-decision axiom for the concrete checker
computation, reported explicitly on both exports. It proves only this cover;
all corresponding leaf certificates remain required for the parent cube.
Wall time, CPU time, peak RSS, source/object/log hashes, and exact axiom sets
are retained. An external check alone is not a passing Lean receipt.
