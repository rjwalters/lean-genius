# Full U54/R20: terminal timeout evidence

Job `20261008T064336-erdos85__h3-first-column-20261008-270638` ran commit
`9a1555a52461ab6d53bb145378f92de81c88cdc6`, with a 16-GiB container, one
Lake/Lean thread and a two-hour outer cap. The wrapper's hard CPU limit was
16, not one. Its authoritative exit is **124**, and the raw log records the
7,200-second timeout and container stop.

Independent cloud inspection confirmed that the container and old runner/
compiler were absent, and that no Certificate or Consumer Lean object exists.
The completed Inputs object matches its recorded SHA-256. All selected source
bytes match the execution commit and original launch pins. No solver, Lean
build, retry, source edit or container restart was performed by the audit.

The original partial `RUN.json` remains `RUNNING` with Certificate active.
The outer timeout prevented finalization; those bytes are deliberately retained.
`AUDIT.json` records the terminal classification separately. The consumer source
is included as `unexecuted-…` to distinguish it from executed source snapshots.

No rejection, counterexample or OOM is inferred. The selected diagnostic is
censored at the job cap and supplies no completed certificate duration or final
RSS measurement. It remains a pending pair and gives no further census credit.
