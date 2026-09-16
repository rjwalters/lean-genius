# Host H1 scaling draft

This is a dispatch design, not an execution approval or a verdict. The live
24-case pilot continues under the previously reviewed four-worker wrapper.

The frozen H1 residual inventory has 1,161 IDs. The scaled route excludes the
24 exact pilot IDs and selects the other 1,137; an auditor combines receipts
from both runs. Capped UNKNOWN cases remain open and are not retried
automatically. The 96 historical-overlay and 34 outside-frozen gaps use their
separate reviewed routes.

`dispatch_scaled.py` can use at most 24 solver worker slots, with at most four
simultaneous native Docker input preparations. It reuses the config-pinned
Phase B materializer and verdict runner. Every UNSAT needs Kissat and CaDiCaL
under separate 14,400-second caps. Primary-only UNSAT is an error. The output
uses the existing Phase B receipt schema so the reviewed gap auditor can read
it; `inventory_all_unsat` stays false because the run is a subset of the
1,416-case index.

A non-pilot execution requires a separately banked scaling gate. The gate
binds the exact completed 24-case pilot results, the resource-monitor bytes,
the frozen config hash, and approved worker/materializer limits. The gate is
not available while the pilot is live. This source revision has no approved
gate hash, so execution fails closed even if someone banks a self-declared
gate. A later reviewed source revision must pin the gate's exact SHA-256 after
auditing pilot receipts and resource profile. The scaled route has no pilot
override; the existing pilot keeps its separate reviewed dispatcher. The host
target remains zero cloud spend; this code does not start AWS or request proof
logging.

For a planning illustration only, 1,137 roots at the historical completed
Kissat mean of 4,539 seconds would occupy 1,433 host-hours of primary solve
time, or about 2.5 days at 24 continuously busy workers. That completed
sample is selected by finish and does not estimate the gap tail; CaDiCaL time
and cap hits add to the timeline. The live pilot, not this arithmetic, must
set the gate limits.
