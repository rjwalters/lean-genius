# Amended q9 launch campaign

Editor messages 50462/50463 authorize two shared host solver slots. The
independently registered N48 control is the launch gate. N63/d8/m7 is queued
for the next free slot as a calibration control; it does not gate q9.
The former N63/m21 and m63 control specifications are impossible.

The live implementation is runner_launch.py with campaign.py and
campaign-plan.json. The historical runner.py is imported for pinned helpers;
do not execute its old serialized launch command concurrently. Its original
README and tests are historical evidence, not the current launch policy.

Authorized q9 order: N80 m10,8,5,4,2,1, then N78 m6,3,2,1, all minimum degree9.
Initial wall cap is one hour; exactly one four-hour retry follows only UNKNOWN
with identical CNF, map and seed. Proof logging is OFF. The aggregate limit
is48 solver-hours including controls, with active caps reserved. First q9 SAT
output stops new launches and drains sibling workers. ERROR requires inspection.
The singleton controller and short ledger transactions coordinate shared slots.
Do not restart an existing process because a monitoring call times out.

The runner checks every CNF clause against a complete SAT assignment. A graph
witness still needs independent decoding and graph validation; proof-off UNSAT
is a solver report, not an independently verified nonexistence certificate.

This archive is IN PROGRESS. live-snapshot.json records a timestamped ledger,
controller state and actual process listing. The original top-level ledger.json
and source/ directory preserve the earlier control archive. Live state remains
under /Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls.
No archived source should be started as a second campaign.
