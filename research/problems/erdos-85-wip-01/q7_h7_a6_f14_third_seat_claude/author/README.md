# claude third-seat audit of the F14 S-P projection application packet (2026-09-15)

Independent implementation, no producer rerun, read-only on all Sol packages.

- `recount-partition-root.json`: application/launch/upstream pin checks; recount of `receipts-000.jsonl.gz`
  (exact order vs the 2716 repaired remaining queue); host-leaf partition identity
  1,757,882 + 75,027 + 445,699 = 2,278,608; root identity cube_F6_t18 (mask 594051) ↔ source F14
  through parent_to_source [2,3,4,1,0,5,6].
- `third_seat_replay.py`: own bitmask implementation of the reviewed 2712/2713 necessary
  singleton-family model and an own replay of INFEASIBLE_PROJECTION choice trees (capacity and
  |F∩F'|+savedCommon>1 rejections; every non-child alternative must be rejected and its stated reason
  reproduced). Run `python3 third_seat_replay.py 2000 400` (sample) or `... all` (full domain).
- `sample-2000-400.log`: seeded sample result. `full-replay.log`: full-domain result when terminal.

Scope: necessary graph projection only; paper + computation; not Lean, not arbitrary-CNF UNSAT,
not an H7-wide or Erdős 85 claim. The 2116/2118/2122/2125/2133 upstream premises are inherited.
