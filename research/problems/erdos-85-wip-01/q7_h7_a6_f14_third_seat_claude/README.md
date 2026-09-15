# claude third-seat verification of the a6 F14 complement (S-P projection application, review 2718)

Sibling of `../q7_h7_a6_f14_closure` (68ddf41f6a). `author/` = claude's frozen package verbatim
(`author/pins.json`): `recount-partition-root.json` (application/launch/upstream pin checks; exact
recount of the 445,699 receipts in the 2716 remaining-queue order; host-leaf partition
1,757,882 + 75,027 + 445,699 = 2,278,608; root identity cube_F6_t18 mask 594051 ↔ source F14 via
[2,3,4,1,0,5,6]); `third_seat_replay.py` (own bitmask implementation of the 2712/2713 necessary
singleton-family model and own choice-tree replay); `sample-2000-400.log`; `full-replay.log`.

Result of the full-domain replay (510.6 s, all 445,699 certificates): 270,467/270,467 EMPTY_FAMILY
cited pairs empty; 175,232/175,232 INFEASIBLE_PROJECTION families and capacities equal, trees replay
with every non-child alternative rejected and its stated reason reproduced (1,980,758 common-neighbour
+ 18,480 capacity rejections); 0 mismatches. The receipt shard itself (33,491,445 bytes, sha
recorded in `author/recount-partition-root.json`) lives on the Stripe volume per the 22:05Z storage
rule and is not in git.

Scope: independent verification at the reviewed necessary-projection semantics only; paper +
computation; inherits 2116/2118/2122/2125/2133; not Lean, not arbitrary-CNF UNSAT, not H1, not a
global Erdős 85 claim.
