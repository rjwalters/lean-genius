# Computational exclusion of the a7 F9 empty graph

F9 has edges 01, 02, 03, 12, 45, 46, 56: a triangle with a pendant edge, disjoint from another triangle. Under the accepted a7 empty-first normal form, its entire finite cover is negative.

Accepted 2116 contains all 39 F9 singleton-host bases in its COMPLETE portion, with 1,620 singleton-edge graphs. An independent core-first traversal reproduced all 1,620 exact graphs on these 39 bases (the supplementary source audit archived with the F9 high cover). No UNKNOWN or unvisited noncycle base was retried or reclassified.

Accepted 2121 covers the canonical high assignments: 148 singleton graphs have no assignment, and the other 1,472 have exactly 28,336 assignments. Accepted 2124 completely enumerates compatible pair-vertex empty hosts with sound optimistic singleton-row pruning: 3,545,834 rejected prefixes and 99,224 retained host leaves. All host calls were COMPLETE.

The one residual pass checked all 99,224 ordered host leaves. Exactly 97,540 have an empty complete residual row domain; the other 1,684 have an arc-consistency contradiction. There are no retained, UNKNOWN, or unvisited leaves. The pass took 12.735 seconds with original limits of 100,000 counted operations per leaf and 60 seconds aggregate. It reused byte-identical accepted 2117 batch and 2111 a7 native code. Full ARC events and compact ROW endpoints are preserved in receipts-000.jsonl.gz. verification.json checks the exact ordered source join and count totals without rerunning any search.

Sol3 independently reconstructed host masks from accepted 2124 and regenerated 156,480 domains with 185,314 rows using increasing active-vertex recursion. It replayed 2,688 atomic removal batches and 2,808 failed-support rows in 3.201 seconds. See its review-f9-residual artifacts and the final directed review for independent acceptance.

Together these stages exclude the entire a7 F9 shape at the computational and mathematical argument level. They do not exclude other noncycle shapes, a6, H7 as a whole, or H1, and are not a Lean kernel theorem or a solution of Erdős 85. The original capped frontier remains unchanged. All files preserve original absolute provenance paths; no search was restarted for this package.
