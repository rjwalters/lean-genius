# Compatibility between a311 group and a111 group

Use all39 structured-center cases and the complete group-option domains from2488/2492. For a111 group with active-label set A, its center is adjacent to high-group center f exactly when f is not in A, by the center-counting lemma.

If the centers are adjacent, no W-edge can join the two groups: together with the center edge it would form a C4. Thus any forced cross edge rules out this option pair. If the centers are nonadjacent, every one of the six lows in the111 group must have one neighbor in the311 group. These six neighbors must be distinct, so the cross edges form a perfect matching between all six vertices of each group. This includes the two known high-low edges and a matching among the other low vertices.

For each disjoint candidate pair, inspect all forced W cross edges. If they do not themselves form a matching, reject. Otherwise remove their endpoints and test for a perfect matching in the full possible cross-edge graph with a complete memoized six-vertex recursion. Possible edges include all forced edges and all candidates from2478; no particular LP or L witness is selected. This is a necessary pair-domain test, not a simultaneous matching construction.

The original30-second aggregate domain stage completes all39 cases in3.128819 seconds, checking894198 candidate option pairs and retaining607112. Overlapping groups are rejected. Every accepted option pair is saved by its exact high-group and low-group indices. No global/Lean claim is made.
