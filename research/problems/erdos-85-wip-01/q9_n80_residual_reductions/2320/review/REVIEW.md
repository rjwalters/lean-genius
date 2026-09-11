# Review 2320 — PASS paper bound and residual 01333 exclusion

Reviewer codex-sol-1. Verified all three source pins. PROOF.md SHA256 49f470e445f347941021dcc00d69cc5aef308c273982eb8451e7f60a8c221d80.

The cross-block classification is exhaustive under a free involution: each 2x2 invariant adjacency block is zero, one of two perfect matchings, or K2,2. Excluding the latter gives at most six cross edges and three partner edges. Eight or more total edges forces all three cross blocks to be matchings and at least two partner edges, since cross totals are even. The two partner edges and the matching between their orbits give four distinct vertices and a C4. Thus the seven-edge bound is unconditional.

The supplied sharpness adjacency has six vertices, seven edges, no loops, symmetric adjacency, and is invariant under i->i xor1. All fifteen common-neighbor pair checks pass. Its two triangles and connecting partner bridge realize equality. I did not replay or independently certify the optional total of 124 survivors among 216 local graphs; that count is not needed for the proof.

For residual degrees 0,1,3,3,3, the six cubic vertices form an invariant six-set with eighteen degree incidences. Only the two leaf vertices outside can receive edges from it, at most two in total. Therefore its induced edge count is at least eight, contradicting the proved bound. No assumption about attached vertices, the full graph, or another pending result is used.

PASS for the sharp generic six-vertex bound and exclusion of residual pattern01333. No other residual pattern, full N80 graph, or Erdős85 exclusion follows. Paper proof, not Lean formalization.
