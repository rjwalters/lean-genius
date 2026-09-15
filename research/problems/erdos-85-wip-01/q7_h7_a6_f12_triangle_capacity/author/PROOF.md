# Triangle-conditioned high-colour capacity

## Exact support count

Use the accepted H7 host-branch hypotheses: seven independent high vertices of degree eight, all other vertices of degree seven, and a C4-free simple graph on 49 vertices. For a high vertex h, every one of its eight neighbours is low and has six further neighbours. These 8*6=48 length-two walks have distinct endpoints: a repeated endpoint would create a four-cycle. None ends at h, so every other vertex has exactly one common neighbour with h.

Take a pair vertex u whose saved degree is two. Its known neighbours are both high; their high supports are empty because the high vertices are independent. Its five further neighbours are active vertices, since high and empty neighbourhoods are already complete. If s of them are singleton vertices and p are pair vertices, then s+p=5. The preceding two-walk count says their high supports partition all seven high vertices, so s+2p=7. Hence s=3 and p=2.

The three singleton vertices must form a triangle in the compatibility graph of the previous criterion (review 2705). For each such triangle, its three disjoint high supports leave four high colours uncovered. Each of the two new pair neighbours must have its support inside these four colours, and must have no known common neighbour with any known neighbour of u or with any of the selected singleton vertices. Any violation would already create a four-cycle through u.

Make a graph on the four remaining high colours with one edge for every eligible pair vertex. The two required pair vertices must give a two-edge matching. If no two eligible support edges are disjoint, this triangle cannot extend. If this obstruction holds for every eligible singleton triangle at one degree-two pair vertex u, the entire host branch is impossible.

This test ignores possible four-cycles between the two new pair neighbours. It generates neither complete residual rows nor ARC propagation. It is a necessary colour-capacity condition; surviving it makes no feasibility claim.

## Scope

One bounded probe applies this criterion to the exact 218 cases left by review 2705. The original capped F12 residual run remains immutable. Any surviving cases will be retained explicitly. Neither this mathematical argument nor the computational checks constitute a Lean/kernel proof or establish the global Erdős 85 statement.

The probe completed in 0.059 seconds and rejected 89 of 218 cases. Independent set-based verification checked 128 triangle-conditioned capacity cuts in 0.006 seconds. Exactly 129 cases remain; the composed negative count is 397105 of 397234, subject to peer review.
