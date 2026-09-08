# No neighbor-only repair after deleting a polarity endpoint vertex

2026-09-08, codex-sol-1. Prose proof and finite calibration; not Lean.
This closes the construction probe announced in Squad message 40748.
Independent review: Codex subagent `review_endpoint` checked the uniform
argument and separately enumerated the q=2,4,8 controls on 2026-09-08.

Let q be an even prime power, and let H be the q-regular graph on q²+1
vertices from `BINARY_POST_SQUARE_INTERVAL_CONSTRUCTION.md`. For **every**
vertex v of H, deleting v and adding edges only among its q neighbors
cannot yield a C4-free graph of minimum degree q on q² vertices.
In fact, every candidate added edge already creates a C4 by itself.

## Uniform proof for q ≥ 4

Use the looped dot-product polarity matrix B of PG(2,F_q). Polar lines
intersect uniquely, so B²=qI+J; every row sum is q+1, so
B³=qB+(q+1)J. Choose an absolute point a, with nucleus c, and delete
S={a} ∪ (N(a) minus {c}), then omit loops to obtain H.
Every retained vertex loses exactly one incidence from B: a retained
absolute point loses its loop and no neighbor, while a retained
nonabsolute point loses one neighbor in S. These degree facts are proved
in the companion construction note.

Fix v in H and distinct nonadjacent x,y in N_H(v). Since H is induced
apart from loop removal, B_xy=0. There are exactly q+1 loop-allowed
three-step walks x,u,w,y in the host. Discard the following walks:

1. Those whose first incidence is the unique incidence at x missing in H.
   If its other endpoint is d, their number is (B²)_dy=1: d≠y because
   B_xy=0.
2. Those whose last incidence is the unique incidence at y missing in H.
   The same argument bounds their number by 1.
3. Those with u=v. Their number is (B²)_vy=1, since v≠y.
4. Those with w=v. Their number is (B²)_xv=1, since x≠v.

These classes may overlap; their union has size at most 4. Any remaining
walk has u,w retained and different from v, and its first and last edges
are edges of H. Its middle incidence is also an edge of H unless u=w.
But u=w would make u a common host neighbor of x,y. That neighbor is
uniquely v, by B²_xy=1 and x~v~y, already discarded. Thus there is no
middle loop. Nor can u=y or w=x, because x,y are nonadjacent. The four
vertices are distinct, so the remaining walks are simple three-edge
paths in H-v.

Consequently every candidate new edge xy closes at least q-3 such paths
into C4s. For q≥4 this is positive. Every neighbor of v has degree q-1
after deletion, so some edge must be added to repair the minimum degree;
none is admissible. This proves the claim.

## Small endpoint and verification

For q=2, H is a simple C4-free 2-regular graph on five vertices, hence C5.
Deleting any vertex leaves P4, whose only possible neighbor-repair edge
closes a C4. The conclusion therefore holds for all even prime powers.

Run `python3 research/problems/erdos-85-wip-01/verify_binary_endpoint_vertex_repair.py`.
The checker constructs the host over F_2, F_4, F_8, F_16; checks B² and
the single lost incidence property; and checks every deleted vertex and
every nonedge among its deficient neighbors. It independently counts
simple three-edge paths and verifies an explicit C4 for each proposed
edge. It uses one chosen absolute point per field; the proof allows any.
The respective minimum path counts are 1, 2, 5, 13. These finite counts
are calibration, not a replacement for the uniform proof.

## Consequence and remaining gap

The q²+1 endpoint cannot be converted to a square-order witness by this
specific one-vertex deletion and neighbor-only edge addition. Repairs
that remove other edges or alter other vertices are not excluded.
This does not prove A-REG, classify arbitrary square-order graphs, or
resolve Erdős 85. This construction route is now closed; further path
count refinements within it would not advance the root.
