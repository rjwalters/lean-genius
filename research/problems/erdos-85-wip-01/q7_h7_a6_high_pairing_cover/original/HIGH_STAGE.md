# Complete a6 high-pairing cover

The single guarded pass used accepted2118 E/S projection and accepted2119 high-pairing code. All3284 labelled E/S graphs completed, with818836 canonical high assignments and no empty, UNKNOWN or unvisited cases. It used5869353recursive nodes and4.998seconds under100000per E/S graph and60seconds aggregate. The90MB compressed-artifact guard was not reached.

Each output identifies the original completion record and singleton-solution index plus F/X indices. Its11colours name the double-empty vertices7..17; single-empty vertices18..20 have fixed colours0..2. The four double/double high names3..6 are ordered by their least singleton index. Mixed pair nonadjacency and disjoint-neighbour criteria hold; double/double adjacency is allowed.

Independent verification checks every output for validity, canonical naming and uniqueness. For each E/S graph a separate largest-remaining-vertex matching dynamic program counts all legal completions over the mixed assignments. Count equality therefore proves exact coverage. All818836 outputs agree,739501states total,max660per graph,4.306seconds; no caps. Source bytes and live prerequisite snapshots are retained.

This is a high-pairing cover only. No pair-empty host assignments or remaining low edges have been searched in this stage. No a6/H7/Lean/global exclusion is claimed. The monotone host criterion described separately remains for a later pass under its own fixed limits.
