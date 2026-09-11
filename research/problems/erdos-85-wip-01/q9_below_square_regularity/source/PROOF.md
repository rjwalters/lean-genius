# Minimum degree below square order forces regularity

Proposed paper lemma, codex-sol-3, 2026-09-11. Awaiting independent review.

Let G be a finite simple C4-free graph with minimum degree at least d≥2.
Fix v of degree D. The induced graph on N(v) has maximum degree at most one:
if u∈N(v) were adjacent to distinct x,y∈N(v), the distinct vertices
v,x,u,y would form a C4. Therefore every u∈N(v) has at least d−2 neighbors
outside N[v], after removing v and its at most one neighbor within N(v).
The outside-neighbor sets for distinct u,w∈N(v) are disjoint, since a common
outside neighbor z would give the C4 v,u,z,w. Counting disjoint sets yields

    |V(G)| ≥ 1+D+D(d−2) = 1+(d−1)D.

If |V(G)|<d², then D≥d+1 would imply |V(G)|≥1+(d−1)(d+1)=d²,
a contradiction. Thus all degrees are at most d; combined with the assumed
minimum degree, G is d-regular.

At d=9 and N∈{78,79,80}, every minimum-degree-nine C4-free graph is therefore
9-regular. For N=79, the degree sum 9·79 is odd, impossible. The N80 and N78
edge counts must be exactly 360 and 351, respectively. This supplies a direct
paper exclusion of N79 independent of any external Ramsey value.

The operator's requested minimum-degree problem is unchanged: regularity is
a proved consequence below square order, not a restriction to an assumed
subclass. The generic generator still imposes only minimum degree. Any
regularity constraints added later must cite the independently accepted lemma.
This does not exclude N78/N80, say anything at N81, or resolve Erdős85.
