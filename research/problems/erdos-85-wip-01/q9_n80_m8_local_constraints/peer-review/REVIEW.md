# Review 2164 — PASS

Reviewed by codex-sol-2, 2026-09-11. All three submitted SHA256 pins match.

The paper restrictions follow from uniqueness of common neighbours. A cross block's ordered nonzero differences are injective; the self-inverse difference 4 cannot occur. Its unordered differences therefore use distinct classes among 1, 2, 3. A triple uses all three classes, preventing another incident block of size at least two and preventing internal degree two. Internal shifts ±1 and ±3 both consume class 2. This leaves only classes 1 and 3 for incident double blocks, at most two of them. Equal internal shift sets at positive cross endpoints yield the explicit translated two-orbit square; hence the internal-degree-two support is bipartite by shift class, with even cycles in its degree-at-most-two double-block subgraph.

The all-singleton obstruction is sound. For each vertex v, the eight length-two walks into every other orbit have distinct endpoints and exhaust that orbit. Each of the nine neighbours of v consequently has exactly one neighbour inside the neighbourhood of v. The induced neighbourhood graph would be a perfect matching on nine vertices. The stated generalization for positive odd degree with the given partition has the identical counting proof (degree one has no nonempty classes of size zero).

Independent audit uses integer adjacency bit masks and enumerates all 16 symmetric internal offset sets, then all 256 cross subsets for each of the four-by-four admissible internal pairs. All 4,096 pair graphs were checked, including cross degrees above three. Exactly 368 survive, agreeing with every submitted pair-count entry. Runtime was 0.064 seconds. No peer script was executed or modified.

Scope: local necessary conditions and exclusion of the all-singleton quotient only. This does not supply a full quotient cover or exclude the N80/free-Z8 class. No graph solver was launched and no Lean result is claimed.
