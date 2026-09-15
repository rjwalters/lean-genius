# Independent necessity check

Work in the accepted H7 host-cover model. H has seven vertices. Every singleton vertex has one fixed H neighbour and every pair vertex has two. The high and empty vertices have their full prescribed adjacency after the reviewed host stage; residual edges can only join singleton or pair vertices.

Take a pair vertex u whose current degree is two, consisting only of its two H neighbours. In any valid completion its degree is at least seven. If p of its additional neighbours are pair vertices and s are singleton vertices, then p+s >= 5. Their fixed H supports must be pairwise disjoint: a shared high neighbour together with u would give a four-cycle. Thus 2p+s <= 7. Subtraction yields s >= 3.

Every chosen singleton v must have its current neighbourhood disjoint from each current neighbour of u; otherwise adding u-v creates a four-cycle. Any two chosen singletons must likewise have disjoint current neighbourhoods, because u becomes a new common neighbour. Therefore three chosen singletons form a triangle in the saved eligibility/compatibility graph. A triangle-free graph contradicts completion.

The independent audit reconstructs each host graph using sets, checks the exact eligible vertices and every compatibility edge, then proves triangle-freeness by empty common-neighbour intersections for every compatibility edge. It joins all 1,253 negative certificates with the 218 unclassified cases to exactly the prior 1,471 unfinished cases. This does not regenerate full residual row domains or resume the old capped producer. The 218 unclassified cases stay open; a triangle is not a completion witness.
