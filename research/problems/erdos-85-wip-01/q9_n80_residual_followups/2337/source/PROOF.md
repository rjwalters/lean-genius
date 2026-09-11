# Complete local11123 residual and single-high-orbit screen

Assume the N80/F10 cubic-fixed residual orbit degrees11123. Label the three leaf orbits0,1,2, the degree-two orbit3, and the cubic orbit4. Between two free involution orbits, a C4-free graph has no edges or a single perfect matching. Every actual residual graph is therefore covered by choosing five partner-edge bits, ten cross-presence bits and one matching sign for each present cross pair.

The finite checker first enumerates all32768 binary quotient skeletons and retains exactly21 with row degrees1,1,1,2,3. Expanding matching signs gives180 labelled graphs, of which144 pass every distinct-vertex codegree check. The original30-second run completed in0.062 seconds. No UNKNOWN or unvisited case occurs.

For a potential degree-three attached orbit, select a residual triple meeting three distinct involution orbits; its partner support is the involution image. Requiring distinct orbits is necessary because an attached vertex and its partner cannot share a residual pair. We retain one ordering of each paired support. The residual support-degree sum must be at most five by the endpoint budget. Adding the two attached vertices and their supports must preserve C4-freeness.

There is one further necessary condition. Each of the five W-neighbors of a degree-three attached vertex has a nonempty residual support consisting only of leaves: in the no-isolation budget the high neighbor already contributes two. These five supports are disjoint and therefore occupy at least five of the six residual leaves. The residual-middle endpoints from the candidate triple must consequently occupy at most one leaf, or they would overlap those W-middle endpoints and create a C4. The checker imposes this condition on the triple; its partner has the same property by involution invariance.

Exactly960 high support orbits pass across the144 graphs. Every graph has at least one such support. Thus this complete necessary single-orbit screen excludes no residual graph. These supports are not full311 groups or completed attachments: their four low group vertices, the fixed center, W edges and other groups have not been supplied.

A separate30-second postprocessing step canonicalizes the144 graphs by all192 degree-preserving equivariant relabellings (permuting the three leaf orbits and independently flipping all five pairs). It gives exactly four residual types with labelled class sizes48,24,48,24 (the saved file orders these by representative). Representatives and their complete local support lists are in classes.json. Canonicalization preserves the distinguished involution and vertex degrees.

The elementary structure also explains the four types. The four nonleaf vertices induce2K2 orP4: their degree sum10 and the six leaves give e(nonleaf)=2+e(leaf), at most three by the two-orbit C4 bound. In the2K2 case its edges are either the two partner edges or a cross matching. In theP4 case its middle orbit can have residual degree two or three, and there is one invariant leaf partner edge. The remaining leaf incidences are forced up to equivariant relabelling.

This packet supplies a complete local domain and positive necessary supports for a future multiple-attachment check. It does not exclude11123 or supply a full graph. No full graph solver or Lean formalization is used.
