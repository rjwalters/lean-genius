# Order24 with five orbits of sizes3,3,24,24,24

Let G be simple, C4-free and nine-regular on78 vertices. Assume A=Aut(G) has order24 and orbit sizes3,3,24,24,24. This packet gives necessary structure and a complete group/action parameterization; it does not exclude the case.

## The two small orbits form the matching centers

Write F0,F1 for the two three-vertex orbits. Each induced graph is regular of degree zero or two. The cross degree between F0,F1 is at most two, since degree three would give K3,3 and a C4. Thus each small-orbit vertex has at most four neighbors within F0 union F1.

For a24-orbit X and Fi, edge balance gives3*q=24*r, where q is the number of X-neighbors of a vertex in Fi and r is the number of Fi-neighbors of a vertex in X. Hence q is zero or eight. Nine-regularity forces each Fi to choose exactly one24-orbit, with q=8. Its remaining degree is one, which cannot come from its internal regular degree zero or two. Consequently each induced Fi graph is empty and the two Fi are joined by a perfect matching.

The chosen24-orbits for F0 and F1 must differ. Otherwise each of24 vertices has one neighbor in each Fi, giving24 pairs in F0 times F1. There are only nine such pairs, so two vertices share both neighbors and yield a C4. Denote the chosen orbits U,V respectively and the remaining orbit R. Every U/V vertex has exactly one F-neighbor, and R has none.

Choose matched centers f0,f1. Their stabilizers agree, because the matching is A-invariant; denote the common order-eight stabilizer by H. The three24-orbits are regular A-orbits, hence free H-sets. Both eight-element sets N(f0) minus{f1} and N(f1) minus{f0} are therefore regular H-orbits. This verifies BOTH local hypotheses of accepted2263 and2269.

The matching normal form2269 now applies. Its six nonfree H-vertices are exactly F0 union F1: all vertices outside that set are in free H-sets, and every vertex in the set has a nontrivial H-stabilizer since its H-orbit has at most three elements. Every attached vertex meets each of the five allowed center fibers once; the matched center fiber is forbidden. Thus G[U] and G[V] are cubic, each U vertex has two V-neighbors and three R-neighbors, and likewise at V. The residual graph G[R] is cubic with six attached neighbors per vertex, one over each of the six centers.

## Complete group and center-action parameters

The elementary group argument in accepted2319, through its section on four Sylow-three subgroups, requires only a group of order24 with a C4-free cubic Cayley graph. That hypothesis holds on R here. It therefore supplies the same complete overinclusive24 labelled group models: the22 products C3 semidirect P8 for all five groups P8 and all binary characters, plus S4 and A4 times C2. The four-orbit center-action section of2319 is not used here. Accepted2322 independently verifies these product tables and every possible cubic residual connection set.

For each such group A, enumerate every subgroup H of order eight. The action on F0 is A/H. Use the matching to identify F1 with a second copy of that same A-set. In these coordinates the matching joins (gH,0) with (gH,1), with no additional normalizer parameter. This is exhaustive: any original matching itself defines the identification of the second copy.

Choose origins U1,V1 attached respectively to (H,0),(H,1), then label U,V by A using left translation. The attachments are Ug to (gH,0), and Vg to (gH,1). Write lambda(g)=gH, using three coset labels with H labelled zero.

The internal connection sets SU,SV are inverse-closed three-element subsets of A minus identity. Each has exactly one element in each of the three left H cosets, because the three allowed same-half center fibers are saturated. The cross connection set T has two elements, one in each of the two nonidentity H cosets. Its inverse set T^-1 must also have one element in each of those two cosets, by saturation at V. No inverse closure of T is assumed.

All potential edges are left translates: Ug--Ugs for s in SU, Vg--Vgs for s in SV, and Ug--Vgt for t in T. The reverse cross neighbors of Vg are Ug t^-1. Enumerating all H,SU,SV,T satisfying these necessary conditions covers every action in this orbit-size case. Further C4 checks are required; these conditions alone do not assert a graph exists.

For a later residual-incidence test, label the regular R orbit by A. The neighbors in U union V of R1 form a six-element set B, with one element over each of the six centers, three in U and three in V. Every other residual attached neighborhood is gB. If two members of B already have a common neighbor in the partial graph, adding R1 makes a C4. If B and gB intersect twice for g not identity, the two residual vertices have two common neighbors. These are necessary obstructions without any residual internal edge choices.

This cover is independent of the pending five-orbit partition reduction and of any universal local regularity claim. Local regularity was proved here from the three regular24-orbits. No finite enumeration, full graph solver or Lean formalization is included in this paper packet.
