# Review2380: PASS

Scope: excludes precisely the S4 orbit pattern (3,3,4,8,12,24,24) for a simple C4-free nine-regular78-vertex graph. No character-enumeration completeness or exclusion of other S4 patterns is asserted.

Verified all four payload/input hashes and fresh2257 PASS. Read2257's accepted graph-premises paragraph: every involution fixes at most six vertices, and six-fixed graphs are3K2 or a triangle with three pendant leaves. These are the exact facts needed here.

The normal double-transposition V4 is contained in every Sylow2 subgroup, hence fixes both size3 orbits pointwise. Each of its three involutions already fixes six vertices, so no nonidentity element fixes an outside vertex: the outside action is free. At a fixed vertex the outside neighbor count is divisible by4. With the fixed degrees restricted to1/3, degree9 forces fixed degree1.

Any outside vertex with two fixed neighbors and its image under a nonidentity V4 element make a C4. Thus every attaching A-orbit has a unique equivariant neighbor map onto one size3 orbit, with uniform fibers. The size4/8 orbits cannot attach; a size12 orbit contributes4 neighbors per target, and a size24 orbit contributes8. Each fixed center needs8, so the sole size12 orbit cannot attach and the two size24 orbits must attach separately to the two size3 orbits.

For w attached to f, at most one W neighbor can lie over any center, and none can lie over the matching partner of f: the latter would complete a four-distinct-vertex cycle through the fixed matching edge. Hence w has at most5 W neighbors and at least3 residual neighbors. A residual vertex has at most one W neighbor over each of six centers. The lower and upper incidence bounds both equal144, forcing all residual vertices to meet each of the six center fibers once, with3 U and3 V neighbors.

The stabilizer of a vertex in the size4 orbit has order6. Its action on the regular size24 orbit U is free, since a stabilizer there is trivial. Its invariant set of three U neighbors would therefore have size divisible by6, a contradiction. All counting equalities and invariance requirements hold pointwise, not merely on averages. No solver or additional finite enumeration was needed.
