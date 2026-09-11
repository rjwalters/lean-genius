# Stabilizers and the kernel in the N78 three-orbit case

Assume the accepted three-orbit case2264: A=Aut(G) has order48 and vertex orbits F,W,R of sizes6,48,24, with F a matching, W its six attached8-sets, and R unattached. For v in F let H=A_v, of order eight, and let x be its matching partner. Then:

1. H acts freely on every vertex outside F; its nonfree vertices are exactly F.
2. The deficiency graph induces K6 on F and has no edges from F to its complement.
3. If L is a stabilizer of a vertex in R, then |L|=2 and no conjugate of L is contained in H.
4. The kernel K of the A-action on F is a normal two-subgroup of order1,2,4,or8. Every nonidentity element of K fixes exactly F and acts freely outside it. The faithful image on F is a transitive subgroup of the automorphism group of3K2, of order48/|K|. If K is trivial, this image is the full group of order48 that permutes the three edges and independently swaps their endpoints.

Proof of1. The A-action on W is regular because its orbit size equals|A|. Thus H acts freely on the attached8-set at v. It preserves that set, so its action there is regular. The matching partner x is fixed by H, and its attached8-set has the same regular H action. Accepted2263 therefore applies: precisely six vertices have nontrivial H-stabilizer.

Every y in F has nontrivial H-stabilizer. Indeed A_y also has order eight, and

    |H A_y| = |H| |A_y| / |H intersect A_y| <=48.

This forces |H intersect A_y|>=64/48>1. This intersection is exactly H_y. Therefore all six points of F are nonfree under H, exhausting the six allowed by2263. No point outside F has nontrivial H-stabilizer.

Proof of2. For the selected v,2263 identifies its E-neighborhood with all other five nonfree H vertices, namely F minus{v}. By A-transitivity on F and invariance of E under automorphisms, this holds for every vertex in F. Five-regularity of E leaves no edge from F to its complement.

Proof of3. Orbit-stabilizer gives |L|=48/24=2. Every conjugate of L is itself the stabilizer of some vertex of R. If contained in H, it would give a nontrivial H-stabilizer outside F, contrary to1. In particular a generator of L has no fixed vertex in F: fixing y there would place L inside A_y, a conjugate of H, and hence some conjugate of L inside H.

Proof of4. The action kernel is the intersection of all A_y for y in F, so K is normal and is a subgroup of H. Its order is therefore one of1,2,4,8. It fixes F pointwise; every nonidentity element fixes no vertex outside F by1. Its quotient image has order48/|K| and is transitive on F. Since the matching is invariant, the image embeds in Aut(3K2). This last group has exactly3!*2^3=48 elements, by independently permuting its three edges and swapping endpoints. If K is trivial the embedding is an equality of finite groups of the same order.

These are necessary action constraints and a reduction to a small family of quotient actions. No existence of a pointwise fixed involution on F is asserted when K is trivial. Neither the three-orbit case nor the faithful action case is excluded. No group enumeration, graph search, or Lean formalization is used.
