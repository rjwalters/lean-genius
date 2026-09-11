# Review 2278: PASS with independently discharged bridge

Verified both source pins, all three stated premise hashes, and the relevant accepted2263/2264 source manifests. The paper argument correctly excludes C8, C4 x C2, and Q8 as order-eight action kernels in the N78 three-orbit case.

The needed freeness bridge can be independently discharged from accepted2263 and2264 without resolving pending2268. For v in F, H=A_v has order eight. The A-action on W is regular, so H acts regularly on both attached eight-sets at v and its fixed matching partner. By2263 exactly six vertices have nontrivial H-stabilizer. Every y in F has one, since |H intersect A_y| >=64/48>1. These exhaust six, so H, and hence K contained in H, acts freely outside F.

Normality of K makes <K,rho> a subgroup of order24. Each outside orbit has size8 or24. The equation8a+24b=72 makes a divisible by three; rho fixes at least two points in each8-orbit by cycle lengths modulo three. Its global bound of three forces a=0. The independent finite arithmetic confirms the unique pair a=0,b=3. Independence of rho's fixed graph rules out any fixed center, since its matching partner would also be fixed. Hence F has two3-orbits, joined by the matching, and each of the two W24-orbits lies over exactly one. Matching saturation gives internal degree three, producing the claimed cubic Cayley graphs.

For an abelian group, an inverse-closed three-element connection set has either three involutions or one involution and a non-involution inverse pair. In both cases two commuting distinct generators not inverse to one another give four distinct vertices1,u,uv,v and four edges. A group with a unique involution has that involution central and falls into the second case. These arguments do not assume the Cayley graph is connected.

Aut(C8) has order four, so an order-three conjugation is trivial. For C4 x C2 I independently enumerated generator images and found exactly eight automorphisms; again conjugation is trivial. For Q8, every involution in the extension maps trivially to its quotient C3 and lies in Q8, so the extension retains a unique involution. Each proposed kernel therefore triggers the corresponding Cayley obstruction.

This verifies the exclusions under accepted2176/2245/2263/2264; the pending2268 record remains untouched. It does not exclude elementary abelian or dihedral order-eight kernels, smaller kernels, or N78 generally. No solver run or Lean formalization.
