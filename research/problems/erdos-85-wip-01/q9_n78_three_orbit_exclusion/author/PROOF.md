# Assembly of the N78 three-orbit exclusion

All component reviews, including 2308, are now resolved PASS. This assembly explicitly discharges older conditional source wording using subsequent accepted reviews; the frozen earlier conditional assembly remains separate.

Let G be a simple C4-free nine-regular graph on 78 vertices. Accepted 2264 gives |Aut(G)| dividing 48 and at least three vertex orbits. If it has exactly three orbits, A=Aut(G) has order 48, with orbits F,W,R of sizes 6,48,24. The six centers F form a matching, W consists of their six attached eight-sets, and R consists of the other 24 vertices. The degree matrix is [[1,8,0],[1,5,3],[0,6,3]].

Accepted 2268 defines the normal action kernel K on F, whose order is 1,2,4 or 8. It acts freely outside F. We assemble the exclusions of all four sizes.

## Kernel one

Accepted 2275 excludes the faithful action on F. Its independent review covers the complete necessary Cayley connection domain and all 380 explicit four-cycle certificates. Its model follows from 2264 alone, so no formerly pending bridge remains relevant. Thus |K| is not one.

## Kernel eight

Accepted 2278 supplies the order-24 subgroup J, the three regular J-orbits outside F, and the cubic connection structure. It excludes kernels C8, C4 x C2 and Q8. Accepted 2298 supplies the complete five-group classification, the trivial elementary action obstruction, the dihedral direct-product action, and the unique nontrivial elementary order-three action. Its independent finite audit also certifies exhaustive S and cross coverage: exactly 16/48 cubic connection sets and 2112/14592 cross configurations.

Accepted 2296 independently excludes necessary residual-orbit incidence for every one of these 16704 configurations. Its saved-domain qualification is discharged by the independently accepted input coverage in 2298. Thus no order-eight kernel remains. The old 2278 reference to a pending 2268 bridge is discharged by accepted 2268.

## Kernel four

Accepted 2300 identifies J as C12, V4 x C3, or A4. Accepted 2301 makes J normal and identifies A/K=S3 x C2. There are two exhaustive cases.

If J is nonabelian, accepted 2302 identifies A=S4 x C2 with the standard elementary kernel. The finite review 2304 excludes all 320 necessary Cayley connection sets after auditing point-stabilizer and matching normalization. Its previously pending 2302 premise is now accepted, so its conditional obstruction applies.

If J is abelian, accepted 2305 gives a complete extension and center-action parameterization. Accepted 2307 independently audits all 240 parameter tuples and all 234336 inverse-closed connection sets, leaving only 32 local candidates in two cyclic-kernel parameterizations. Accepted 2308 excludes even a single required residual neighborhood in each of those 32 candidates using explicit complete-domain incompatibility certificates. Its independent review verifies all 160 candidate domains, 640 base rejections and 512 incompatible-pair certificates. Therefore no abelian-J case remains.

Thus both possible order-four-kernel action types are excluded, with complete paper and finite coverage independently accepted.

## Kernel two

Accepted 2309 excludes the order-two-kernel case. Its review verifies the central-extension splitting argument from accepted 2306 and the complete set of 228 necessary Cayley connection choices, with all four-cycle certificates. No unreviewed central-extension classification is assumed.

## Consequence

All four possible orders of K are excluded. Therefore no such graph has exactly three automorphism orbits, and 2264 strengthens to at least four orbits. This does not exclude all graphs on 78 vertices: asymmetric graphs and other actions with more orbits are outside the result. The 80-vertex cases and the full Erdős85 problem also remain open.

This assembly uses paper and independently checked finite results. It is not Lean formalization and does not reinterpret any capped or UNKNOWN search receipt as a negative result. All component source manifests were rehashed during preparation; current review states are stored separately to document the discharge of every previously conditional premise.
