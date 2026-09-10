# H3 triple equality: exclude m=2 and obtain T>=12

Within the reviewed universal H3 triple partition, m=2,T=11 is excluded by exact finite induced-graph enumeration for both r=3 and r=4. Combined with the reviewed m=1,r=3, m=1,r=4 and m=3 exclusions and the universal T>=11 bound, this proves the computationally supported universal triple-profile lower bound T>=12.

This does not exclude the H3 triple profile or any full order49 graph. It is not a Lean theorem and selects no residual spectrum. Its inputs are the graph-to-partition reductions in the reviewed support, secondary, matching-capacity and triangle-lower-bound notes. The standalone standard-library verifier regenerates all domains and completions using integer arithmetic, with no optimizer or timeout.

## Equality restricts U to at most one triangle

Write E={u} union N union T2 union U1 union U2 union U3, of sizes1,6,2,5,5,5, and R=N union T2. The six special-singleton triangles and the m triangles through u are distinct. The 6-2m unmatched N vertices are independent, belong to none of those known triangles, and each lies in an all-low triangle. Thus at T=11 at least6-2m of the5-m additional triangles meet unmatched N. At mostm-1 additional triangles avoid unmatched N. Every U-triangle avoids them, so U has at mostm-1 triangles. For m=2, retain zero or one U-triangle.

## Complete finite domain

For r=4, all three cross matchings between Ui blocks are full. Normalize two to identity, enumerate the third in S5 and all15 internal two-edge matchings in each Ui. The same explicit block and common-label relabelings used in the reviewed m3/m1r4 verifiers give12 representatives with at most one U-triangle:2 with zero and10 with one, covering3960 normalized configurations.

For r=3, the cross sizes are4,5,5. Put the deficient matching between blocks1 and2, normalize the full matchings from block0 to identity, and enumerate the600 partial permutations and all internal matchings. Explicit common-label permutations and interchange of the deficient-matching endpoint blocks give167 representatives:65 triangle-free and102 with one triangle, covering37080 normalized configurations. This is the same regenerated domain and action audited for the m1r3 verifier, now retaining both triangle counts. The verifier checks disjoint orbit coverage rather than trusting saved representatives.

Fix the two matching edges in N. Enumerate epsilon and each T vertex's zero-or-one N-neighbor, retain r in {3,4}, ki+epsilon>=1 and C4-freeness on R union {u}. Quotient by explicit N permutations preserving the matching and interchange of the T vertices. There are eight r=4 representatives and one r=3 representative. The U and R relabelings are independent before adding U-R edges. Therefore the Cartesian completion domain has8*12+1*167=263 cases.

## Exact completion and matching coverage

The completion engine is the one reviewed for m1r3, with m=2 and the appropriate r-domain. Each E vertex other than u must have degree4, so compute each U vertex's required R-degree and each R vertex's required U-degree from the fixed graph. Each R vertex has at most one neighbor in any Ui (otherwise a C4 through si); enumerate disjoint subsets of R for the five Ui vertices, of exactly the required sizes. No such subset contains two N vertices (otherwise a C4 through u). An R vertex requiring three U-neighbors must appear in every block.

Combine the block options with exact remaining-degree tracking and the uniquely required final incidence mask. Incremental edge insertion rejects an existing length-three path between endpoints, precisely a new C4. Common-neighbor counts track the exact number e of E-triangles. Reject e>5 because six special-singleton triangles are already present.

Let S consist of empty vertices not covered by the E-triangles or six special-singleton triangles. The Y=5-e remaining low triangles each cover at most two empty vertices, adjacent if two. Assign every vertex of S to a covering triangle. Assignments of size two are a matching, even if the original triangles overlap. Therefore |S|-nu(C[S])<=Y is necessary. The exact maximum-matching recursion either leaves a chosen vertex unmatched or pairs it with each available neighbor. All branches decrease the vertex set. The weaker scalar empty/unmatched-N coverage checks are also enforced.

Every case continues through all completions; no first-survivor snapshot is used to infer exhaustion. The final verifier asserts completion of263 cases and absence of any survivor.

## Scope of the combined conclusion

The previously reviewed universal bound T>=11 and m in {1,2,3}, together with the separate exhaustive equality exclusions, imply T>=12 for the universal H3 triple partition. The conclusion depends on the stated finite enumeration and mathematical reductions; it is not kernel-checked Lean. The H3 pair partition and the existence or exclusion of any profile at larger T remain open.
