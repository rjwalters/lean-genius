# Only the exponent-five presentation can remain in the kernel-four8+16 profile

Assume accepted2451's kernel-four S2+4 residual8+16 profile and the separately submitted extension-cover packet. Its independent acceptance is required. The cover says that the abstract group is one of A_k=<r,t | r^8=t^2=1,trt=r^k> with k=3 or5. The quotient A/K is V4 by2451. Since r squared lies in K and has order four, and |K|=4, necessarily K=<r squared> in either presentation.

Suppose k=3. Every element in the coset tK is an involution: (r^(2j)t)^2=r^(8j)=1. This coset maps to one nonidentity element of the regular V4 action on S4.

The W-to-Y degree profile2451 is2,1,3; the degree-three W orbit is attached to S4. Identify the regular Y set with A, choose an origin w in that W orbit, and write D={d1,d2,d3} for its Y-neighbors. At the Y identity the corresponding W-neighbors are d_i inverse w and their S-neighbors are d_i inverse s, where s is the S4-neighbor of w. These three S points must be distinct by C4-freeness. Since the quotient acts regularly on S4, the three cosets d_i K are distinct in V4.

The three pairwise differences of any three distinct elements of V4 are its three nonidentity elements. One difference therefore lies in tK and is an involution. Such an unordered Y pair has a nontrivial stabilizer under the regular A action. But a pair with common middle in a regular W orbit must have trivial stabilizer: forgetting the middle is an injective equivariant map by C4-freeness, and the middle stabilizer is trivial. Contradiction. Hence k=3 is excluded.

Thus only A_5 can remain. In this group (r^j t)^2=r^(6j), so the only involutions are r^4, t and r^4 t. The latter two are noncentral; the first is central and belongs to K. Let H be the order-eight S2 point stabilizer. Its image H/K is an order-two subgroup of V4, so H is one of the three preimages <r>, <r squared,t>, or <r squared,rt>. The middle choice contains every involution of A. But an X8 point stabilizer requires an involution outside H, since H is free outside S by2419. That choice is impossible. The other two preimages are cyclic of order eight: <r> directly, and <rt> because (rt)^2=r^6 generates <r squared>. Therefore H is cyclic of order eight in either remaining labeling.

This leaves the necessary abstract presentation A_5, its unique possible K=<r squared>, and a cyclic S2 stabilizer H. It does not exclude this presentation, its incidences, or the separate residual8+8+8 profile. No graph search or Lean formalization is used. Independent review is requested after the extension cover.
