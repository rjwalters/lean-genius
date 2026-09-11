# Two-power automorphism orders at N78

Let G be a simple C4-free graph on78 vertices with minimum degree9. The accepted involution bounds2220,2236,2237 imply that every nonidentity involution fixes0,2,4,or6 vertices. Accepted2238 and2240 show that if it fixes six, its fixed graph is either three disjoint edges or a triangle with one pendant leaf per triangle vertex.

Suppose sigma is an automorphism of exact order2^k with k>=2. Put tau=sigma^(2^(k-1)), a nonidentity involution, and let F=|Fix(tau)|. Every sigma orbit has a length that divides2^k. An orbit is moved by tau precisely when its length is2^k: all shorter orbit lengths divide2^(k-1). Therefore

    2^k divides 78-F, with F in{0,2,4,6}.

The possible moved cardinalities are78,76,74,72. Their largest powers of two dividing them are2,4,2,8 respectively. Thus k<=3. In particular no automorphism has order16 or any higher power of two, and no automorphism can have an order divisible by16 (taking a suitable power would give order16).

For order4, F is2 or6. For order8, F is necessarily6. In every F=6 case arising here, we now exclude the triangle-with-leaves fixed graph.

Because sigma commutes with tau, it preserves tau's fixed graph and permutes its three cubic triangle centres. The induced permutation has power-of-two order, so on three points it is either the identity or a transposition. It fixes a cubic centre v. The six moved neighbors B_v of v are preserved by sigma: v is fixed, adjacency is preserved, and Fix(tau) is preserved. But every vertex in B_v is moved by tau, hence belongs to a sigma orbit of full length2^k. The six-element set B_v would have to be partitioned into such orbits. This is impossible for k>=2, since4 does not divide6.

Therefore:

* an order4 automorphism has an involution square fixing either two vertices (which induce a single edge by odd fixed degree), or six vertices inducing three disjoint edges;
* an order8 automorphism has an involution fourth power fixing exactly six vertices inducing three disjoint edges;
* no automorphism has order divisible by16.

The argument places no upper bound of eight on the order of an arbitrary two-subgroup: a group can have large order while all its elements have small order. It does not exclude order4 or8 automorphisms or their remaining matching cases, and it does not solve the full N78 graph problem. This is a paper group-action argument, not a new graph search or a Lean formalization.
