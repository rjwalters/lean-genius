# The t=2 residual shape forces a marked three-triangle fixed graph

Assume the N80/F10 cubic-fixed branch and the t=2 residual shape of accepted review 2259. Thus G is simple, C4-free and nine-regular; its involution fixes a cubic graph H on ten centers, with attached groups B_f of size six. The ten residual vertices form a central edge xx', four neighbors L of x and four neighbors L' of x', with a perfect matching on each side. The involution swaps x,x' and L,L'. There are either two type-211 attached groups or one type-221 group, all other groups being type 111. Every attached neighbor of x or x' has residual degree one.

Let P be the four fixed centers whose attached groups meet x (equivalently x'), and M the other six centers. Write b_f=e_G(B_f,R). We first prove

    b_f = 4 + 2 deg_H[P](f)                 (1)

for every fixed center f. Here deg_H[P](f) means the number of neighbors of f in P, whether or not f belongs to P.

Let A be the adjacency matrix of G and E=8I+J-A^2. By accepted 2259, E(x) consists exactly of x' and the six centers M. Therefore (EA)_{x,f}=deg_H[M](f). On the other side, (AE)_{x,f} sums over x', L, and the four attached neighbors of x. The last four terms vanish: their residual degree one saturates their internal and allowed cross-group slots, giving one common G-neighbor with every fixed center. The x' term is 1[f in M]. Equivariance and the fact that each residual vertex meets each attached group at most once show that B_f meets exactly (b_f-2*1[f in P])/2 vertices of L. The sum of E(r,f) over L is consequently 4-b_f/2+1[f in P]. Thus (AE)_{x,f}=5-b_f/2. Since AE=EA and H is cubic, (1) follows.

In particular the P-neighbor counts are one, two, or three for type 111, 211, or 221 respectively.

## The single type-221 group is impossible

Suppose B_z is the unique type-221 group. It covers all ten residual vertices, so z lies in P. Its two residual-degree-one vertices u,u' are exactly the neighbors of x,x' in this group. All other groups have type 111 and therefore saturate every allowed cross-group matching. Thus every allowed cross-group slot is also full at each vertex of B_z. Nine-regularity now gives k_R(y)=2-deg_{B_z}(y) for y in B_z. Its four residual-degree-two vertices have no internal neighbor; u and u' each require an internal neighbor. They must be matched to each other. But u,x,x',u' then form a four-cycle, contradiction.

## The two type-211 centers lie outside P

There are now exactly two type-211 centers. Equation (1) says that H[P] has degrees one at ordinary centers and two at special centers. The degree-sum parity makes the number of special centers in P even. If both lie in P, H[P] is a four-vertex path. Every center of M has one P-neighbor and two M-neighbors. An interior vertex p of that path has exactly one M-neighbor y. Each of the two M-neighbors of y has a unique P-neighbor, its label. That label cannot be p, since y is its only M-neighbor; nor can it be adjacent to p in the four-vertex path, since this makes a four-cycle using the edge from y to that neighbor. Therefore both M-neighbors of y must have the far endpoint of the path as label. They and y and that endpoint form a four-cycle, contradiction.

Both special centers therefore lie in M, and H[P]=2K2. In H[M], they have degree one and the other four vertices have degree two. Its possible components are P6, P3 plus C3, or P2 plus C4; the last is forbidden. A triangle in M has three distinct P-neighbor labels: a shared label for two triangle vertices makes a four-cycle through the third triangle vertex. Among three distinct vertices of P with H[P]=2K2, two are adjacent. The corresponding triangle edge and the two attachment edges again make a four-cycle. Thus H[M]=P6, with the special centers exactly its endpoints.

## Finite fixed-graph specialization

Accepted review 2231 classifies cubic C4-free graphs on ten vertices into three representatives, with zero, two, or three triangles. The accompanying check considers all 210 four-subsets of each representative, 630 marked pairs (H,P) in total. Equation (1) and the two pattern alternatives leave 24 pairs: 15 single-221 cases and nine two-211 cases. After the single-221 contradiction, all nine remaining marked pairs belong to the three-triangle representative. Each has H[P]=2K2 and H[M]=P6. These are nine marked subsets in a fixed labelled representative, not nine nonisomorphic cases.

This is a necessary restriction on the t=2 residual-degree-five subcase. It does not claim that any remaining attachment is realizable, does not exclude t=0 or t=1, and does not solve Erdős 85. The proof uses no full-graph solver and is not a Lean formalization.
