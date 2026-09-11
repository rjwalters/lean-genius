# Every vertex stabilizer at N78 has order at most eight

Let G be a simple C4-free graph on78 vertices with minimum degree nine, and let A be its automorphism group. Accepted2264 gives |A| dividing48. Accepted2262 bounds every two-subgroup fixing a vertex by eight. We exclude subgroups of orders12 and24 fixing a vertex; it follows that every full vertex stabilizer has order in{1,2,3,4,6,8}, hence at most eight.

We use accepted2207's order-three premises: a nonidentity order-three automorphism has independent fixed set of size zero or three. Accepted2257's graph premises give nine-regularity, at most six fixed vertices for any involution, and either one or three fixed neighbors at any fixed vertex. If an involution fixes six vertices, their graph is either3K2 or a triangle with a pendant leaf at each triangle vertex. For any involution, every fixed vertex has odd degree within its fixed graph, by pairing its nonfixed neighbors.

## A three-point neighborhood orbit

Suppose H has order12 or24 and fixes v. An order-three element of H fixes no neighbor of v, by independence of its fixed set. Each H-orbit on the nine neighbors is therefore divisible by three. Its size divides |H| and is at most nine, so the possible sizes are three and six. There is an H-orbit T of size three.

The image of H on T is C3 or S3. Its kernel L is a two-group of order |H|/3 or |H|/6. Every involution in L fixes all three points of T and hence no other neighbor of v, by the local fixed-neighbor bound. Every nonidentity element of L that fixed a vertex in the other six neighbors would have an involution power fixing it as well. Thus L acts freely on those six vertices. Its order divides six and, being a nontrivial power of two, must be two.

This immediately excludes |H|=24. For |H|=12 the image is S3 and L={1,tau} is central in H.

## The central involution must fix a four-vertex star

The involution tau fixes v and exactly its three neighbors T. If its fixed graph had six vertices, it would be the triangle-with-leaves graph with v a cubic triangle vertex. The centralizer H preserves this fixed graph and fixes v; its induced action has order at most two, because only the other two triangle vertices and their pendant leaves can be swapped. An order-three element of H would then fix all six vertices, contradicting2207.

Therefore tau has exactly four fixed vertices, namely{v} union T. This graph is the star centered at v. Write B=N(v) minus T, of size six; tau is free on B.

## The group H and its action on B

Every lift in H of a transposition in H/L=S3 has square1 or tau. The latter is impossible on B: its square tau is free there, so its permutation cycles on B would all have length four, incompatible with |B|=6. Thus transpositions have involutive lifts. Above each three-cycle exactly one lift has order three, giving a normal C3 subgroup. An involutive transposition lift inverts it. Hence H is the direct product S3 times <tau>.

The H-orbits on B have size three or six, as before. An orbit of size three cannot admit the free action of central tau, so B is one transitive H-orbit of size six. Choose b in B and let a generate its order-two stabilizer. This a is a noncentral involution. It fixes exactly two points of B: the coset fixed-point formula gives |C_H(a)|/2=4/2=2. They are b and tau(b), since tau is central and free. The other involution class, consisting of the three conjugates of tau*a, has no fixed point in B. Both classes act as transpositions on T and therefore each fixes one point there.

## The internal neighborhood matching

The induced graph on N(v) has maximum degree one by C4-freeness. No vertex of T can have a neighbor in B: applying tau would supply a second neighbor in N(v). The set T is itself independent. Transitivity on B makes its internal degree constant, zero or one. Zero would make all of N(v) independent; then the72 nonreturn two-step walks from v would have distinct endpoints outside {v} union N(v), requiring at least82 vertices. Therefore B induces a perfect matching.

The matching partner of b must be fixed by a, as the unique internal neighbor of b. The only other a-fixed point of B is tau(b), so these two vertices are matched. If t is the point of T fixed by a, the fixed graph of a contains the triangle v,b,tau(b) and the edge vt. It cannot have only four vertices: odd degrees would force both b and tau(b) to meet t, creating K4 and a C4. Thus it has six vertices and is a triangle with pendant leaves, with t the leaf attached to v. The two other fixed vertices attach respectively to b and tau(b).

All three conjugates of a therefore have six fixed vertices. Write m for the common fixed count of the three conjugates of tau*a; it is one of2,4,6, since they fix v and one neighbor in T.

## Two deficiency neighbors and Burnside's formula

The zero-codegree graph E=8I+J-M^2 is five-regular, because G is nine-regular and has78 vertices. Every point of T has no common neighbor with v, whereas each point of B shares its matching partner with v. Therefore

    N_E(v) = T union Z,

where Z has two vertices outside {v} union N(v). This set Z is H-invariant. The fixed set of tau is exactly{v} union T, so tau exchanges the two vertices of Z. Any order-three element rho of H fixes both, and its full fixed set is exactly{v} union Z. In particular Z is independent.

The involution a cannot fix a vertex of Z. Since it preserves this two-set, doing so would fix both. But its only two fixed vertices outside {v} union N(v) are the pendant leaves attached to b and tau(b), and no vertex of Z can be adjacent to any neighbor of v, by its zero codegree with v. Thus a exchanges Z, and tau*a fixes it pointwise.

The twelve elements of H consist of identity, central tau, two order-three elements rho,rho^-1, two order-six elements tau*rho,tau*rho^-1, and the two three-element involution classes. Their fixed counts are respectively78,4,3,1,6,m. For the order-six elements the fixed set is the intersection of the tau and rho fixed sets, exactly{v}. Burnside's formula requires

    (78+4+2*3+2*1+3*6+3*m)/12 = 9+m/4

to be an integer. Among m=2,4,6 this forces m=4.

Consequently the fixed set of tau*a consists exactly of v, its one fixed point t in T, and the two vertices of Z. Neither vertex of Z is adjacent to v, because Z lies outside N(v); neither is adjacent to t, by zero codegree with v; and they are not adjacent to each other, since Fix(rho) is independent. They have fixed degree zero under tau*a, contradicting the odd fixed-degree rule. This excludes |H|=12.

Together with the order24 exclusion, the accepted group-order divisor48 and the vertex-fixing two-subgroup bound eight, the asserted full stabilizer bound follows. In particular an A of order48 can have vertex-orbit sizes only6,8,12,16,24,48. This does not bound A below48 or exclude graphs with smaller stabilizers. It is a paper proof, not Lean formalization or a full Erdős85 solution. The four-fixed-vertex star is explicitly handled; it is not assumed excluded.
