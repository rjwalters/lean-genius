# Global automorphism order and the three-orbit case at N78

Let G be a finite simple C4-free graph on78 vertices with minimum degree9, and let A=Aut(G). The accepted near-Moore reduction makes G nine-regular. We prove |A| divides48, that A has at least three vertex orbits, and that equality in the orbit count forces a specific equitable partition.

## Order bound

Accepted2182 restricts the prime divisors of |A| atN78 to2 and3. Accepted2207 bounds its Sylow3 subgroup by9 and excludes the cyclic order9 case; accepted2215 excludes the remaining elementary abelian order9 case. Hence the Sylow3 order is at most3. Accepted2262 bounds every two-subgroup, including a Sylow2 subgroup, by16. Therefore

    |A|=2^a*3^b, with0<=a<=4 and0<=b<=1,

so |A| divides48. This includes a trivial automorphism group and is not an existence or nonexistence theorem for G.

## At least three vertex orbits

Every orbit size divides |A| and hence48. The possible sizes are1,2,3,4,6,8,12,16,24,48. One or two such sizes cannot sum to78: without a48 their sum is at most48; with a48 the other size would have to be30, which is not on the list. Thus there are at least three orbits.

If there are exactly three, |A|=48: otherwise |A| is at most24 and three orbit sizes sum to at most72. At least one orbit has size48 for the same reason. The other two sizes sum to30, and among the divisors of48 the only such pair is24 and6. Denote the orbits by W,R,F, of sizes48,24,6 respectively. Orbit-stabilizer gives stabilizer orders1,2,8 on those three orbits.

## The three-orbit degree pattern

Automorphism orbits form an equitable partition: for any two orbits, the number of neighbors in one of a vertex in the other is constant. Let c be the number of F-neighbors of a W vertex and d the number of F-neighbors of an R vertex. Counting edges between orbits gives degrees8c from F to W and4d from F to R. Let e be the internal degree on F. Thus

    e+8c+4d=9, with0<=e<=5, c,d nonnegative integers.

The only possibilities are(c,d,e)=(1,0,1),(0,1,5),(0,2,1). The middle possibility makes G[F] complete on six vertices, contradicting C4-freeness. The last gives every one of the24 R vertices two F-neighbors. Their24 unordered pairs of F-neighbors would have to be distinct by C4-freeness, but F has only15 pairs. It is impossible. Therefore(c,d,e)=(1,0,1): F induces a perfect matching, each W vertex has one F-neighbor, and R has none.

Partition W into six groups B_v=N(v) intersect W, each of size8. For x in B_v, at most one W-neighbor lies in B_v, none lies in the group of v's matching partner in F (such an edge closes C4 through the two centres), and at most one lies in each of the other four groups (two would share x and the group centre as common neighbors). Hence degree_W(x)<=5. As x has total degree9 and one F-neighbor, degree_R(x)>=3.

Let b be the constant W-to-R degree. Edge counting gives R-to-W degree2b. Any R vertex meets each B_v at most once by C4-freeness, so2b<=6. Together with b>=3, this forces b=3. Every inequality above is tight. Consequently the six B_v groups have full internal matchings, full cross matchings except between matched centres, and each R vertex has one neighbor in every B_v. The residual graph G[R] is cubic.

In the order(F,W,R), the exact quotient matrix and orbit sizes are

    sizes=(6,48,24),
    [1 8 0]
    [1 5 3]
    [0 6 3].

Thus the three-orbit case has the same saturated matching structure as accepted2245, although here F is an automorphism orbit rather than an assumed involution-fixed set. No involution fixing F pointwise has been inferred.

This rules out vertex-transitive or two-orbit examples atN78 and restricts the three-orbit case. It does not exclude three-orbit graphs, graphs with more orbits, or asymmetric graphs. The argument is paper group theory and elementary incidence counting, not a new graph search or Lean formalization.
