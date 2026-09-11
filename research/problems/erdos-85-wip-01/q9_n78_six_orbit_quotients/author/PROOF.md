# Six-orbit necessary reduction to two size patterns

Let G be a simple C4-free nine-regular graph on78 vertices with exactly six full automorphism orbits, A=Aut(G). Accepted2264 gives |A| dividing48 and2315 bounds vertex stabilizers by8. An order at most12 cannot cover78 vertices by six orbits. Enumerate orders16,24,48 and all nondecreasing six-part partitions of78 into divisors n_i satisfying |A|/n_i<=8. There are no order16 partitions, five at24 and eight at48; results.json records all thirteen.

## Complete necessary quotient calculation

Each equitable degree entry q_ij is a nonnegative integer with row sum9, q_ii<n_i, and n_i*q_ij=n_j*q_ji. Also n_i*q_ii is even by the handshaking lemma. Common-neighbor pair capacities give

    sum_j n_j choose(q_ji,2) <= choose(n_i,2),
    sum_j n_j q_ji q_jk <= n_i*n_k for i!=k.

The checker exhausts lexicographic off-diagonal pairs as(n_j/g*t,n_i/g*t), g=gcd(n_i,n_j), bounded only by remaining row degrees. It forces the diagonal when a row is complete, including parity, and forces the last diagonal at the leaf. Unknown entries are zero: every capacity summand is nonnegative and nondecreasing at nonnegative integer values, so violating a partial capacity cannot be repaired. Thus no actual quotient is removed by pruning. All surviving matrices are saved. This is the same necessary argument accepted2335, now with six rows and parity checked directly.

The original aggregate30-second calculation finishes COMPLETE in1.054seconds. Every partition is COMPLETE, no UNKNOWN/unvisited. Raw survivor counts in saved order are

    A24: 0,4,24,20,96;
    A48: 0,24,20,0,0,0,96,0.

Survival is not a realizability claim.

## Sylow3 removes the three-eight-orbit patterns

The surviving partition(6,8,8,8,24,24) is impossible for either order. Exactly the24 vertices in size8 orbits have stabilizers divisible by3. Their stabilizers have order3 at A24 and6 at A48, and each has a unique order3 subgroup. Count incidences(vertex, Sylow3 subgroup fixing it). All Sylow3 subgroups are conjugate, and an order3 element has zero or three fixed vertices by accepted2207/2332. Here some fixed vertices exist, so every Sylow3 fixes three vertices and24=3s. But Sylow gives s in{1,4} at order24 and{1,4,16} at order48; neither permits8. This excludes both instances.

## The four-six-eight partition is impossible

Only A24 has partition(4,6,8,12,24,24), with four saved quotients. Two give degree3 on the eight-vertex orbit. A cubic C4-free graph on eight vertices is impossible (the self-contained argument in accepted2314): every vertex's three neighbors induce at mostone edge; its six nonreturn two-step endpoints must be distinct, and at mostfour lie outside its closed neighborhood. Thus each neighborhood contains exactlyone edge, so every vertex belongs to exactlyone triangle, partitioning eight vertices into triples, impossible.

The other two quotients give degree1 on the four-vertex orbit F. Thus G[F]=2K2, whose automorphism group has order8. Since |A|=24, Cauchy's theorem supplies an element of order3. Its restriction to F is trivial because its order divides both3 and8. It fixes all four vertices of F, contradicting the order3 fixed-count upper bound three. These two quotients are also excluded.

## Remaining necessary alternatives

Only the following sizes remain, at either |A|=24 or48:

    (6,6,6,12,24,24):24 saved labelled quotients;
    (6,12,12,12,12,24):96 saved labelled quotients.

Every vertex stabilizer in these cases has 2-power order, hence every order3 automorphism acts freely. This is conditional only on the assumption of exactly six orbits, independent of the unfinished five-orbit exclusion. Neither remaining partition is asserted realizable or excluded. No seven-plus-orbit, fullN78, N80 or Erdős85 conclusion is claimed. No full graph solver or Lean formalization is used.
