# Order-five fixed-point restriction at orders 78 and 80

Assume a simple C4-free graph G has N=78 or 80 vertices and minimum degree at least 9. Accepted below-square regularity (review 2140) makes G exactly 9-regular. Let g be an automorphism of exact order 5. Write F for the number of fixed vertices, M=N-F for the number of moved vertices. Exact order implies M>0; M is a multiple of 5.

Every moved vertex has at most one fixed neighbour. Otherwise its orbit of five distinct vertices consists of common neighbours of two distinct fixed vertices, giving a C4. Consequently the graph induced on the moved vertices has minimum degree at least 8. The elementary C4-free bound |V| >= 1+d(d-1), applied at d=8, gives M>=57, hence F<=N-57.

Suppose F>0. At a fixed vertex the permutation of its nine neighbours has orbit lengths 1 or 5, so its degree in the fixed induced graph is either 4 or 9. Thus this induced graph has minimum degree at least 4, giving F>=13 by the same bound. Let b be its number of degree-four vertices. The boundary has exactly 5b edges. Since each moved vertex has at most one fixed neighbour, 5b<=M.

In any C4-free graph every ordered pair of distinct vertices has at most one common neighbour. Applied inside the fixed set this yields
  72(F-b)+12b <= F(F-1),
so F(73-F)<=60b<=12(N-F), or equivalently F(85-F)<=12N.

For N=80, the constraints F>=13, F<=23 and F congruent to 80 modulo 5 leave F=15 or 20. Both violate F(85-F)<=960: their products are 1050 and 1300. Therefore F=0: every exact-order-five automorphism acts freely. This does NOT exclude a free Z5 action.

For N=78, the constraints F>=13, F<=21 and F congruent to 78 modulo 5 leave F=13 or 18. F=18 violates the inequality (1206>936). At F=13, the inequalities force b=13 because F(73-F)=780 and M=65, so 60b>=780 and 5b<=65. The fixed induced graph is therefore 4-regular on 13 vertices. Its ordered two-step count 13*4*3=156 equals 13*12, so every distinct vertex pair has exactly one common neighbour. In particular every edge belongs to exactly one triangle. There are 13*4/2=26 edges, which cannot partition into triangles since 3 does not divide 26. Contradiction. F=0 is also impossible since 5 does not divide 78. Thus there is no exact-order-five automorphism at N=78.

Together with accepted review 2163 and Cauchy, the automorphism group of a hypothetical 78-vertex witness has prime divisors only among 2,3,7. At 80 the prime support remains 2,3,5,7, but its order-five elements must be fixed-point-free. Neither conclusion excludes an asymmetric graph or proves global nonexistence. No graph solver, quotient search or Lean result is claimed.
