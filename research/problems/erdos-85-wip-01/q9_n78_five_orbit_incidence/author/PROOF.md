# Five automorphism orbits: four necessary order/size alternatives

Let G be a simple C4-free nine-regular graph on78 vertices with exactly five automorphism orbits, and let A=Aut(G). Accepted2264 gives |A| dividing48. Accepted2315 bounds every vertex stabilizer by8. Accepted2207 gives zero or three fixed vertices for every nonidentity order-three automorphism of G; accepted2264 includes that Sylow3 subgroups have order3.

## Orbit-size cover

For each divisor m of48, every orbit size d divides m and satisfies m/d<=8. If m<=12, five orbits contain at most60 vertices. If m=16, every orbit size is a power of two at most16. Five such sizes either all equal16 and sum80, or have sum at most4*16+8=72. Hence m=24 or48.

The complete five-part divisor partitions of78 under the stabilizer bound are:

* m=24: (3,3,24,24,24), (6,12,12,24,24).
* m=48: (6,6,6,12,48), (6,8,8,8,48), (6,8,16,24,24), (6,12,12,24,24), (6,16,16,16,24).

The saved elementary arithmetic check enumerates these divisor partitions. It is not a graph or quotient search.

## Order-three fixed-point incidence

Let s be the number of Sylow3 subgroups of A. For m=48, Sylow's theorem gives s in{1,4,16}. A vertex whose stabilizer has order divisible by3 has stabilizer order3 or6, by2315. Either group has a unique subgroup of order3. Thus such a vertex contributes exactly one incidence with a Sylow3 subgroup fixing it; all other vertices contribute zero.

All Sylow3 subgroups are conjugate. If any fixes a vertex, each fixes exactly three vertices by2207. Consequently the number of vertices with stabilizer divisible by3 equals3s, and must be one of3,12,48. For m=48 these are precisely vertices in orbits of size8 or16.

Both partitions (6,8,8,8,48) and (6,8,16,24,24) have24 such vertices, impossible. The partition (6,16,16,16,24) has48 and is not excluded by this incidence alone.

## Excluding the remaining nonfree order-three partition

Suppose the orbit sizes are (6,16,16,16,24), and denote the six-vertex orbit by F. The graph induced on F is regular, say of degree d, because F is an automorphism orbit. C4-freeness bounds its two-step endpoints by d(d-1)<=5, so d<=2.

For any other orbit X of size n, let r be the number of F-neighbors of each vertex in X. Different vertices of X cannot have the same unordered pair of F-neighbors. Therefore

    n*choose(r,2) <= choose(6,2)=15.

Since n is16 or24, this forces r<=1. Edge balance says n*r=6*q, where q is the number of X-neighbors of each vertex in F. If n=16, divisibility forces r a multiple of3, hence r=0. If n=24, r<=1 gives q<=4. Thus a vertex of F has at most two neighbors in F, zero in the three16-orbits, and four in the24-orbit. Its degree is at most6, contradicting nine-regularity.

## Result and scope

The remaining necessary alternatives are exactly

    |A|=24: (3,3,24,24,24) or (6,12,12,24,24);
    |A|=48: (6,6,6,12,48) or (6,12,12,24,24).

In all four alternatives, every vertex stabilizer has order a power of two. Hence every order-three element acts freely on vertices.

This does not exclude these four alternatives or assert their realizability. It does not require the separate at-least-five-orbits assembly, and makes no universal regular-neighborhood claim for order-eight stabilizers. The mixed regular/four-plus-four dihedral local case is not resolved here. No graph search, capped UNKNOWN premise, or Lean formalization is used.
