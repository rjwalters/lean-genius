# Core44: four distinguished-incidence patterns

This is a proposed universal reduction for core44, pending independent review. It fixes only heavy-to-empty incidences, four triple-special singleton incidences, and one forced empty-neighbor row. It does not fix the remaining singleton assignment or empty-induced graph. All four patterns admit a C4-free empty-induced completion in a bounded pilot; none is excluded by this projection.

Write A=012,B=034,C=13,D=14,E=23,F=24. The fixed heavy edges are A-D,A-E,B-C (mask44 in the reviewed ordering). BC=J and exact degree seven give:

- A has one singleton a0 and one empty eA; D and E each have two empty neighbors.
- B has singleton specials b0,b2,b4 and no empty neighbor; C has two empty neighbors.
- F has no heavy or empty neighbor.
- Each triple special has exactly three empty neighbors, since its only heavy neighbor is its triple and its two uncovered colours require exactly two singleton neighbors.

The empty-neighbor sets of D,E,a0 are disjoint because all three vertices already share A. Their sizes are 2,2,3. Their union U omits eA by support overlap. The empty eA has only heavy neighbor A (complementary pair34 is absent), two singleton neighbors, and hence four empty neighbors. Paths eA-A-v-e forbid every vertex of U. Thus N_E(eA)=R, the complement of U among the other eleven empties, of size four.

The empty-neighbor sets of C,b0,b2,b4 are pairwise disjoint because these vertices share B. None of C,b0,b2 can meet eA, by overlap with support(A). For any of these vertices v, |N_E(v)∩R|≤1, because eA and v can have at most one common neighbor.

C cannot share an empty with D or E (shared high1 or high3), and can share at most one with a0. Its two empty neighbors are therefore exactly one in N_E(a0) and one in R.

b0 cannot share an empty with a0 (shared high0). Its three empty neighbors are exactly one in N_E(D), one in N_E(E), and one in R: each of the first two intersections is at most one, and R contributes at most one.

b2 cannot share an empty with E (shared high2). Its three empty neighbors are exactly one in N_E(D), one in N_E(a0), and one in R, by the same argument.

These C/b0/b2 sets are disjoint. Relabel the twelve empties as follows:

| Empty indices | Role |
|---|---|
| 0 | eA |
| 1,2 | D-neighbors; used by b0,b2 respectively |
| 3,4 | E-neighbors; 3 used by b0 |
| 5,6,7 | a0-neighbors; 5 used by C, 6 by b2 |
| 8,9,10,11 | R; 8 used by C, 9 by b0, 10 by b2 |

The remaining b4 empty-neighborhood must consist of three of the four unused vertices {0,4,7,11}. This yields exactly four canonical patterns, indexed by the omitted vertex. No permutation of high colours is needed: only empty labels were normalized within their already-distinguished sets.

check_patterns.py constructs each 27-vertex partial graph (five highs, six heavies, four specials, twelve empties), checks C4-freeness, and fixes edges0–8,0–9,0–10,0–11 in the empty-induced graph. Its four patterns are in patterns.json. Empty-induced degrees are4 at0,3 at1,2,3,4,5,8, and2 at6,7,9,10,11, by the support-weight/degree identity. complete_empty.py finds a projected completion for every pattern in25,11,9,8nodes respectively. These are partial graphs only: remaining singleton vertices/edges are omitted. No old capped search was retried, and no core exclusion follows.
