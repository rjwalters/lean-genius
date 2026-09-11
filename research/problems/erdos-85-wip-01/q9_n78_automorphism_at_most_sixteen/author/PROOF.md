# Full automorphism order at most16 for N78 candidates

Let G be a simple C4-free nine-regular graph on78 vertices and A=Aut(G). We prove |A|<=16, with possible orders restricted to

 1,2,3,4,6,8,12,16.

Accepted2264 proves |A| divides48. Accepted2361 excludes |A|=48. It remains to exclude |A|=24, the only other divisor of48 exceeding16.

Suppose |A|=24. Independently accepted2401 exhausts all such actions: A must be S4 with vertex orbit sizes(6,6,6,12,12,12,24), cyclicC4 stabilizers on the six-orbits, transposition-generated stabilizers on the twelve-orbits, and a regular24-orbit. Order3 elements act freely. All other order24 character cases have already been excluded in that accepted composition.

Independently accepted2405 excludes this last action. Its necessary geometry2400 and complete partial domains2402/2404 give576 partial78-vertex graphs. In each graph the42 vertices outside the residual set already have final degree9, while the36 residual vertices have degree4 and need five new neighbors within that set. Each partial graph has a residual vertex with six individually eligible partners but no possible five-element neighborhood: every such five-subset contains two vertices with an existing common neighbor and would create a C4. Independent review verified all576 input/result/certificate correspondences, recomputed the eligible sets and local neighborhoods, and checked all3456 explicit subset-conflict certificates. Thus no full graph can extend any necessary partial root.

All relevant input-coverage conditions in2405 are discharged:2400,2402 and2404 are independently PASS, as are2401 and2405. Therefore |A|=24 is impossible. Together with2264 and2361 this gives the stated remaining divisor list and |A|<=16. In particular this does not assert that |A| divides16; orders3,6 and12 remain possible.

This composition uses the verified local-neighborhood obstruction, not the withdrawn informal argument that incorrectly counted a60-vertex complement as48. All earlier UNKNOWN search outputs remain unchanged and are not negative evidence. The proof does not exclude the remaining automorphism orders, asymmetric candidates, N78 existence, N80 or Erdős85 globally. There is no new graph search or Lean formalization in this assembly.
