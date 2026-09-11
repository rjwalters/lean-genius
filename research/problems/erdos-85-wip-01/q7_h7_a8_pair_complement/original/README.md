# H7 a8: five possible complements of the pair-to-empty graph

Let Q on the seven high colours have edge ij when pair vertex Pij has an empty neighbour, and put R=K7 minus Q. For a low vertex of support weight w, its low degree is7-w and the summed common-high condition is7. Thus pair-neighbour count minus empty-neighbour count equals w. Pair neighbours have disjoint two-colour supports, so there are at most3. Each pair vertex therefore has at most1 empty neighbour, while each empty has equally many pair and empty neighbours. Consequently Q has2a edges.

For each high i, let s_i be the total number of empty neighbours of its two singleton vertices. Summing the empty/high common-neighbour conditions gives s_i+degree_Q(i)=7, hence degree_R(i)=s_i-1. A singleton with e empty neighbours has e+1 pair neighbours and5-2e singleton neighbours, so e<=2 and s_i<=4.

In a hypothetical remaining graph, s_i=1 is impossible at ANY high i: choose it as high0, normalize the high0 matching and host counts using reviewed2064/2066/2068. The only count profiles with singleton-host empty sum1 are twin6 and crossed14. Their entire host-assignment domains have been excluded in2074+2075 and2076, respectively. This use does not require i to maximize anything. Since degree_Q<=6 already gives s_i>=1, every remaining high has2<=s_i<=4 and hence1<=degree_R(i)<=3.

For a8, R has5edges, degree sum10. On7vertices with no isolate this leaves exactly the degree patterns(3,2,1,1,1,1,1) and(2,2,2,1,1,1,1). The five possible isomorphism types are:

- The five-vertex tree with degrees(3,2,1,1,1), plus K2:1260 labellings.
- K1,3 plus P3:420 labellings.
- P5 plus K2:1260 labellings.
- P4 plus P3:1260 labellings.
- K3 plus two disjoint K2:105 labellings.

These counts sum4305. Completeness is also elementary: maximum degree2 components are paths or cycles; with7vertices,5edges and no isolate the listed path/cycle partitions exhaust them. When a degree3 vertex exists, the sole degree2 vertex either subdivides one arm of its star or belongs to a separate P3, yielding the first two types. The independent finite checker inspects all20349 choices of five edges, retains degrees1..3, and compares component shapes/counts. It never enumerates host assignments or revisits capped searches.

This is a necessary auxiliary-graph cover for a8, not an exclusion of any of its five shapes, not a Lean proof, and not a solution of H7 or Erdős85. It strengthens the representation available for subsequent work. Review snapshots provide the prerequisite exclusions; their original evidence remains in the referenced packages.
