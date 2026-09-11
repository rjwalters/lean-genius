# Independent review 2245: PASS

Verified both supplied file hashes and the accepted 2220 premise hash. Audited the graph derivation directly.

A vertex in B_v has exactly one fixed neighbor v. Two neighbors in any B_w would share w, producing a C4; a neighbor in the group of the fixed partner creates a C4 through that fixed edge. Consequently its eight moved neighbors have at most five in W, forcing at least three in R. The eight vertices of B_v send at least 24 edges to R, while each of the 24 R vertices receives at most one. Equality saturates every bound, giving all asserted internal/cross matchings and cubic R.

For any distinct fixed pair, a common neighbor would have to be fixed (a moved common neighbor brings its distinct involution mate). Three disjoint fixed edges have no common-neighbor pair. Thus E[F]=K6 exhausts the E degree five. The identity ME=EM follows from regularity and E=8I+J-M^2. At (x,v), ME counts the fixed G neighbor of x other than v, whereas EM counts E neighbors in B_v, since E has no fixed--moved edges. This proves all asserted E blocks, including E(R,W)=0 and the perfect matchings between distinct B groups.

Independently checked quotient row sums, weighted symmetry, and its characteristic polynomial by evaluating the monic cubic determinant at four distinct integers. The equitable lift is injective since each cell is nonempty, so both irrational eigenvalues occur. On the five-dimensional fixed zero-sum subspace E=-I and J=0, hence M^2=9I. The two eigenvector maps have the stated signs; their W restrictions reproduce f(v), proving injectivity and both multiplicity bounds. The eigenspaces for different eigenvalues are disjoint.

This establishes necessary constraints only. It neither excludes the matching case nor constructs a graph, and it is not a Lean verification. No search was run.
