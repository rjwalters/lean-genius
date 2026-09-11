# Deficiency components for the two elementary order9 quotients

Conditional on2208/2211/2212. Let M be the adjacency matrix of a hypothetical N78 graph realizing either representative, and define E=8I+J-M^2. C4-freeness and degree9 imply E has zero diagonal and off-diagonal entries0/1: it joins exactly pairs with no common neighbour. Its degree is8+78-81=5. Every automorphism of G preserves E.

The equitable quotient of E is8I+J_s-Q^2, where Q is the10-orbit quotient of G and every row of J_s is(3,3,9,9,9,9,9,9,9,9). check.py computes this with integers for both representatives and obtains the same matrix. It has no edges between the following blocks:

 C1=A union B union X1 union X3 (size24),
 C2=X2 union X4 (size18),
 C3=X0 union X5 union X6 union X7 (size36).

Each block is connected in E, as follows. On a regular C3 x C3 orbit an invariant simple graph of degree4 is a Cayley graph whose inverse-closed connection set consists of two distinct lines' nonzero elements; these two lines generate the group, so it is connected. This applies to X2,X4,X5,X6,X7, whose E-internal degrees are4. The E cross graph X2--X4 has degree1 in both directions, joining the two connected pieces of C2. Every vertex of X0 has one E neighbour in each of X5,X6,X7, and conversely, so C3 is connected. In C1, E[A] and E[B] are triangles. Every X1 vertex has one E neighbour in A, so A union X1 is connected; likewise B union X3. The E graph X1--X3 has degree2, joining the two connected pieces. Thus E has exactly these three connected components.

The G-partition into these components is equitable, directly by summing the already known ten-orbit quotient. Its quotient, with C1,C2,C3 in that order, is

 [[3,3,3],[4,1,4],[2,2,5]].

All entries are nonnegative integers and each row sums9. Squaring gives3I plus the matrix with every row(24,18,36), as expected from M^2=8I+J-E on component-constant vectors. The quotient eigenvalues are9 and plus/minus sqrt(3), so this condition supplies no spectral contradiction. It is a necessary structural restriction, not a graph construction or exclusion.
