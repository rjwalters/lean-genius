# Exact Z/3 convolution conditions for F2 phase extensions

Fix any of the complete 56916 partial phase choices of accepted 2234. Its fixed vertices u,v and 18 attached vertices already have degree nine, and its 60 residual vertices have no residual edges yet. No search or optimization is performed here.

Write attached orbits as A_0,...,A_5 and residual orbits as R_0,...,R_19. Every orbit is parametrized by g in Z/3 so the specified automorphism adds one. A directed orbit block is its three-entry zero/one vector X(t): an edge joins source g to target g+t exactly when X(t)=1. Define reversal X*(t)=X(-t), and ordinary integer cyclic convolution (X*Y)(t)=sum_s X(s)Y(t-s). Here a superscript star denotes reversal, while the binary star denotes convolution; coefficients are integers, never reduced modulo three.

Let U be the known 6 by 6 attached adjacency block, C the known 6 by 20 attached-to-residual incidence block, and D an unknown 20 by 20 residual adjacency block, all over these coefficient vectors. Matrix products below use convolution and integer addition. C^dagger is the transpose with every vector reversed.

For the normalization in 2234, a fully attached residual orbit i of word (a,b) and phase s has C[a,i]=delta_0 and C[3+b,i]=delta_{-s}; its vertex g meets A_(a,g) and B_(b,g+s). A one-sided incidence uses delta_0 on the present side; absent incidences are zero. U is obtained directly from the chosen attached matching phases.

The following finite conditions are necessary and sufficient for D to complete this chosen partial graph to a C4-free nine-regular graph with the specified order-three action:

1. Every D_ij is a zero/one coefficient vector, D_ji(t)=D_ij(-t), and D_ii(0)=0. These are precisely simplicity, undirectedness and translation invariance. In particular D_ii is either empty or {1,2}.
2. For each i, sum_j sum_t D_ij(t)=9-a_i-b_i, with a_i,b_i indicating its two possible attached incidences.
3. Every coefficient of (U C + C D)_[a,i] is at most one, for every attached orbit a and residual orbit i.
4. Every coefficient of (C^dagger C + D D)_[i,j] is at most one when i!=j. When i=j, impose the bound only at t=1,2.

Proof. A coefficient of a product of orbit blocks counts common neighbors: the path source g -> middle g+s -> target g+t contributes X(s)Y(t-s). The new full adjacency matrix has blocks on fixed vertices, attached vertices, and residual vertices. Squaring it gives attached/residual block U C+C D (there is no fixed/residual edge), and residual/residual block C^dagger C+D D. Thus conditions 3 and 4 are exactly all codegree bounds for pairs with a residual endpoint and no fixed endpoint.

A fixed/residual pair has zero or one common neighbor, namely the residual vertex's incidence in that fixed vertex's attached group; this is unchanged by D. All pairs with both endpoints outside R have unchanged common-neighbor counts, since the old incidence C is fixed. They already satisfy the bound in the chosen accepted partial graph. Hence all distinct vertex pairs have at most one common neighbor, which is equivalent to C4-freeness. The diagonal coefficients at t=0 are return walks and equal degree nine by condition 2; they must not be bounded by one. Every old vertex retains degree nine, while condition 2 gives degree nine on R. This proves sufficiency as well as necessity.

Summing condition 4 over residues for i!=j recovers (Q^2)_ij+h_ij<=3 from 2219/2244, where Q_ij=sum_t D_ij(t). Summing the nonreturn bounds within one orbit recovers the one-double bound. Thus this retains the phase information discarded by the integral quotient model.

A useful forced equation: suppose i,j have the same fully attached word and distinct incidence phases s_i,s_j. Their old residual-to-residual two-step offsets are 0 and s_i-s_j. If a middle residual orbit k joins each endpoint through a single matching, let x be the directed i-to-k offset and y the directed k-to-j offset. Then condition 4 forces x+y=s_j-s_i modulo three: it is the unique remaining residue. This equation can propagate phase constraints across different quotient edges, though it is not alone sufficient for an extension.

validate.py checks the cyclic convolution identity for all 64 ordered pairs of three-bit masks and the same-word forced-offset rule for all six ordered distinct phases. This is a finite algebra verification, not a search for D, and establishes no feasible extension or excluded phase choice. The complete phase cover may contain isomorphic duplicates.
