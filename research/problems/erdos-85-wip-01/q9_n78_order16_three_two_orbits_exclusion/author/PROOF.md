# Exclusion of three two-point center orbits at full order16

Let G be simple, C4-free and nine-regular on78 vertices, with full automorphism group A of order16. Use accepted2419's invariant matching S of size6, attached set W of size48, and residual set R of size24, with quotient [[1,8,0],[1,5,3],[0,6,3]]. Suppose S has three A-orbits of size2. We derive a contradiction without a group or graph enumeration.

## W is regular, and R consists of three eight-orbits

For each S two-orbit let H_i be a point stabilizer, of order8 and index2 in A. The proof of2419 applies to each H_i and gives a nonfree locus S_i of size6. For every s in S, its A-stabilizer has order8, so its intersection with H_i has order at least4. Thus S is contained in S_i, and equality follows from their sizes. Every H_i acts freely outside S.

Any automorphism fixing w in W fixes its unique S-neighbor s. Hence A_w is contained in A_s=H_i, and H_i-freeness at w makes A_w trivial. Therefore W consists of three regular16-orbits. Its unique-neighbor map to S sends each such orbit onto a two-orbit, contributing eight neighbors at each target vertex. Each S vertex requires exactly eight W neighbors; thus there is exactly one W16 for each S two-orbit. This conclusion does not require the matching edges of S to coincide with its A-orbits.

Every r in R has one neighbor in each of the six groups B_s by2419, so it has exactly two neighbors in each W16. All R orbits have size8 or16. Its size24 permits either X8+Y16 or three8-orbits.

If R=X8+Y16, the stabilizer at a point of X has order2 and acts freely on regular Y, so its Y-degree is even. Since R is cubic, X has internal degree3 or1. Accepted2425's elementary cubic-eight lemma excludes degree3. Thus X-to-Y degree is2, Y-to-X degree1, and Y internal degree2. Balance between equally sized Y and each W16 gives W-to-Y degree2 as well. Every vertex outside S therefore has exactly two Y-neighbors. For y in Y, all nine neighbors lie outside S, and each gives only one other Y endpoint of a length-two walk. At least15-9=6 other Y vertices have no common neighbor with y. But a C4-free nine-regular graph on78 vertices has exactly77-9*8=5 such vertices in total, a contradiction. Hence R has three8-orbits, denoted R0,R1,R2.

Balance now gives every W vertex exactly one neighbor in each R_i, since each R_i vertex has two neighbors in each W16.

## The cubic residual quotient is forced

Let d_ij be the number of R_j-neighbors of a vertex in R_i. The matrix D is symmetric because all three orbits have size8, has nonnegative integer entries, and every row sums to3. For each i, some entry in column i is at least2. Otherwise no R vertex would have two neighbors in R_i; no W vertex does either, and S has no R-neighbors. Thus no two R_i vertices would share a neighbor, giving every one of them seven zero-codegree partners, contrary to the global bound5.

No diagonal entry can be3, by the cubic-eight lemma. No off-diagonal entry can be3 either: it would exhaust both of its rows and leave the third row with diagonal3. Thus every entry is at most2. Every row has exactly one entry2 and one distinct entry1. The positions of the2 entries form a symmetric permutation matrix P, and the1 entries form a disjoint symmetric permutation matrix Q. A symmetric permutation on three letters is the identity or a transposition. The identity shares a diagonal position with every such permutation, so P and Q must be distinct transpositions. Relabelling gives

D = [[0,2,1],[2,1,0],[1,0,2]].

In particular R0--R2 is an equivariant perfect matching, and R2 induces an invariant graph of degree2. Transitivity on its8 vertices makes all cycle components have equal length. Simplicity and C4-freeness therefore force a single8-cycle.

## The action on that cycle is faithful

The kernel of A acting on R2 is contained in a point stabilizer of order2. If nontrivial, it would be a normal order2 subgroup, whose unique involution is central and fixes all8 vertices of R2. This contradicts accepted2257's six-fixed-vertex bound. Hence A acts faithfully on the8-cycle. Its full automorphism group is the dihedral group of order16, so A is that whole group in this action.

Identify R2 with the vertices of the8-cycle. A vertex stabilizer is the order2 reflection through that vertex and its opposite; it fixes exactly two cycle vertices. There are four distinct such stabilizers, each shared by one opposite pair. The equivariant perfect matching identifies R0 with the same A-set.

In the Cartesian product R0 x R2, a pair has a nontrivial stabilizer exactly when its two point stabilizers coincide. Each of the four stabilizers fixes two points in each orbit, giving4*2*2=16 such pairs. The other64-16=48 pairs have trivial stabilizer and form exactly three free16-orbits.

## Too many free cross-pair orbits

For a regular W16 orbit, each w has one neighbor in R0 and one in R2. Mapping w to this cross-pair is equivariant and injective: two different common middles for the same pair would give a C4. Its image is one free16-orbit of pairs. Images from distinct W orbits are disjoint by the same argument. The three W orbits therefore fill all48 cross-pairs having trivial stabilizer.

There is nevertheless another free16-orbit of such pairs. For each middle m in R2, let u in R0 be its unique matching neighbor, and choose either of m's two cycle neighbors v in R2. The incidences (m,u,v) number16 and form a free A-orbit: the order2 stabilizer of m fixes u but swaps the two cycle neighbors, so it fixes neither incidence. Forgetting m maps these incidences injectively and equivariantly to R0 x R2, again by C4-freeness. Their image is therefore16 additional cross-pairs with trivial stabilizer. It is disjoint from all W images, since its middle lies in R2. This contradicts the total capacity48 already exhausted by W.

Thus S cannot have three A-orbits of size2. By2419, its only remaining orbit pattern at full order16 is2+4. Combining accepted2438, the action on S is nonfaithful, with a central involution fixing S exactly. Since an orbit of size4 requires the image on S to have order at least4, the kernel has order at most4; nonfaithfulness leaves kernel order2 or4. These remaining actions are not excluded here.

All arguments use accepted2419,2257,2425 and2438, together with elementary cycle/group actions and zero-codegree counting. No pending table enumeration, finite search, capped retry or Lean formalization is used. Full order16 and global Erdős85 remain open.
