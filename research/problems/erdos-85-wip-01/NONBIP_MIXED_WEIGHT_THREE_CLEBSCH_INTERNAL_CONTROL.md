# Clebsch internal control excluded by a triangle-packing bound

Node: A.5.3 / A-REG-NONBIP / NONBIP-MIXED / weight three.

Status: the internal conditions below are simultaneously realizable, but
the full small-shore Gram equation is impossible for this H,D. An exact
triangle-packing count excludes B, before any exterior equation is needed.
This is a q16 candidate-specific proof, not a Lean theorem or an exclusion
of all weight-three defect graphs.

## Construction

Write the points as `(x,i)` with `x` in F2^4, encoded by integers0 through15,
and `i` in `{0,1,2}`. Addition of base coordinates is bitwise XOR.
Let the base graph have connection set

```text
S={1,2,4,8,15}.
```

This is the 5-regular folded5-cube, also called the Clebsch graph; see the
[DistanceRegular.org entry](https://www.math.mun.ca/distanceregular/graphs/clebsch.html).
The explicit definition fixes which of the two complementary graphs
sometimes carrying that name is meant. No classification theorem is used.
Define D by replacing each base vertex by three independent points and
joining all nine pairs between adjacent base vertices:

```text
D((x,i),(y,j)) iff x XOR y belongs to S.
```

Define H with generators3,5,9 and the three different transpositions of
`{0,1,2}`:

```text
sigma_3=(0 1), sigma_5=(0 2), sigma_9=(1 2),
N_H(x,i)={(x XOR s, sigma_s(i)): s in {3,5,9}}.
```

## Exact internal properties

D is simple and15-regular on48=3q points. The four unit vectors in S give
connectivity. No sum of two distinct elements of S lies in S, so D is
triangle-free. Base vertices `0,1,3,7,15` give an induced5-cycle, and taking
fiber coordinate0 gives one in D. Thus D is nonbipartite.

H is simple, symmetric, and cubic: each generator and each corresponding
fiber permutation is an involution, and the three base neighbors differ.
Each generator translation commutes with the base adjacency of D; each
fiber permutation commutes with the all-ones3-by-3 matrix. Therefore HD=DH.
None of3,5,9 belongs to S, so H and D have disjoint edge sets. In particular
`diag(HD)=0`, satisfying the even-overlap condition that excluded the entire
interval-defect family.

For two different H generators s,t, their sum is respectively6,10,12.
These three sums are distinct and outside S. At a fixed starting fiber
coordinate i, the two orders of the generators end at
`sigma_s sigma_t(i)` and `sigma_t sigma_s(i)`. Products of distinct
transpositions are opposite3-cycles, which take i to different points.
Consequently every off-diagonal entry of H^2 is at most1, and every entry
on a D-edge is0. Thus H is C4-free and its neighborhoods across D-edges
are disjoint.

Exact binary elimination gives `rank_F2(D+I)=38`, which is even. Hence the
new closed-neighborhood rank condition is also satisfied. All these
properties hold simultaneously for these same H,D matrices.

## The full small-shore Gram is impossible

The required incidence matrix B would have48 rows,208 columns, row sum13,
column sum3, and

```text
H^2+BB^T=15I+J-D.
```

Its off-diagonal support is the26-regular graph
`L=J-I-D-(H^2-3I)`. Such a B exists if and only if L has a triangle
decomposition. Each size-three column covers its three point pairs;
the Gram equation requires each L-edge exactly once and all other pairs
zero times. Conversely a decomposition gives row degree13 because L
has degree26. In fiber blocks, L has K3 within each
base fiber, matching I3 blocks at base differences6,10,12, and full K3,3
blocks at the other seven nonzero differences outside S.

Let X be the subgraph consisting of all full fiber blocks at differences

```text
R={3,5,7,9,11,13}.
```

These are six of the seven full block classes; the omitted class is14.
No XOR of two elements of R lies in R, so X is triangle-free. It has
degree `6*3=18`, and is a subgraph of L. Consequently

```text
|E(L)| = 48*26/2 = 624,
|E(X)| = 48*18/2 = 432.
```

Any triangle of L uses at most two X-edges. A triangle decomposition of
L would contain `624/3=208` triangles, covering at most `2*208=416`
X-edges. But all432 X-edges must be covered. This is a contradiction.
Equivalently, every triangle needs an edge of L outside X, but there
are only `624-432=192` such edges for208 edge-disjoint triangles.

The general counting obstruction used here is: if X is a triangle-free
spanning subgraph of a triangle-decomposable L, then
`3|E(X)| <= 2|E(L)|`. The explicit R above violates this necessary bound.
The checker verifies R is sum-free, X is a triangle-free subgraph of L,
both exact edge counts, and the strict inequality.
The same count excludes a nonnegative fractional triangle decomposition:
total triangle weight would be208, but X-edge coverage would still be at
most416. This obstruction is stronger than failure of one integer search.

In fact X is the cut of L by the least-significant base bit. Sol3 gave an
equivalent signed-square certificate. Set `s(x,i)=(-1)^(x mod 2)`, so
`sum s=0`, `Hs=-3s`, and `Ds=3s`. The C Gram would imply

```text
||B^T s||^2 = s^T (15I+J-D-H^2) s = (15-3-9)*48 = 144.
```

Every column of B has three ones. Its signed column sum is odd, so its
square is at least1;208 columns therefore require `||B^T s||^2>=208`.
This contradicts144. Thus strict positive definiteness of the required
Gram matrix does not suffice: its odd-weight integer factorization fails.
More generally an incidence matrix of odd column weight must satisfy
`||B^T s||^2>=number of columns` for every sign vector s. This is the
same obstruction as the cut bound here, not a second independent result.

Thus no incidence B satisfying the stated full C Gram exists, regardless
of any choices for T or the exterior defect. The internal construction
remains valid: it cuts an internal-only exclusion using parity and
commutation. The subsequent packing bound supplies the missing
candidate-specific obstruction. It does not classify arbitrary cubic H,
other Clebsch-based H, or all weight-three D. A bounded unrestricted
triangle-decomposition solver returned UNKNOWN at45 seconds; this proof
depends on the exact count, not a solver verdict.

## Changing the three base generators cannot repair the failure

Sol1's character argument extends the same signed bound to any three
base translations `s1,s2,s3` in F2^4, allowing repetitions and zero.
Assume H has an equitable quotient on the16 base fibers equal to the sum
of these three translation matrices: for each vertex over x, the number
of H-neighbors over y is the multiplicity of `x+y` among the three shifts.
The fiber edges may vary, provided H is simple: a fiber-constant character
does not see which fiber labels are matched. Retain the same Clebsch
blow-up D and full C Gram requirement.

For a binary character k, put `chi_k(x,i)=(-1)^(k dot x)`. The subspace

```text
U={k : k dot(s1+s2)=0 and k dot(s1+s3)=0}
```

has dimension at least2. On U the three generator signs agree, so
`H chi_k = +3 chi_k` or `-3 chi_k`. The base Clebsch eigenvalue at a
nonzero character of Hamming weight t is `4-2t+(-1)^t`: it is1 for
t=1,2, and -3 for t=3,4. The five characters of weight3 or4 form a
sum-free set: two distinct weight3 characters sum to weight2, and a
weight3 character plus the weight4 character has weight1.

A two-dimensional subspace has three nonzero vectors a,b,a+b, so it
cannot have all its nonzero vectors in that sum-free set. Therefore U
contains a nonzero character of weight1 or2. Its sign vector is balanced,
`D chi_k=3 chi_k`, and `H^2 chi_k=9 chi_k`. The same Gram computation
requires144 while the208 odd columns require at least208. Contradiction.

Thus the full Gram is impossible throughout this three-base-translation
family, independently of the fiber edges. This does not classify
all cubic H commuting with the Clebsch blow-up D. The original explicit
H was only one member; the stronger family conclusion is still at q16.

## Equitability follows, but translation invariance does not

For an arbitrary simple cubic H commuting with this fixed D, the partition
into the sixteen three-point fibers is automatically equitable. This does
not require that H was built using base translations.

Let E=I16 tensor J3, the matrix with an all-ones block on each fiber. The
base Clebsch identity C^2=3I-2C+2J gives the exact identity

```text
D^2+6D-6J48=9E.
```

Regularity and symmetry make H commute with J48; commutation with D then
makes H commute with E. In the (x,y) fiber block, the entries of HE are
the row sums of H[x,y], whereas the entries of EH are its column sums.
Equality for every pair of fiber labels forces all those row and column
sums to be one common integer Q[x,y]. Thus Q is symmetric, nonnegative,
and has every row sum3. Summing HD=DH over fiber blocks gives QC=CQ.
The checker verifies the displayed polynomial identity entry by entry.

Consequently the missing hypothesis in the excluded quotient family is
translation invariance of Q, not equitability. No proof here forces an
arbitrary cubic integer commutant Q into that family. A bounded20-second
necessary-condition quotient probe returned UNKNOWN and supplies no
classification or nonexistence evidence. The fixed-D arbitrary-H problem
remains open; no further quotient enumeration is justified by that timeout.

Run the standard-library checker:

```sh
python3 research/problems/erdos-85-wip-01/check_weight_three_clebsch_internal.py
```

## Lean signed-Gram consumer

`proofs/Proofs/Erdos85OddColumnSignedGram.lean` supplies the direct algebraic
consumer, with no assumed energy bound:

- `oddColumn_signedGram_lower_bound` proves the sign-vector Gram lower
  bound from odd integer column sums (binary entries are unnecessary).
- `oddColumn_gram_jointSign_false` derives the Gram energy from the actual
  identity `BB^T=(q-1)I+J-D-H^2` and a balanced joint sign eigenvector,
  then contradicts the lower bound when the parameter inequality holds.
- `clebsch_signedGram_no_incidence` specializes to 48 rows, 208 columns,
  column sum 3, `Hs=-3s`, and `Ds=3s`, deriving the contradiction 144<208.

The module compiles with no `sorry` and only `propext`, `Classical.choice`,
and `Quot.sound`. The concrete definitions of H,D and the Clebsch character
geometry, including the widened quotient-family argument, remain the
prose/checker inputs above; the numerical corollary keeps those eigenvector
hypotheses explicit. This is not a Lean exclusion of arbitrary Clebsch
commutants or of the entire weight-three branch.
