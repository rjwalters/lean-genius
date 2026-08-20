# Odd plane-order existence: the near-Latin lift model

Status: structural extraction from the checked 48-vertex witness, 2026-08-17.
This note sharpens `GAP B-EXIST` in `FINAL_PROOF_OUTLINE.md`. It is not a
construction theorem. Its purpose is to replace “find a non-Cayley family” by
a precise intermediate conjecture which can be proved, falsified, or searched
at `q = 9` without assuming vertex transitivity.

## 1. Exact structure visible at q = 7

Let `G₇` be `Erdos85.boza48Graph`. Direct evaluation of its checked edge list
gives the following facts.

1. `G₇` is 7-regular and C4-free (already kernel-checked as
   `boza48Graph_degree` and `boza48Graph_not_containsC4`).
2. Its second-order defect graph `D` is 5-regular and has six connected
   components of order eight. In the numbering `v = 2a+b`, the components are
   the fibers of `a mod 6`.
3. Each component of `D` is the complement, inside its eight-point fiber, of
   two disjoint 4-cycles. Equivalently its spectrum is
   `{5, -3, 1, 1, -1, -1, -1, -1}`.
4. Write the six fibers as `F_i`, indexed by `i ∈ Z/6Z`. The original graph
   has the equitable quotient

   ```text
   Q = J₆ + P,
   ```

   where `P` pairs `i` with `i+3`. Concretely:

   - `G₇[F_i]` is a perfect matching;
   - between `F_i` and `F_j` there is a perfect matching when `j ≠ i+3`;
   - between `F_i` and `F_{i+3}` there is a 2-regular bipartite graph, in fact
     two disjoint 8-cycles.

The degree count is therefore `1 + 4·1 + 2 = 7`. This description does not
use the Cayley action. It survives after independently relabeling every fiber,
so it defines a substantially larger, generally non-vertex-transitive search
space than Cayley graphs.

The six-by-eight shape is not numerology: `48 = (q-1)(q+1)`, the fiber count
is `q-1`, and the fiber size is `q+1`. For any q-regular C4-free graph on
`q²-1` vertices, the second-order defect graph is automatically `(q-2)`-
regular, because every vertex has `q(q-1)` distinct distance-two endpoints.
In the observed model each defect component has the smallest natural order
`q+1` compatible with this degree.

## 2. The abstract lift datum

Fix an odd `q`. Put `m = q-1` and `r = q+1`. Both are even. A **near-Latin
lift datum of order q** consists of:

- an `m`-element fiber index set `I` with a fixed-point-free involution
  `p : I → I`;
- an `r`-element point set `X`;
- for every `i ∈ I`, a fixed-point-free involution `μ_i` of `X`;
- for every ordered pair `i ≠ j`, a bijection `π_ij : X → X`, with
  `π_ji = π_ij⁻¹`;
- for every paired index `j = p(i)`, a second bijection
  `ρ_ij : X → X`, again inverse-compatible, whose matching is disjoint from
  that of `π_ij`.

It defines a simple graph on `I × X` by putting edges

```text
(i,x) -- (i, μ_i(x));
(i,x) -- (j, π_ij(x))                 if j ≠ i,p(i);
(i,x) -- (p(i), π_i,p(i)(x));
(i,x) -- (p(i), ρ_i,p(i)(x)).
```

Inverse compatibility makes adjacency symmetric. The fixed-point and
disjointness conditions remove loops and repeated edges. Every vertex has

```text
1 + (m-2) + 2 = q
```

neighbors, and the graph has `mr = q²-1` vertices. Thus only one substantive
condition remains: every two distinct vertices must have at most one common
neighbor. In permutation language this says that the relevant two-step maps
formed from `μ`, `π`, and `ρ` have no repeated value. It is a nonabelian,
fiber-dependent analogue of the Latin-square/Sidon collision condition.

Call a datum **collision-free** when this common-neighbor condition holds.
Then its graph is q-regular and C4-free by construction.

### The routing-factorization reformulation

The global collision condition is not an amorphous SAT constraint. For
distinct fibers `i,j`, put `d_ij=2` when `j=p(i)` and `d_ij=1` otherwise.
Every possible channel for a common neighbor of `(i,x)` and `(j,y)` induces a
permutation from the `x`-copy of `X` to the `y`-copy:

- a third fiber `k` contributes `d_ik d_jk` transition permutations, one for
  each choice of a matching on `i--k` and `j--k`;
- the endpoint fiber `i` contributes `d_ij` permutations obtained by composing
  the matching(s) on `i--j` with the internal involution `μ_i`;
- the endpoint fiber `j` contributes another `d_ij` permutations.

There are exactly `q+1` channels. If `i,j` are paired, the count is

```text
(q-3) + 2·2 = q+1.
```

If they are not paired, the third fibers `p(i),p(j)` contribute two channels
each, the other `q-5` third fibers contribute one each, and the endpoints
contribute two:

```text
2 + 2 + (q-5) + 2 = q+1.
```

C4-freeness says that two channel permutations never take the same value at
the same `x`. Each permutation has `q+1` graph edges, so the `q+1` disjoint
permutations have `(q+1)²` edges and therefore partition the complete
bipartite graph `X×X`. Equivalently, the channel labels form a 1-factorization
of `K_{q+1,q+1}`, or a Latin square of order `q+1`, for **every** fiber pair.

This gives an exact two-level reformulation of collision-freeness:

1. **Same-fiber condition.** Each doubled fiber pair, viewed just as a
   2-regular bipartite graph between its two fibers, has no 4-cycle. This is
   exactly what prevents two vertices in one fiber from acquiring two common
   neighbors in its paired fiber.
2. **Global condition.** For every two distinct fibers, their `q+1` routing
   permutations form a complete 1-factorization.

The field ansatz should therefore seek a coherent family of Latin squares,
not isolated matchings. Any regular permutation group of order `q+1` supplies
one canonical 1-factorization: the graphs of its regular action are pairwise
disjoint. The unresolved compatibility problem is to choose fiber-dependent
conjugates/cosets of such actions whose transition factorizations agree
simultaneously. Allowing the conjugates to depend on the fiber pair is
precisely what escapes the Cayley no-go results. A Singer cycle on
`P¹(F_q)` is one tempting regular action, but the next audit shows that it is
not the action used by the known witness.

The checked q=7 edge list verifies this reformulation directly. For each of
the 15 unordered pairs of eight-point fibers, every one of the 64 cross-fiber
vertex pairs has exactly one common neighbor. Grouping those common neighbors
by their fiber gives blocks of size 8 or 16 exactly as predicted by the one-
or two-matching channel multiplicities above. Thus all 15 routing families in
the known witness really do partition `K_{8,8}`.

There is a sharper coordinatization. Each of the three doubled blocks is two
eight-cycles and has four alternating decompositions into two matchings.
`near_latin_q7_routing.py` enumerates all `4³=64` simultaneous choices, forms
the eight routing permutations for all 15 fiber pairs, and asks whether each
factorization is a coset of a regular permutation group. Exactly eight choices
make all 15 factorizations group cosets. They are the independent exchanges of
the two matching labels in the three doubled blocks, so the successful
decomposition is unique as an unordered pair of matchings on each block. In
every case the group has element-order multiset

```text
1, 2, 2, 2, 2, 2, 4, 4,
```

so it is the dihedral group of order eight. No choice makes even one routing
factorization cyclic, and hence no choice makes all of them Singer-cyclic.
The q=7 witness is therefore best viewed as a coherent atlas of dihedral
torsors. For general odd `q`, this points first to regular actions of the
dihedral group of order `q+1` (with rotation subgroup of order `(q+1)/2`),
rather than to a cyclic order-`q+1` action.

The natural coordinates of the checked edge list make the structure more
rigid still. For every successful decomposition, all 15 routing
factorizations have the **same** embedded regular subgroup of `Sym(8)`, not
merely conjugate copies of abstractly isomorphic dihedral groups. Moreover,
all 24 permutations occurring in the datum—the six internal involutions and
the 18 cross-fiber matchings—normalize that common subgroup. Thus they lie in
the holomorph

```text
Hol(D₈) = D₈ ⋊ Aut(D₈) ≤ Sym(D₈).
```

This suggests the sharper **dihedral-holomorph ansatz** for odd `q`. Take `X`
to be the underlying set of the dihedral group `H_q` of order `q+1`; require
every datum permutation to lie in `Hol(H_q)`, and require every routing
factorization to be a left or right coset of the one common regular copy of
`H_q`. The q=7 witness satisfies this ansatz exactly. It is much smaller than
the arbitrary near-Latin search space while still being fiber-dependent, so
it is not ruled out by the vertex-transitive Cayley searches at q=9 and q=11.
The next decisive existence test should search this holomorph-valued model at
q=9, where `H_q` is the dihedral group of order ten.

`near_latin_holomorph.py` implements this test exactly. It restricts every
datum permutation to `Hol(H_q)`, imposes all C4 clauses, and imposes the common-
coset condition through a small quotient formulation. Write each holomorph
element uniquely as a translation followed by an automorphism. A routing
family is a coset of the common regular group exactly when all its members
have the same automorphism part: C4-freeness makes the `q+1` translations
distinct, so they exhaust the regular group. The encoding adds one
`Aut(H_q)`-valued routing label `β_ij` for every fiber pair and enforces

```text
β_ij = aut(π_ij) aut(μ_i)
     = aut(μ_j) aut(π_ij)
     = aut(π_jk)⁻¹ aut(π_ik)
```

for every applicable matching choice and third fiber `k` (and similarly for
the second matching on doubled blocks).

Independent holomorph relabelings of the fibers justify a star-tree gauge
fixing seven q=9 cross matchings to the identity. The full encoding calibrates
at q=7, finding a fresh C4-free witness in under four seconds. At q=9 it has
11,000 variables and 5,648,975 clauses; Kissat returns `UNSAT` in under twenty
seconds. Thus the precise **common-dihedral-holomorph ansatz fails already at
q=9**. This is a reproducible computational verdict, not a promoted proof
certificate. It does not refute the general near-Latin axiom: a q=9 datum may
use non-holomorph permutations or routing Latin squares which are not group
tables, and an unbounded family need not contain q=9 at all.

The same program also supports the cyclic regular group. This gives a useful
cross-check at q=7: the cyclic model is `UNSAT`, agreeing with the independent
routing audit that the known witness is dihedral rather than cyclic. At q=9
the full common-cyclic-holomorph model has 4,760 variables and 4,795,071
clauses and is also `UNSAT` in under thirty seconds. Up to isomorphism, the
only groups of order ten are `C₁₀` and `D₁₀`. Consequently **every q=9 common-
group-holomorph model is computationally eliminated**. A q=9 near-Latin datum,
if one exists, must use routing Latin squares which are genuinely nongroup, or
use group structures/conjugacy gauges which cannot be made common across all
fiber pairs.

For comparison, before the cocycle clauses were added, the necessary
holomorph-valued relaxation had 9,640 variables and 5,516,707 clauses and
timed out after ten minutes both with and without the star gauge. The quotient
equations therefore supply real mathematical propagation rather than merely
more solver time.

Clause-stratification locates the group-model obstruction globally. With the
cocycle equations retained, both q=9 group types are SAT if all C4 clauses are
omitted. They also remain SAT after imposing every C4 clause whose four
vertices occupy at most three fibers. Conversely, imposing only the clauses
on four distinct fibers is SAT as well. For the cyclic model, even the union
of the two-fiber and four-fiber clauses is SAT; the three-plus-four-fiber run
remains `UNKNOWN-TIMEOUT`. The full model is UNSAT. Thus the failure is not a
local doubled-block obstruction, a standalone cocycle obstruction, or a pure
quartet obstruction. It is a compatibility failure involving the quartet
constraints together with lower-fiber routing consistency. The script exposes
`--c4-min-fibers`, `--c4-max-fibers`, and `--c4-fiber-counts` to reproduce
these diagnostics.

An induced-fiber audit makes the obstruction finite and asymmetric between the
two group types. Keep all eight-fiber cocycle equations, but emit C4 clauses
only when all four vertices lie in a chosen fiber subset. For the cyclic model,
every subset of at most five fibers is SAT. Six fibers consisting of three
complete doubled pairs are already UNSAT, whereas the other six-fiber type
(two complete pairs and two single fibers) is SAT. Thus the minimal cyclic
configuration is three doubled pairs. For the dihedral model both six-fiber
types are SAT, while seven fibers (three complete pairs plus one single fiber)
are UNSAT. These conclusions use symmetry of the fixed-point-free pairing to
reduce subsets to their numbers of complete pairs and singles. The diagnostic
is reproducible with `--c4-allowed-fibers`.

This identifies concrete prospective lemmas: a common-`C₁₀` routing atlas
cannot be C4-free on three doubled pairs, and a common-`D₁₀` atlas cannot be
C4-free on three doubled pairs plus one endpoint from the fourth. Proving
either directly should target transition products around fiber triangles and
quadrilaterals rather than the full 80-vertex graph.

## 3. Precise candidate axiom for B-EXIST

**AXIOM B-NEAR-LATIN-LIFT.** There are collision-free near-Latin lift data of
order `q` for an unbounded set of odd prime powers `q`.

This axiom immediately supplies the existence jaw of Branch B: its graphs are
`C4FreeMinDegreeWitness (q²-1) q`. It is strictly stronger than the bare
`B-EXIST` conclusion, but it is now a mathematical construction problem rather
than a hope.

The q=7 Boza witness proves that the class is nonempty. The exhaustive Cayley
failures at q=9 and q=11 do **not** falsify this axiom: a general datum allows
the matchings to depend on the ordered fiber pair and need not admit any
regular automorphism group.

## 4. Decisive next tests

The following tests are ordered by mathematical value.

1. **q=9 existence test.** Here `I` and `X` both have order eight. Determine
   whether a collision-free datum exists. A positive result is the first
   genuinely non-Cayley odd witness; a negative result disproves the simplest
   extrapolation of the q=7 geometry.
2. **Algebraic ansatz.** Take `I = F_qˣ` or an additive model of order `q-1`
   and `X = P¹(F_q)`. Seek fractional-linear matchings whose two-step
   collisions reduce to a field equation with at most one solution. This is
   the natural incidence-geometric interpretation of the `(q-1)×(q+1)`
   fibers.
3. **Defect-component converse.** Prove that if a q-regular C4-free graph on
   `q²-1` vertices has `q-1` defect components of order `q+1`, and its
   component quotient is `J+P`, then it is exactly a near-Latin lift datum.
   This would connect the construction model to intrinsic graph structure.
4. **Do not repeat Cayley exhaustions.** Further group catalogs test only the
   special case in which all matchings are translates of one connection set.
   They cannot decide B-NEAR-LATIN-LIFT.

## 5. First exact q=9 scout

`near_latin_q9.py` encodes the model directly. It fixes the within-fiber
matchings by independent fiber relabeling, represents every ordinary fiber
pair by a perfect matching and every paired fiber pair by a 2-regular
bipartite graph, and forbids each of the three possible 4-cycles on every
four-vertex set. Its CNF objective is exact: SAT reconstructs a q-regular
graph and independently rechecks that every vertex pair has at most one common
neighbor.

The trust calibration succeeds at q=7: Kissat finds a new collision-free datum
from a 960-variable, 343,440-clause CNF, and reconstruction reports zero C4s.

At q=9 the unrestricted model has 2,800 variables and 3,114,580 clauses. A
30-minute Kissat run returned `UNKNOWN-TIMEOUT`; this is neither positive nor
negative evidence. The doubled fiber pair must have cycle type `20`, `6+14`,
`8+12`, or `10+10`. Four further five-minute positive scouts normalized all
four doubled pairs to one of these types while correctly leaving the internal
fiber matchings variable. All four also timed out. Mixed cycle-type tuples
remain untested.

The honest result is therefore that q=9 remains open even inside the
near-Latin model. The exact formulation is reproducible and the next solver
work should add mathematically justified symmetry breaking or enumerate the
`4^4` doubled-pair cycle-type tuples; simply extending the timeout would not
clarify the construction.

The exact scout now supports this mixed enumeration.  The four doubled fiber
pairs may be permuted, so the `4^4` ordered assignments reduce to the 35
multisets of four types.  For example,

```text
python3 near_latin_q9.py --paired-cycles '20,20,6+14,8+12' --timeout 300
python3 near_latin_q9.py --enumerate-cycle-multisets \
  --multiset-start 0 --multiset-count 5 --timeout 300
```

fixes a single mixed assignment or runs a resumable shard of the 35 canonical
representatives.  A one-second end-to-end smoke test of one mixed assignment
and representative 34 reaches Kissat and returns `UNKNOWN-TIMEOUT`; this validates the new routing
but is not evidence for satisfiability or unsatisfiability.  A complete exact
run is still required for the decisive q=9 datum. A subsequent five-minute
Kissat scout of the maximally heterogeneous representative
`(20, 6+14, 8+12, 10+10)` also returned `UNKNOWN-TIMEOUT` on the
3,160-variable, 4,780,580-clause encoding. This shows that mixed types are not
immediately easier; it is still not evidence against existence.

### 5.1 Every plane-minus-two existence witness is necessarily nonbipartite

There is a uniform extremal obstruction which should constrain every algebraic
ansatz, not just the searches above:

> No `q`-regular C4-free graph on `q^2-1` vertices is bipartite.

Indeed, if such a graph had bipartition `L union R`, regularity and `q > 0`
would give equal side sizes

```text
|L| = |R| = n = (q^2-1)/2.
```

Count unordered pairs of vertices of `L` through their common neighbors in
`R`.  Every vertex of `R` contributes `choose(q,2)` pairs, while C4-freeness
says that each pair of `L` occurs at most once.  Hence

```text
n * choose(q,2) <= choose(n,2),
q(q-1) <= n-1 = (q^2-3)/2.
```

After rearranging, this would say

```text
(q-1)^2 + 2 <= 0,
```

which is impossible.  Thus the nonbipartite character of the q=7 Boza graph
is forced at the target order.  In particular, no incidence graph, bipartite
double cover, or other genuinely bipartite construction can establish
`B-EXIST`, regardless of the field or coordinatization.  A successful odd-q
family must build internal edges or identify the two incidence sides in a way
that retains degree `q` without introducing repeated common neighbors.

### 5.2 The signed-determinant double cover fails uniformly in odd characteristic

There is a tempting algebraic construction which has exactly the required
order and degree, but it fails for a structural reason.  Let `q` be odd, let
`a != 0` in `F_q`, and put

```text
X = (F_q^2 \ {0}) / {u ~ -u}.
```

Take two copies `L,R` of `X`, and join `[u] in L` to `[v] in R` when

```text
det(u,v) in {a,-a}.
```

The condition is independent of the representatives.  For fixed `[u]`, the
equation `det(u,v)=a` has `q` solutions, and every signed class satisfying the
adjacency condition has a unique representative among those solutions.
Consequently the bipartite graph is `q`-regular on

```text
2 * (q^2-1)/2 = q^2-1
```

vertices.  In characteristic two this is essentially the familiar affine
determinant construction; quotienting by signs appears to repair its odd-
characteristic orientation problem.

It cannot be C4-free.  Choose linearly independent `u,u'`.  For each
`(s,t) in {+1,-1}^2`, the nonsingular two-by-two system

```text
det(u,v)  = s*a,
det(u',v) = t*a
```

has a unique solution `v_(s,t)`.  Simultaneously reversing both signs negates
the solution, so the four solutions give at most two points of `X`.  They give
exactly two: equality of the two remaining signed classes would force either
`a=-a` in the first equation or `a=-a` in the second, impossible because the
characteristic is odd and `a != 0`.  Thus `[u]` and `[u']` have exactly two
common neighbors in `R`, producing a 4-cycle.

This is a q-generic no-go, not a q=9 census.  It closes the most direct
projectivized alternating-form analogue of the even-q family.  Any viable
odd-q incidence construction must break at least one of its three symmetries:
the full `+-` sign choice, the two-copy bipartition, or the uniform determinant
level on every projective class.

### 5.3 A nonbipartite replacement: linear triangle configurations

The bipartite obstruction suggests reversing the usual incidence construction.
Instead of taking the incidence graph itself, take a **point graph of a linear
triangle configuration** and then add a sparse triangle-free shadow.

For any C4-free graph `G`, split its edges canonically into

```text
T = edges which lie in a triangle,
F = edges which lie in no triangle.
```

Every edge of `T` lies in a unique triangle: two distinct third vertices on
the same edge would form a 4-cycle.  The triangles are therefore the blocks
of a linear 3-uniform hypergraph on `V(G)`.  If every vertex lies in exactly
three triangles, then this hypergraph is also 3-regular.  It has equally many
points and blocks, `|V(G)|`, its point graph `T` is 6-regular, and

```text
G = T union F,       deg(F) = q-6.
```

This is not merely an abstract alternative.  The kernel-checked theorems
`boza48Graph_localTriangleEdges` and
`boza48Graph_triangleFreeEdgeGraph_degree` show that the q=7 Boza witness has
three triangles through every vertex and a 1-regular triangle-free shadow.
Hence its triangular shadow is the point graph of a symmetric `48_3` linear
configuration and its triangle-free shadow is a perfect matching.  This
repackages the known graph as

```text
point graph of a 48_3 configuration + one-factor.
```

The configuration has a particularly small algebraic description.  Under the
semidirect group `Z24 x|_{19} Z2`, all 48 triangle blocks are the distinct left
translates of the single base block

```text
{(0,0), (1,1), (3,0)}.
```

The six ordered nonidentity differences of that block are exactly the six
triangular Cayley generators; the remaining generator `(0,1)` is the
one-factor.  This is kernel-checked by
`boza48DevelopedTriangle_injective`,
`boza48DevelopedTriangle_is_triangle`, and
`boza48Graph_triangle_exists_development`.  Thus the q=7 seed is not an
opaque seven-generator graph: it is **one developed triple plus one
involution**.  A non-Cayley generalization may retain the one-block
configuration locally while twisting the developments or the sparse shadow
between orbits.

The nonabelian semidirect action is essential, not cosmetic.  In an abelian
group, any two connection elements `a,b` which are not mutual inverses create
the Cayley parallelogram

```text
1 -- a -- ab -- b -- 1.
```

The Lean theorem
`commutative_invClosedCayley_containsC4_of_two_generators` formalizes this
4-cycle, and
`connection_product_eq_one_of_commutative_invClosedCayley_not_containsC4`
proves the contrapositive: in a C4-free abelian Cayley graph every two
distinct connection elements are mutual inverses.  Hence an inverse-closed
abelian Cayley graph has degree at most two.  This uniformly rules out cyclic
or other abelian one-block extrapolations for every target `q > 2`; a viable
development must use a nonabelian action, or abandon global Cayley symmetry
by twisting blocks/shadows between orbits.

The q=9 transitive case is now formally rigid in exactly the same language.
The Lean theorems in `Erdos85OddSquareOrderNineUniformTriangles.lean` prove:

- `squareOrderNine_vertexTransitive_localTriangleEdge_card_eq_three`:
  exactly three triangles pass through every vertex;
- `squareOrderNine_vertexTransitive_triangle_census`: the two shadows have
  120 and 240 edges and there are exactly 80 triangles;
- `triangleFreeEdgeGraph_vertexTransitiveByIso` and
  `triangularEdgeGraph_vertexTransitiveByIso`: both shadows inherit vertex
  transitivity.

Thus every vertex-transitive q=9 witness would be

```text
point graph of a vertex-transitive 80_3 linear configuration
  + a vertex-transitive cubic graph F on the same 80 points,
```

with the additional cross-condition that the union remains C4-free.  This is
a substantially smaller and more structural search space than arbitrary
9-regular graphs, while unlike a Cayley connection-set search it permits the
two shadows to carry different invariant structures.

This suggests a new general existence ansatz.  For odd `q`, seek a symmetric
linear `((q^2-1)_3)` configuration together with a `(q-6)`-regular graph `F`
on its points such that:

1. `F` is edge-disjoint from the configuration point graph;
2. every edge of `F` lies in no triangle of the union;
3. the union has no 4-cycle.

At q=7 this datum exists.  At q=9 the formal census above shows that every
vertex-transitive solution must have exactly this form.  The remaining
condition is a compatibility problem between a cubic graph and a linear
configuration, not a bipartite incidence problem; it therefore escapes the
uniform impossibility in Section 5.1.

### 5.4 Finite-field dot-product construction does not repair at q=9

Zhang--Chen--Cheng, *Finite Fields Appl.* **45** (2017), 73--85,
doi:10.1016/j.ffa.2016.11.012, construct a C4-free graph `Gamma_a` on
`F_q^2 ∖ {0}` by joining distinct `u,v` when `u · v = a`. At q=9 this is
an exceptionally close candidate: it has 80 vertices, 72 of degree 9, and the
eight conic points satisfying `u · u = a` of degree 8. Those eight missing
degrees are exactly the discarded loops, so the cheapest repair would add a
perfect matching among the conic points.

`gamma_q9_repair.py` implements `F_9 = F_3[t]/(t^2+1)` and exhausts this
repair for every nonzero `a`. In all eight cases the base graph is C4-free,
but **none of the 28 individual missing conic edges can be added** without
creating a C4. Consequently none of the 105 perfect matchings repairs the
graph. This closes the direct dot-product-plus-matching route, but not more
general edge-switching repairs and not q=9 existence itself.

An exact local catalog (`near_latin_local_catalog.py`) further locates the
difficulty. There are 945 perfect matchings on a ten-point fiber. For each
doubled-pair cycle type, the number of ordered pairs of internal matchings
whose induced 20-vertex graph is C4-free is:

```text
cycle type       compatible pairs out of 945²
20               84,261
6+14             85,008
8+12             83,712
10+10            82,330
```

Every left matching has at least 56 compatible right matchings (the minimum
over all four types). Thus no doubled-pair type has a local obstruction. The
missing condition is the routing factorization above: the ordinary perfect
matchings between different doubled pairs must be coordinated into a Latin
square for every fiber pair. Future reductions should target compatibility of
these factorizations rather than prune local cycle types.

### 5.5 No induced order-81 witness inside the orthogonal polarity graph

The other immediate projective-plane construction is also closed at q=9.
The orthogonal polarity graph `ER_9` on `PG(2,9)` is C4-free and has 91
vertices: ten absolute points of degree 9 and 81 nonabsolute points of degree
10. An induced 81-vertex subgraph of minimum degree 9 would be obtained by
deleting ten vertices such that every retained absolute point loses no
neighbor and every retained nonabsolute point loses at most one neighbor.

`er9_induced81_search.py` constructs `PG(2,9)` directly over
`F_3[t]/(t^2+1)`, verifies the `(9^10,10^81)` degree profile and the common-
neighbor bound, and solves that exact 91-variable deletion problem. Z3 returns
`UNSAT`. As an independent geometry diagnostic, the 81 nonabsolute points
split into 36 with no absolute neighbor and 45 with two; none has exactly one.

This rules out **only induced ten-vertex deletion from `ER_9`**. It does not
exclude deletion plus edge repair, another polarity, or an arbitrary
C4-free minimum-degree-9 graph on 81 vertices. Together with the failed
`Gamma_a` matching repair, however, it closes both direct finite-field
constructions presently attached to the q=9 branch.

The canonical deletion is even more rigid. Removing all ten absolute points
leaves a C4-free 81-vertex graph with degree profile `(8^45,10^36)`.
`er9_absolute_deletion_repair.py` checks all 2,880 missing edges, using the
equivalent test that a new edge closes a pre-existing length-three path.
There are **zero individually safe added edges**: this restriction is already
edge-maximal C4-free. Therefore its 45 deficient vertices cannot be repaired
by edge addition at all. Deleting a different ten-set and simultaneously
switching edges remains outside the scope of both exact checks.

### 5.6 Exact slack law for any nonabelian Cayley construction

The failure of the abelian route does not leave the nonabelian Cayley search
unstructured. Let `A` be an inverse-closed connection set of size `q` in a
group of order `q²−1`. C4-freeness makes the non-backtracking product map

```text
(a,b) ↦ ab,    a,b ∈ A,    ab ≠ 1
```

injective: a collision `ab=cd` with `a≠c` gives the rim
`1—a—ab—c—1`, while `a=c` allows left cancellation. Hence its image has
exactly `q(q−1)` elements, leaving exactly `q−2` nonidentity group elements
unused. The unused set is closed under inversion, because
`(ab)⁻¹=b⁻¹a⁻¹` is another admissible product.

In fact every nonidentity involution of the *ambient group* lies in this
unused set. If `ab=t=t⁻¹`, the inverse word `b⁻¹a⁻¹` is a second
representation unless `a=b⁻¹`, which would make the product the identity.
Consequently a candidate group of order `q²−1` may have at most `q−2`
nontrivial involutions. This supplies an immediate group-table sieve before
any connection-set search (at q=9, every order-80 group with at least eight
involutions is excluded).

This condition is not merely necessary: it is **equivalent** to C4-freeness.
Any embedded four-cycle, translated so one vertex is the identity, supplies
two distinct non-backtracking length-two connection words with the same
opposite endpoint. Therefore the Cayley part of `GAP B-EXIST` has the exact
algebraic formulation:

> Find, for unbounded odd prime powers `q`, a group of order `q²−1` and an
> inverse-closed `q`-element subset omitting the identity whose
> non-backtracking ordered product map is injective.

In other words, the missing object is an inverse-closed noncommutative Sidon
set at plane-minus-two order. No additional graph-side condition is hidden.

There is also a forced structure inside `A` itself. Because `q` is odd and
`A` is inversion-closed without the identity, inversion fixes a nontrivial
generator `t∈A`. Right multiplication `x↦xt` is a fixed-point-free
involution and every pair `{x,xt}` is an edge. Consequently every odd-q
Cayley candidate necessarily contains a canonical perfect-matching layer;
this is not an optional feature of the q=7 example.

The matching involution must also be genuinely noncentral. If `t∈A` is an
involution and `s∈A∖{t}`, then C4-freeness forces

```text
tst ∉ A,
```

because the two non-backtracking words `st` and `t(tst)` have the same
product. In particular `ts≠st` for every other generator `s`. Thus groups
with a central (in particular, unique) involution cannot support an odd-degree
C4-free Cayley graph of degree greater than one. The required construction
mechanism is now sharper than merely “use a nonabelian group”: conjugation by
the matching involution must separate the residual connection set from its
conjugate. This is the algebraic twist that the doubled-fiber routing must
encode.

For odd `q`, the unused cardinal `q−2` is odd. Inversion therefore fixes an
unused element; since the identity was removed, this element is a
nontrivial involution. Thus every viable odd-q Cayley family must organize
its small slack around at least one distinguished order-two element. This
matches the structural role of the `Z₂` coordinate in the q=7 semidirect
witness and gives a concrete design constraint for any extrapolation.

These statements are formalized, uniformly in the group, by
`connection_product_ne_of_invClosedCayley_not_containsC4`,
`card_unused_nonidentity_of_planeMinusTwo_Cayley`, and
`exists_unused_involution_of_odd_planeMinusTwo_Cayley`, together with the
matching-layer theorem `exists_connection_perfectMatchingLayer_of_odd_card`, in
`Erdos85NoncommutativeCayleyProductCollision.lean`. The twist is formalized by
`involution_conjugate_not_mem_connection` and
`involution_generator_not_commute` in the same file; the group-class
capstone `containsC4_of_odd_connection_card_of_all_involutions_central`
formally eliminates all groups whose involutions are central. The equal-sized
disjoint shores `A∖{t}` and `t(A∖{t})t` are packaged by
`erase_involution_disjoint_conjugate_shore` and its cardinal corollary.
The equivalence itself is
`not_containsC4_iff_nonbacktracking_connectionProduct_injective`.
The ambient involution sieve is
`card_nontrivialInvolutionFinset_le_of_planeMinusTwo_Cayley`.

## 6. Honest status in the final tree

- `PROVEN-AT-49-ONLY`: the q=7 datum exists, via `boza48Graph`.
- `PROVEN-COMPUTATIONALLY`: the displayed six-fiber decomposition and quotient
  are exact evaluations of the checked edge list.
- `AXIOM`: B-NEAR-LATIN-LIFT for unbounded odd prime powers.
- `GAP`: no algebraic formula for the matchings is known, and q=9 is not yet
  decided in this larger non-Cayley class.

This does not move the odd branch past `GAP B-EXIST`, but it identifies a
specific missing object and a decisive smallest experiment. That is the
top-down information the certificate campaigns did not provide.
