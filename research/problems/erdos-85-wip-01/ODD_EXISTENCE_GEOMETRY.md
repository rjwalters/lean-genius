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

For comparison, before the cocycle clauses were added, the necessary
holomorph-valued relaxation had 9,640 variables and 5,516,707 clauses and
timed out after ten minutes both with and without the star gauge. The quotient
equations therefore supply real mathematical propagation rather than merely
more solver time.

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
