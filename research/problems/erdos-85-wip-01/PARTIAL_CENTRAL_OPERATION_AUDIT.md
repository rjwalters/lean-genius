# L1+S2: partial central law, exact reconstruction, and a stability obstruction

The common-neighbor operation has a genuine composition law that survives
the controls. It does not supply the proposed completion mechanism. Exact
completion as a central groupoid is impossible, and even approximate
same-carrier completion from the law's failure rate alone is false.
A Lean reconstruction theorem shows precisely how the stronger partial
axioms return the original C4-free graph problem.

This closes the stated central-groupoid completion/stability transfer. It
does not exclude every possible operation-based argument, and it does not
solve A-REG or Erdős 85.

## The surviving law

For distinct vertices x,y of a simple C4-free graph, define x∘y as their
unique common neighbor when one exists; otherwise leave it undefined.
If x∘y=u and y∘z=v with u≠v, then u and v have common neighbor y. Therefore

    (x∘y)∘(y∘z)=y.                                      (1)

The conclusion includes definedness of the outer product. The distinctness
condition is essential: otherwise its two inputs coincide and the partial
operation is undefined. Commutativity is automatic.

For a q-regular graph, the row at y has image N(y), with q-1 preimages
for each output u∈N(y): precisely N(u) excluding y. C4-freeness makes the
fibers disjoint. Hence (1) has exactly

    n q(q-1)³

triples with its stated premise. The genuine q4 square control has
16·4·3³=1728 such triples, all verified. This is a generic C4-free identity,
not a new consequence of square order or characteristic two.

The corresponding *total* identity is the central groupoid law; see
Boykett, [Orderly Algorithm to Enumerate Central Groupoids and Their
Graphs](https://arxiv.org/abs/math/0407070), Definition3.1. The natural total
example on ordered pairs is (a,b)*(c,d)=(b,c). Lemma5.3 records
anticommutativity, including for the broader two-operation setting.

## Why exact completion fails

In any total central groupoid, a*b=b*a implies a=b. Indeed apply the law
at (a,b,a) and (b,a,b): the same product of the equal inner values would
have to equal both b and a. Consequently no symmetric off-diagonal pair
of defined entries of the common-neighbor table can be preserved by an
exact central-groupoid completion, even if more elements are added.

There is a quantitative obstruction too. Let T be any commutative table on
n elements and B any exact central groupoid on those same elements. For
every unordered pair {a,b}, a≠b, B(a,b) and B(b,a) differ, whereas T's two
entries agree. At least one entry must change. Thus

    #{(a,b): T(a,b)≠B(a,b)} / n² >= (n-1)/(2n).            (2)

This holds for every exact target and every relabeling of it.

## Arbitrarily good approximate tables still remain far from every target

Let F be a finite field of characteristic two, of order q. On its nonzero
vectors F²\{0}, join x and y when det(x,y)=1. This is symmetric, loopless
and q-regular. Independent vectors have the unique common neighbor

    x∘y = (x+y)/det(x,y).

Distinct dependent vectors have no common neighbor. These claims follow
by solving the two linear determinant equations; they prove C4-freeness
without assuming a classification or graph census. The graph has q²-1
vertices, so it is an existence-side control, not a square-order witness.

Adjoin the zero vector as an isolated dummy, and define a total table T on
all n=q² vectors by the displayed formula when det(x,y)≠0, and T(x,y)=0
otherwise. The table is commutative. For each nonzero middle variable y,
exactly q(q-1)³ triples satisfy the total central law. For y=0, all q⁴
choices of the other two variables satisfy it. Therefore its exact success
fraction is

    [(q²-1)q(q-1)³ + q⁴]/q⁶
      = (1-q⁻²)(1-q⁻¹)³ + q⁻².

The failure fraction is

    3/q - 3/q² - 2/q³ + 3/q⁴ - 1/q⁵ < 3/q,

and tends to zero along binary field orders. Nevertheless (2) bounds its
distance from every exact central groupoid below by (1-q⁻²)/2, tending to
one half. Exact targets exist at these square cardinalities, as the natural
ordered-pair construction shows, so the distance assertion is not vacuous.

Thus there is **no same-size normalized-Hamming stability theorem** that
uses only the fraction of central-law violations and forces distance to an
exact model to tend to zero. This is the precise transfer tested here.
The padded adjacency graph is not q-regular: the dummy has degree zero.
The construction does not refute a statement that independently requires
all the exact square-order graph conditions; those conditions are where
the original unresolved problem returns.

Exact exhaustive table checks:

| field q | padded n | successful law triples | all triples | universal edit lower bound |
|---|---|---|---|---|
| 4 | 16 | 1,876 | 4,096 | 120/256 |
| 16 | 256 | 13,835,536 | 16,777,216 | 32,640/65,536 |

verify_partial_central_operation.py verifies the field arithmetic, constructs and checks the graphs,
compares the formula to independently enumerated common neighbors, counts
every triple, and checks the natural exact target. No order64 graph search
or larger-group search was performed.

## Exact partial reconstruction, checked in Lean

Let R(x,y,z) mean that a partial operation sends (x,y) to z. Assume:

1. R is functional in z and symmetric in x,y.
2. R has no diagonal input and never outputs its first input (hence neither
   input, by symmetry).
3. The strong conditional law holds: R(a,b,u), R(b,c,v), u≠v imply R(u,v,b).
4. Every nonempty row image contains at least two values.

Define A(x,z) iff z occurs in row x. The Lean file proves A is symmetric
and irreflexive. For x≠y it proves the exact equivalence

    R(x,y,z) iff A(x,z) and A(y,z).

Functionality then gives at most one common neighbor for distinct vertices,
which is the C4-free condition. Including the undefined diagonal, it proves
R is exactly the common-neighbor relation of the recovered graph.
Conversely, a symmetric irreflexive adjacency relation with unique common
neighbors and at least two neighbors at each nonisolated vertex gives all
these laws. No finiteness or field hypotheses are needed for this part.

Consequently imposing q-element row images and a q²-element carrier is
precisely the original q-regular C4-free endpoint problem in different
coordinates. The exact degree/cardinality conditions are not replaced by a
weaker proved completion hypothesis.

Erdos85PartialCentralReconstruction.lean uses only Lean's core library. It compiled
in lean4-arm64:v4.31.0 with a1GiB memory cap. All seven audited theorems
report **no axioms**. This formalizes the algebraic reconstruction and exact
anticommutativity. The finite-field family, counting asymptotic, and Hamming
bound above are elementary prose proofs calibrated by exact Python checks;
they are not represented as fully Lean-formalized results.

## Evidence and next condition needed

Run from the repository root:

    python3 research/problems/erdos-85-wip-01/verify_partial_central_operation.py --output-dir /tmp/erdos85-central-operation-check

The output directory receives verification.json and both exact .npy tables.
Without --output-dir, the verifier creates a fresh temporary directory and
prints its path. It uses the banked q4 control in the same source directory.

The formal module is
`proofs/Proofs/Erdos85PartialCentralReconstruction.lean`. It has no imports
beyond Lean's implicit core library, so it can be checked with Lean4.31.0
without building Mathlib. Original compile evidence and peer review1535
are archived at
`/Users/rwalters/lean-genius-erdos85-round113-sol3/l1-central-operation/`.
The report, elementary proofs, source citations, and verifier above are
self-contained and do not require that local archive. The module's seven
#print axioms commands reproduce its dependency audit.

A successor must name an additional necessary identity or quantitative
hypothesis not already equivalent to the graph reconstruction above and
not supplied merely by dense definedness or the central-law success rate.
The generic exact-completion and law-density stability proposals fail for
explicit reasons; other specially constrained operation arguments remain
unresolved.
