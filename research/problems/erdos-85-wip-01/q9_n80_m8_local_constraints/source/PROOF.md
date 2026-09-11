# Necessary local structure for N80 with a free Z8 action

codex-sol-3, 2026-09-11. Accepted2140 gives9-regularity. Write each of the ten free orbits as Z8, with quotient Q. These restrictions do not enumerate or exclude the full action class.

An internal C4-free circulant has degree at most2. Its possible offset sets are empty, {4}, {±1}, {±3}: degree2 with shifts±2 makes a C4, and any degree at least3 contains distinct noninverse shifts making a parallelogram C4. Thus internal degrees0,1,2 are allowed, and the degree2 shift is odd.

For any cross block T, its ordered differences of distinct offsets must be distinct nonzero residues. Otherwise two vertices in one orbit have two common neighbours. Difference4 is forbidden, since reversal would repeat that same difference. There are only six remaining nonzero residues, so |T|(|T|-1)<=6 and |T|<=3.

A degree2 cross block contributes one folded difference class from{1,2,3}. A degree3 block contributes all three classes, each once modulo sign. Internal degree2 contributes class2 through its two-step differences ±2s. Different middle orbits cannot contribute the same within-orbit two-step displacement.

Consequently:

- A row with a degree3 cross block has internal degree0 or1 and every other cross degree at most1. Degree3 edges form a matching on orbit indices.
- A row without a degree3 block has at most three degree2 cross blocks, using distinct folded classes. If its internal degree is2, at most two are possible, with classes1 and3.
- Two internal-degree-one orbits cannot be joined by any cross edge, because their shared shift4 and the translate of that edge form a C4.
- More generally, two internal-degree-two orbits with the same unoriented internal shift cannot be joined. Since their only possible shift classes are1 and3, the positive-cross support induced on all internal-degree-two orbit indices is bipartite. In particular it cannot contain any odd cycle.
- A degree2 block joining two internal-degree-two orbits has odd offset difference (class1 or3), hence its character value at -1 is0. Such degree2 blocks form a graph of maximum degree2 on those orbit indices, with even cycles only.

The bipartition statement is an existence constraint; no particular colouring is imposed on labelled quotient inputs. It does not require connectedness or any assumed transitivity between orbits. The common-shift C4 uses two vertices from each orbit, so all four are distinct.

The attached bounded local verifier builds only the16-vertex induced graphs on two orbits, over all four possible internal offset sets and all cross subsets of size at most3. It independently detects four-cycles by common-neighbour intersections and verifies every C4-free local survivor satisfies the stated pairwise restrictions. This is verification of a local lemma, not a search for full80-vertex witnesses. No complete quotient cover, full action-class exclusion, CNF/SAT run, or Lean result is claimed.

## The all-singleton quotient is impossible

The particular quotient Q=J10-I10 (zero diagonal and every cross degree1) cannot occur. For a fixed vertex v in orbit i and any other orbit j, its two-step walks to j come through the eight middle orbits distinct from i,j, one each. Their endpoints must be distinct by C4-freeness, so they fill all eight vertices of orbit j. In particular every neighbour of v has exactly one common neighbour with v. Therefore the graph induced on the nine neighbours of v is1-regular, impossible on an odd number of vertices.

The same argument excludes a C4-free graph of odd degree d partitioned into d+1 independent classes of size d-1 with a perfect matching between every pair of classes. This is a restriction on that partitioned construction, not on all graphs of order d²-1. It is the zero-internal-degree special case of the already used saturated-cross triangle obstruction.
