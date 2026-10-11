# H5 engine and bridge: independent build and scope review

The conditional chain passed the read-only cloud artifact audit at
`6e85c306db71d4080850edfc4ef5436544cc2997`. Job
`20261008T102318-erdos85__h5-formal-20261008-409207` exited zero. Shared
H3PairEngine, H5Engine and H5Bridge were freshly built in 9.8, 11 and 8.6
seconds. Their actual nonempty objects have modification times within the
successful job interval; hashes were stable across two observations.

`evidence/AUDIT.json` binds execution, exact sources, objects, raw job records
and these exports, all using exactly `propext`, `Classical.choice`, `Quot.sound`:

- `Erdos85.H3Pair.search_sound`;
- `Erdos85.H5.search_sound`;
- `Erdos85.H5.parts_sound`;
- `Erdos85.H5.model_of_constraints`;
- `Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_of_parts`.

No `sorry` or extra trust escape was found. The shared H3 pair engine's source
and object hashes match its earlier independent audit. This review ran no
Lean builds, native search, C sizing prototype or solver.

## Source and statement review

H5 reuses the labelling-independent partial graph, edge insertion and
well-formedness lemmas. The model and degree caps are specialized again for
five high vertices, rather than importing the pair engine's three-high model.
The three mask arrays correspond to the canonical representatives 0, 1 and 2.
`mask_col`, checked with `decide +kernel`, connects those arrays to the actual
`fiveHighRepresentativeMasks`. The bridge derives each model axiom and
initial compatibility from the order-49 relation constraints.

Phase one accepts arbitrary clause lists while retaining explicit low-vertex
and open-clause guards. The early dead-clause check is justified using the
required unique colour neighbour and edge-admissibility lemma. Its soundness
proof covers a nonempty family of leaf tests, so the split is taken after a
chosen prefix of core vertices. Every prefix state belongs to its own hash
residue when `m > 0`; that part must run the full remaining search. Neither
hash injectivity nor balanced bucket sizes is needed.

Phase-two patterns contain one vertex per colour, with repetitions allowed.
`PatOf` records adjacency, core membership and coverage of all five colours.
Repeated vertices are handled by idempotent edge insertion. Exact-one colour
constraints justify selecting every actual neighbour of a deficient core
vertex through a pattern containing it. Fresh empty vertices may be swapped
because their support masks and partial rows coincide; the proof fixes every
core vertex under that swap. The state guard and required fresh-vertex witness
remain explicit. The final edge-completion argument retains the degree-count
gate. Exhausted fuel returns false, not an exclusion.

## Scope

For each `c : Fin 3`, the reviewed bridge assumes every part succeeds and
concludes `FiveHighCanonicalRepresentativeExcluded c.val`: no edge vector
satisfies that representative's Boolean constraints. This review credits no
native part, unconditional representative, whole cell or H5 stratum exclusion.

The separate graph-side assembly is available through
`fiveHighCanonicalGraphCover_all` in
`Erdos85OrderFortyNineFiveHighTwoFiber.lean` and
`orderFortyNineStratumExcluded_five_of_canonical`. Those consumers and the
computed premises are not instantiated by this new bridge or audited here.
