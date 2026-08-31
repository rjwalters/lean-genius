# A Decided Drop and a Uniform Reduction for Erdős Problem 85

**Claude Fable and GPT Sol**

**Status.** Working manuscript. Nothing in this document is for external
distribution before the operator read-through and Zenodo gate. Formal claims
refer to Lean 4.31.0 with the repository-pinned mathlib; certificate-backed
claims additionally require the final cold build and literal `#print axioms`
audit. Theorem A is the operator-decided headline, but its unconditional
generated Lean capstones are still pipeline-pending at this draft revision;
the conditional finite-drop core is already checked. The title's “decided
drop” wording inherits the same final evidence gate.

## Abstract

Let `f(n) = minDegreeForC4 n`, the minimum threshold such that every simple
graph on `n` vertices with minimum degree at least `f(n)` contains a `C₄`.
We report two complementary results. First,
we report the determination of the adjacent values, with the final evidence
gate still pending at this draft revision:

`f(48) = 8` and `f(49) = 7`,

giving a strict finite drop, subject at this draft revision to completion of
the final replay, cold-build, and axiom-audit gate. The lower side uses a newly
checked 48-vertex extremal witness; an independently computed isomorphism check
finds it non-isomorphic to the previously recorded Afzaly–McKay witness. The
order-49 upper side is supplied by exhaustive structural reduction and LRAT
evidence whose final generated kernel replay is in progress. Second, we reduce
a negative answer to Erdős Problem 85 to one uniform graph-theoretic proposition,
`BinarySquareRegularExclusion` (A-REG). Lean verifies the entire implication

`BinarySquareRegularExclusion → ¬ Erdos85Question`.

A-REG is a live hypothesis, not a proved theorem or a forecast. In particular,
the exact Lean results at orders 15 and 16 exhibit no drop and refute the
`q = 4` analogue, while the published Boza table reports the same no-drop
behavior at orders 35 and 36. We therefore present the operator's
plane-order interpretation as a genuine rival hypothesis. The extensive
negative map records which determinant, spectrum, packing, incidence, and
finite-census routes fail to settle A-REG, isolating the connected and mixed
non-bipartite residues that remain open.

## Main results

### Theorem A — the decided 48-to-49 drop

The completed certificate chain is designed to prove

`minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7`,

and hence

`minDegreeForC4 49 < minDegreeForC4 48`.

The already checked finite-drop core is
`minDegreeForC4_fortyEight_fortyNine_exact_checked` and
`minDegreeForC4_fortyNine_lt_fortyEight_checked`; both take the order-49
nonexistence hypothesis. The unconditional generated endpoints will be
`minDegreeForC4_fortyEight_fortyNine_exact_of_generatedSevenBaseCertificates`
and
`minDegreeForC4_fortyNine_lt_fortyEight_of_generatedSevenBaseCertificates`.
They become paper evidence only when the generated module lands and passes the
cold build and literal axiom audit. No conjectural uniform hypothesis enters
this finite computation. Separately, an independently computed NetworkX
isomorphism comparison of archived graph6 artifacts finds that the checked
order-48 extremal graph is not isomorphic to the Afzaly–McKay record; this
novelty check is not part of the kernel-checked theorem.

### Theorem B — a one-proposition reduction of the infinite problem

Define `BinarySquareRegularExclusion` to assert that, for every `k ≥ 3`, no
simple `C₄`-free `2^k`-regular graph exists on `4^k` vertices. Lean proves

`not_erdos85Question_of_binarySquareRegularExclusion :
  BinarySquareRegularExclusion → ¬ Erdos85Question`.

The existence jaw comes from deleting the absolute nucleus of the
even-characteristic polarity graph; tight square-order candidates are forced
to be regular; and both unit defect components and bipartite defect components
are excluded. The remaining honest residue is A-REG-NONBIP. Its one-component
socket is stated by `BinarySquareConnectedNonbipartiteExclusion`, but no
uniform theorem currently routes every disconnected or mixed non-bipartite
partition into that socket. Thus Theorem B is a complete checked reduction,
not a proof of A-REG.

### Contributions and collaboration

Claude Fable led the certification pipeline and cold-integration verification,
the existence halves of the census, fleet operations, §8, and the final scope
review. GPT Sol developed the structural reductions,
negative map, and independent audits. The human operator set compute policy,
research priorities, authorship, scope, and the final read-through gate. The
shared room infrastructure supplied durable coordination, claims, review
gates, and a reproducible transcript; it is acknowledged as infrastructure,
not as an author. High-variance proposals were admitted only after independent
Lean elaboration or exact certificate replay.

---

## 0. Mathematical status: one uniform axiom remains

Let `f(n) = minDegreeForC4 n`, the minimum threshold such that every simple
graph on `n` vertices with minimum degree at least `f(n)` contains a `C₄`.
Erdős Problem 85 asks whether `f` is eventually nondecreasing.  The formal
reduction is complete: the negation is
equivalent to the existence of arbitrarily late strict drops
(`erdos85Negation_iff_not_question`), and a `q`-regular witness on `q²−1`
vertices together with nonexistence at `(q²,q)` produces such a drop
(`PlaneOrderDropWitness.strict_drop`).  Cofinally many such pincers therefore
refute the problem (`not_erdos85Question_of_cofinalPlaneOrderDropFamily`).

For `q = 2^k`, `k ≥ 3`, the existence jaw is already uniform: delete the
absolute nucleus from the even-characteristic polarity graph
(`Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus`), and the
resulting orders are cofinal
(`cofinalEvenFieldSquareExclusion_of_binary`).  On the nonexistence jaw, the
normalized square-order reduction is an equivalence
(`squareOrderTightCoreExists_iff_witness`,
`binarySquareOrderTightCoreExclusion_iff`), while parity forces every such
tight core to be regular (`squareOrder_regular_of_even`).  Consequently the
whole infinite theorem follows from one proposition:

> **A-REG (`BinarySquareRegularExclusion`).** For every `k ≥ 3`, there is no
> simple `C₄`-free `2^k`-regular graph on `2^k · 2^k = 4^k` vertices.

This is not shorthand for several hidden assumptions.  Lean proves directly
that A-REG implies the normalized tight-core exclusion
(`binarySquareOrderTightCoreExclusion_of_regularExclusion`) and hence the
negation of Erdős 85
(`not_erdos85Question_of_binarySquareRegularExclusion`).  Thus every arrow
from A-REG to the headline theorem is cold-green; A-REG itself remains an
axiom/conjecture, not a proved result (outline v2.64, §A.5; room msg 31964).

The defect operator makes the residue precise.  For a hypothetical regular
graph with adjacency matrix `A`,

`A² = (q−1)I + J − D`,

and `A` commutes with `D`
(`adjMatrix_sq_eq_sub_secondOrderDefect_of_regular`,
`adjMatrix_comm_secondOrderDefect_of_regular`).  Its defect components have
orders `q m_c`, with `Σ_c m_c = q`
(`binarySquare_regular_exists_defectComponent_partition`), and every vertex
of component `c` has exactly `m_c` graph-neighbours within that component
(`binarySquare_regular_degree_induce_defectComponent_eq_part`).  Unit
parts are impossible for even `q`
(`binarySquare_regular_no_sizeQ_defectComponent_of_even`), as are bipartite
defect components when `4 ∣ q`
(`binarySquare_regular_no_bipartite_defectComponent`).  What remains is
therefore exactly **A-REG-NONBIP**: all partitions `q = Σ m_c` with
`m_c ≥ 2` and every defect component non-bipartite.

The one-part subcase has an especially sharp equivalent formulation:

> **NONBIP-CONNECTED.** For binary `q ≥ 8`, every loopless `q`-regular
> `C₄`-free adjacency matrix `A` of order `q²` is singular.  Equivalently,
> its defect graph `D` is not connected, since
> `dim ker(A) = numberOfComponents(D) − 1`
> (`binarySquare_regular_finrank_adj_kernel_eq_card_components_sub_one`).

The formal branch socket is
`BinarySquareConnectedNonbipartiteExclusion`.  Its nonbipartite hypothesis
is now discharged literally for every regular binary-square candidate by
`binarySquare_twoPow_regular_defectGraph_not_bipartite` (with the stronger
per-component coloring exclusion
`binarySquare_twoPow_regular_no_bipartite_defectComponent`).  Its connected
hypothesis is different: there is currently no uniform Lean theorem routing
all disconnected or articulated defect graphs into this socket.  Such a
routing is closed only in the separate `q = 9` B.3 analysis.  Thus the
connected socket and the mixed nonbipartite partitions are sibling open
cases for binary `q`; connectivity must not be cited as a proved uniform
reduction.

This formulation includes all graph hypotheses; proving singularity from
generic regularity or spectrum alone would not suffice.  The campaign's
current mathematical frontier is the implication from the full symmetric
`C₄`-free incidence completion to that singularity statement.  Mixed
non-bipartite partitions remain a sibling subcase, not a consequence of the
connected case (outline v2.64, §E).

### Negative map: discarded routes are part of the result

The search did not merely fail to finish several familiar approaches; it
produced exact countermodels or reductions showing why they do not close the
remaining node.

- Determinant and Smith-normal-form arguments collapse to
  `det(A)² = q⁴ τ(D)`.  They show that the spanning-tree count of connected
  `D` is a square but do not force singularity; the uniform elimination is
  recorded at outline §A.5.3(i), commit `0ed91c72d6`.
- Spectrum-only and scalar moment inequalities are compatible with exact
  real spectral controls.  The uniform countermodel preserves the required
  even moments while allowing every odd trace obstruction to fail
  (outline §C/D, commit `f6ee2ed421`; divergence #66).
- Generic packing, Hall, code-LP and fractional-transversal statements omit
  the completion of all rows to one symmetric adjacency matrix.  The
  strongest faithful self-polar partial interface already has an exact
  half-integral survivor at `q=6`, so integrality does not follow from those
  hypotheses (`e401f3034f`; room msg 31951).
- The proposed P8 inverse-sign separation is impossible: exact product-sign
  identities force both signs among the relevant inverse entries.  The false
  terminal was retracted, not weakened (`19f227dced`; outline v2.62,
  room msgs 31962–31963).
- Pfaffian/mod-2 valuation, Ihara, exterior-power and Lefschetz variants
  reduce to the same determinant or spectral data.  Coherent-configuration,
  projective-completion and line-graph thresholds lack the required bridge;
  the latter premise already fails the `q=4` incidence control and connected
  spectral controls.  The ten-route audit and its no-survivor verdict are
  banked in `NONBIP_CONNECTED_LITERATURE_DIVERGENCE.md` at `cf2243a6e8`
  (room msgs 31957 and 31962).

These are scope statements, not impossibility theorems about every future
variant.  They say exactly which advertised hypotheses were too weak and
identify the missing input: a new invariant that uses the simultaneous
completion of *all* rows to a symmetric `q`-regular `C₄`-free `A`.  Recording
that boundary prevents a finite census, a partial incidence model, or a
conditional terminal from being mistaken for the uniform theorem.

---

## 1. Verification asymmetry

The campaign separates the cost of proposing a claim from the cost of
admitting it to the record.  Proposals may be fast and speculative; admission
requires either source elaboration under the pinned Lean toolchain or replay
of a checked certificate against the exact formal CNF.  The distinction is
visible in the inverse-potential episode.  At 17:46, a root-summed identity
was announced as `tr(A⁻¹)=q` (room msg 31890).  Five minutes later its
author re-expanded the all-pairs term, found that it was `q·1ᵀA⁻¹1=q²`
rather than `q·tr(A⁻¹)`, and withdrew the consequence (31895).  No Lean
wrapper or outline node had been built, so the correction cost minutes and
left no false theorem behind.

The same asymmetry governed the order-64 `h305` endpoint.  The first
certificate family used 80 owners, but the graph semantics required 88: the
missing eight were the antipodal shore pairs.  The mismatch was detected by
comparing the formal shore modes with the certificate universe, before the
endpoint was called proved (room msgs 31664, 31674, 31697; outline v2.64,
§A.5.2).  The corrected chain ends in
`false_of_h305_source_or_transported` and
`muNegThreeZeroFiveEndpointCallback_false`; the integrator then rebuilt the
full chain cold and printed the exact six Owner88 certificate axioms
(31809, 31845, 31882).  High-variance search is safe here because a plausible
certificate is evidence only after semantic identity and kernel replay.

## 2. Adversarial diversity

Different agents are useful only when they test different failure modes.
Review #939 did not merely repeat the inverse-potential derivation: it
re-derived P1–P7 and then inspected the exceptional root term.  That audit
found that the proposed sign dichotomy could be satisfied by the root itself
and forced the corrected domain `V \ (N(y) ∪ {y})` (31868–31874).  The
author then attacked the corrected statement and proved that its P8 sign
separation was itself impossible: a suitable defect-neighbour block has
zero potential sum, so it cannot be strictly negative pointwise.  A second
agent caught an overbroad sentence in that retraction—defect edges may also be
triangle-free graph edges—and supplied the necessary choice from
`N_D(y) \ N_A(y)` (31905, 31907, 31913).  The final correction is banked in
`19f227dced` and `0ae7069f40`.

Independent checking also corrected campaign accounting.  A manuscript
audit initially described the thirteen order-49 inputs as five one-high
cells plus one seven-high cell.  The host manifest listed the actual inputs:
four H3 scouts, three H5 cells, and six H7-t0 cubes.  The author retracted
that sentence within two minutes and corrected the draft (31989, 31994,
31997).  The lesson is narrower than "use multiple models": the reviewer
must inspect an independent invariant—the exact host manifest, a semantic
universe, or a boundary term—rather than replay the author's narrative.

## 3. The structure–compute exchange rate

The order-49 campaign gives a current, measured exchange.  Structural
normalization reduces seven H3/H5 monoliths to two checked cover formulas
and a `7×8` grid per cell.  Lean proves the accounting—392 positive cubes
plus fourteen covers—in
`orderFortyNineSmallHigh_positiveCube_job_count`, and proves their exhaustive
composition in `orderFortyNineSmallHigh_unsat_of_checkedCubeGrid`.  The host
therefore runs 406 bounded jobs instead of trusting a solver-side cube list
(31994).  When the campaign was fired, a separate audit found that these
grid results did not fit the older five-monolithic-LRAT socket: the cube
stack used the VariableHigh CNFs and returned `CNF.Unsat`, while the final
socket expected canonical `LRAT.check`s.  The missing semantic path was
formalized as
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat`
(`d0a17f358b`; room msg 32032) before the first verdict was needed.

The `h305` repair shows the reverse exchange.  Six honest 88-owner CNFs were
all externally UNSAT in seconds, but the expensive work was not search; it
was proving that the graph semantics map to those exact literals and modes.
That chain runs through `h305_crossExteriorSplit_of_profile`,
`muNegThreeZeroFiveCorrectFiniteSemantics_false`, and
`false_of_h305_source_or_transported` (outline v2.64, §A.5.2; 31882).
Compute locates a finite obstruction; structure determines whether the
obstruction says anything about the graph.

## 4. Persistence and the shape of a long campaign

The campaign state lives in four independent records: Lean sources and git
commits, the room transcript, the proof outline, and durable certificate
storage.  The outline is not a retrospective summary.  Operator goal #25
made it the allocation instrument: every root-to-leaf node is labelled
PROVEN, CERT, AXIOM, or GAP, and workers choose lanes against that tree
(outline v2.64, §G; goal #25).  This prevented a long finite endpoint from
silently becoming the whole project: order-64 `h305` was parked when its
premise was underived, then reopened by goal #38 after the operator chose the
endpoint audit.  The reopened audit discovered the 80/88 mismatch, rebuilt
the honest universe, and closed the endpoint in one day at `802f6d79d3` and
`778a2e1595` (31664–31682, 31849).  Persistence here means preserving enough
state to restart from the actual boundary, not merely keeping a process
alive.

The same rule governs compute.  Goal #39 required a pre-fire manifest with
all thirteen input hashes, tool hashes, job order, caps, storage exclusions,
and deletion policy.  The posted manifest verified all thirteen SHA-256
entries before launching a solver (31994).  A verdict without that durable
provenance is not campaign progress, even if the process printed `UNSAT`.

## 5. Honest scoping

Every status word names its scope.  The callback theorem
`muNegThreeZeroFiveEndpointCallback_false` carries the foundational axioms
plus exactly six disclosed Owner88 `native_decide` checks.  The broader
`orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected` additionally
inherits the older FullClosure certificate family; the integrator printed
both lists separately rather than reporting the smaller list for the larger
theorem (31845, 31846, 31882).  It closes the disconnected size-two subtree
at order 64, not NONBIP-CONNECTED and not A-REG.

The same discipline permits the stronger order-49 status only after the
generated frontier has passed kernel replay, cold integration, and the literal
axiom audit. The operator has accepted Theorem A as the decided finite-drop
headline; this working revision records its final evidence gate as pending.
Once discharged, that statement still does not enlarge into a solution of
eventual monotonicity. The release manuscript will say “drop proved” for
48-to-49 only after that gate and “conditional reduction” for
A-REG-to-`¬ Erdos85Question`; it never exchanges one scope for the other. The
distinction is enforced by outline §F and operator goal #40.

## 6. The thin human role

The human role is thin but decisive at branch points.  Goal #36 did not
suggest a lemma; it imposed a stuck test: if workers cannot name every link
from recent banks to the terminal, they must stop, search outside first,
diverge widely, and report refutations as results.  That rule ended the
inverse-potential lane after P8, fractional-cover integrality, and divergence
#68 all failed (31951–31964).  Goal #38 separately chose to reopen the parked
`h305` endpoint; goal #39 authorized the certificate campaign that closes the
currently launched H3/H5/H7 finite cells but cannot decide 48/49 without a
separate H1 closure; goal #40 commissioned this manuscript in parallel.
These are portfolio and governance decisions.  The mathematical
claims still pass through Lean or certificate replay, and nothing goes
external before operator review (31965, 31970).

## 7. Why Erdős problems

Erdős 85 exposes several proof currencies at once: an elementary extremal
statement, uniform finite-field witnesses, exact graph reductions, spectral
and incidence structure, and finite certificate endpoints.  Each partial
claim has a precise interface.  A-REG would close the uniform theorem through
`not_erdos85Question_of_binarySquareRegularExclusion`; the order-49 campaign
would close one finite drop through the small-high socket; and the order-64
work can honestly report a closed signed-joint subtree while leaving the
connected defect frontier open (outline v2.64, §0, §A.5, §B.1).  That
granularity makes the problem a useful test of whether a machine
collaboration can accumulate durable mathematics without confusing a large
amount of verified local work with a solved root problem.

---

## Silence is not success (a recurring failure class)

Silence fails at the mathematical level too.  The false trace identity in
31890 looked plausible because no term visibly objected; an explicit
re-expansion produced the positive evidence of cancellation and triggered
the retraction at 31895.  P8 survived a thousand sampled `q=4` models only
because those models were singular and therefore never instantiated the
inverse hypothesis; the correct response was `UNKNOWN`, not support
(31886).  A direct block-sum argument then proved that P8 was impossible in
every hypothetical survivor (31905–31913).

The same standard applies operationally.  A solver cell counts only when its
ledger line contains a verdict, return code, input hash, proof-check status,
LRAT hash, and upload status; a missing line is not an UNSAT.  A Lean file
counts only after the named target elaborates and its `#print axioms` output
is inspected.  On 25 August the `h305` dependency chain ran for nearly an
hour, but the room did not infer success from the absence of errors: three
agents waited for the final file check and separately reported its axiom
scope (31845, 31846, 31882).  Positive artifacts, rather than quiet logs,
are the unit of trust.

## Methods (summary)

- **Room protocol**: persistent SQLite chat; claim → red-team → formalize
  → relay-merge → independent cold audit. Relay cadence: every push to
  the working branch is merged to the mirror branch by the counterpart.
- **Cold-audit rule**: "verified" means the file elaborates from source
  under the pinned toolchain (v4.31.0 + pinned mathlib) in an
  independent environment, unfiltered, with verbatim `#print axioms` on
  the public theorems. Adopted after the stale-cache incident; upgraded
  after the rg-mask incident.
- **Certificate factory**: exact DIMACS emitters with input hashes;
  kissat/cadical portfolios; DRAT/LRAT replay; compressed artifacts plus a
  manifest on durable storage; and resumable per-verdict queues.  A SAT
  result becomes mathematical evidence only after a semantic bridge proves
  that every graph in the stated stratum satisfies the exact checked CNF.
  The order-49 campaign currently uses the checked-grid interface
  `orderFortyNineSmallHigh_unsat_of_checkedCubeGrid`; its 406 jobs are seven
  7-by-8 positive-cube grids plus fourteen negative-cover checks, not five
  monolithic LRAT files (room msgs 31965 and 31971).
- **Census tooling**: exhaustive B&B sweeps over partition/atom spaces
  with every constraint tied to a named Lean lemma (loads, budgets,
  balance integrality, the equal-LCM law, oriented-cover kernels).

## Results and evidence map

The paper has two different logical endpoints and keeps them separate.
Theorem A is the unconditional finite result targeted by the active final
replay gate: the adjacent values at 48 and 49 are decided exactly once its
generated endpoints pass the recorded cold-build and axiom audit. Theorem B is
a uniform conditional result: the negation
of Erdős 85 follows from A-REG, while A-REG itself remains open. The
implications from an unbounded family of plane-order drops to the negation of
Erdős 85 are proved as `erdos85Negation_iff_not_question`,
`PlaneOrderDropWitness.strict_drop`, and
`not_erdos85Question_of_cofinalPlaneOrderDropFamily`. On the binary branch,
the existence jaw, tight-core reduction, and even-order regularity are proved
by `Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus`,
`binarySquareOrderTightCoreExclusion_iff`, and
`squareOrder_regular_of_even`. The checked capstone is
`not_erdos85Question_of_binarySquareRegularExclusion`.

The strongest unconditional uniform reduction beneath A-REG is already
substantial.  The defect operator satisfies
`A² = (q−1)I + J − D` and commutes with `A`
(`adjMatrix_sq_eq_sub_secondOrderDefect_of_regular` and
`adjMatrix_comm_secondOrderDefect_of_regular`).  Its components have orders
`q m_c`, with `Σm_c=q`; unit parts are impossible; and no component is
bipartite when `4 ∣ q`
(`binarySquare_regular_exists_defectComponent_partition`,
`binarySquare_regular_no_sizeQ_defectComponent_of_even`, and
`binarySquare_regular_no_bipartite_defectComponent`).  What remains is the
all-non-bipartite connected-or-mixed node A-REG-NONBIP; the post-inverse
divergence found no surviving terminal (room msgs 31962–31964).

### The decided 48-to-49 campaign

Theorem A combines two checked witness ingredients—a 48-vertex degree-seven
`C₄`-free witness and a 49-vertex degree-six witness—with certificate-backed
nonexistence of a 49-vertex minimum-degree-seven witness. The graph-to-CNF consumer
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat`
assembles the one-, three-, five-, and seven-high exclusions. The finite-drop
core then yields the exact thresholds and strict inequality. The certificate
universe, its structural decomposition, and the final dependency-cone audit
belong to the proof evidence for Theorem A; they are not a third headline
result.

The order-48 existence input deserves separate notice. An independent NetworkX
check over archived graph6 artifacts finds the checked extremal witness
non-isomorphic to the Afzaly–McKay record, providing a second realization at
the same extremal parameters. This comparison is reproducible computation
rather than a Lean theorem; its script and graph6 inputs must be included in
the release artifact and cited separately from the generated Lean endpoint.

The campaign's operational scale explains the hybrid proof architecture. The
authoritative H1 capacity universe contains 13,351 rows, while the higher
strata decompose into checked cover and cube interfaces. SAT search produces
LRAT evidence; Lean fixes the graph semantics, inventory bijections, and final
composition. Receipts are resumability bookkeeping. The proof trust root is
the kernel replay, clean cold integration build, and literal public-theorem
axiom audit required by mandate 1318.

### The 63-to-64 campaign: useful finite evidence, still open

At `q=8`, the possible defect-component partitions are
`[2,2,2,2]`, `[3,3,2]`, `[4,2,2]`, `[4,4]`, `[5,3]`, `[6,2]`, and `[8]`.
They are not all excluded.  The size-two `μ=3` sector is closed on honest
regular hypotheses by `orderSixtyFour_regular_sizeTwoEigenline_false`.
The complete negative signed-joint size-two subtree, including the corrected
`μ=-3,(0,5)` endpoint, is closed by
`orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected`.  But
`[3,3,2]`, `[4,2,2]`, and `[6,2]` retain non-bipartite cases; `[4,4]` and
`[5,3]` have only partial owner-nullity information; and the connected `[8]`
case remains a gap.  The eleven `[2,2,2,2]` assembly targets are external
UNSAT verdicts without certificates.  Therefore `63→64` is **not a decided
drop**, and none of these order-64 enumerations proves the uniform A-REG
statement (outline v2.64, §A.5.2).

### Certificate case study: the h305 80-owner error and 88-owner repair

The `μ=-3,(0,5)` endpoint is a compact example of why hypothesis fidelity
matters more than an UNSAT line.  The first encoding silently reused the
h114 shore table: eight fixed owners per shore and 80 candidate owners.  The
actual h305 shore modes contain antipodal offsets as well, giving twelve
fixed edges per shore and an 88-owner universe.  Consequently the original
80-owner UNSAT result excluded only a strengthened, wrong problem (room msgs
31664, 31674, and 31697; outline v2.64 change entry 2.61).

The repair rebuilt the whole chain around the honest table.  Six canonical
88-owner CNFs were emitted independently and agreed byte-for-byte; all six
were UNSAT, and their LRAT payloads are checked by the six `h305Owner88*_check`
theorems in `Erdos85MuNegThreeZeroFiveCorrectOwnerCertificate`.  The graph
semantics culminate in `muNegThreeZeroFiveCorrect_graph_false_of_exterior`,
the source/transport endpoint in `false_of_h305_source_or_transported`, and
the callback-free order-64 consumer above.  The six checked payloads contribute
exactly six disclosed theorem-specific compiler-generated `native_decide`
axioms to this corrected endpoint;
all structural bridge modules use standard axioms.  The result is genuinely
`PROVEN-AT-64 CERT`, but only for that endpoint—not for the full order-64
nonexistence theorem (room msgs 31845–31846 and outline v2.64 entry 2.61).

## 8. Interpretation: a finite theorem and an honest infinite frontier

After its final replay gate, Theorem A answers a natural finite extremal
question exactly and supplies a concrete failure of monotonicity. It does not
by itself decide eventual monotonicity: one drop at 48-to-49 is compatible with either answer to Erdős
85. Its broader value is methodological and structural. The proof combines a
new extremal witness with a complete nonexistence certificate at the next
order, and exposes a reusable interface between finite graph normalization,
SAT certificates, and kernel checking.

Theorem B identifies what would turn this phenomenon into an infinite family.
It is deliberately stated as a reduction from the single proposition A-REG.
The evidence is mixed. Even-characteristic polarity graphs supply the
cofinal existence jaw, and the binary-square defect calculus removes unit and
bipartite components. Against that, the Lean-checked orders 15 and 16 and the
published order-35/36 table entries show no drop, the `q=4` analogue is false,
and every attempted generic terminal for the remaining non-bipartite
completion problem has failed or exposed a weaker hypothesis. A-REG is
therefore the live mathematical frontier, not a conclusion licensed by the
finite data.

The operator's plane-order interpretation is the principal rival: special
orders may organize both the constructions and the obstructions without the
binary regular-exclusion pattern persisting uniformly. Publishing the twin
result makes that disagreement useful. The checked reduction states exactly
what a proof of the negative answer must supply; the negative map states which
plausible shortcuts do not supply it; and the finite drop provides a fully
decided calibration point for future theory.

This section is owned by Claude Fable for the final scope-honesty read. Before
external release it must be reconciled with the final cold-build and literal
axiom-audit record, the exact theorem names for the completed order-49
frontier, the witness non-isomorphism artifact, and a consumed-tag ledger count
of exactly 13,351 at freeze. No operational receipt or fleet count substitutes
for those mathematical artifacts.
