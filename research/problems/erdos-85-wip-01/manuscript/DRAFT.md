# Computational Evidence for a Drop and a Uniform Reduction for Erdős Problem 85

**Claude Fable and GPT Sol**

**Status.** Working manuscript. Nothing in this document is for external
distribution before the operator read-through and Zenodo gate. Formal claims
refer to Lean 4.31.0 with the repository-pinned mathlib. Result A is a
computational claim, subject to completion of the two-solver H1 gap census;
it is not a proved finite theorem. The conditional finite-drop core is Lean
checked, but its order-49 nonexistence hypothesis has not been discharged.
The operator has cancelled certificate replay and production for this paper.
Theorem B is the Lean-checked conditional reduction to A-REG, which itself
remains open.

## Abstract

Let `f(n) = minDegreeForC4 n`, the minimum threshold such that every simple
graph on `n` vertices with minimum degree at least `f(n)` contains a `C₄`.
We report two complementary results. First, the current computation supports
the adjacent-value claim, with the H1 gap census still in progress:

`f(48) = 8` and `f(49) = 7`,

which would give a strict finite drop. The lower side uses a 48-vertex
extremal witness checked in Lean through `native_decide` (six named
`native_decide` axioms in total for the two witness endpoints; a preliminary
`#print axioms` audit is banked as `AXIOM_AUDIT_OVERLAY_20260916.md`); an independently computed isomorphism check finds
it non-isomorphic to the previously recorded Afzaly–McKay witness. For the
order-49 upper side, structural reductions and archived SAT evidence have
different verification levels; the remaining H1 rows are being tested by two
independent solvers without proof certificates. Second, we reduce
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

### Result A — computational evidence for a 48-to-49 drop

The combined evidence supports the adjacent-value claim

`minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7`,

and consequently the proposed strict drop

`minDegreeForC4 49 < minDegreeForC4 48`.

This is a computational result, not an unconditional Lean theorem. Rows that
reach a declared solver cap remain open and prevent a complete computational
claim. Even if all rows return UNSAT, proof certificates would still be needed
for a formal theorem.

The already checked finite-drop core is
`minDegreeForC4_fortyEight_fortyNine_exact_checked` and
`minDegreeForC4_fortyNine_lt_fortyEight_checked`; both take the order-49
nonexistence hypothesis. The conditional generated endpoints are specified as
`minDegreeForC4_fortyEight_fortyNine_exact_of_generatedSevenBaseCertificates`
and
`minDegreeForC4_fortyNine_lt_fortyEight_of_generatedSevenBaseCertificates`.
They would prove the finite drop only after every input is supplied, the
generated module lands, and a cold build and literal axiom audit pass. No
conjectural uniform hypothesis enters this finite computation. Separately,
an independently computed NetworkX
isomorphism comparison of archived graph6 artifacts finds that the checked
order-48 extremal graph is not isomorphic to the Afzaly–McKay record; this
novelty check is not part of the Lean-elaborated theorem, and that theorem's
witness side rests on `native_decide`, not on a standard-axiom-only kernel proof.

### Evidence levels and formal obligations for Result A

The evidence classes below are not a partition: the historical 96 H1 roots,
the existing certificate-object inventory, and the Phase B root set use
different selections of the same capacity tags. No row is promoted from a
solver verdict or an archived proof object to a kernel-checked theorem.

| Class | Current evidence | Limit for this paper |
|---|---|---|
| Order 48 and 49 lower witnesses | Finite graphs in `Erdos85FiniteDropWitnesses.lean`, elaborated in Lean via `native_decide`; the preliminary `#print axioms` audit lists three `native_decide` axioms per witness endpoint, and independent edge-list audits (168 edges, all pair codegrees ≤ 1) corroborate both graphs | Establish the lower sides only; not standard-axiom-only. |
| H3/H5 | Reviewed paper/computation cover and archived local proof receipts | Generated formal aggregate and public axiom audit are absent. |
| H7 | All 28 surviving structural roots covered after 15 singleton-capacity exclusions (`H7_CLOSURE_20260915.md`) | Paper/computation closure; the Lean evidence-vector arguments remain uninstantiated. |
| H1 historical overlay | 96 reviewed historical cases with archived `drat-trim` verification (`phase_b_historical_overlay_96/`) | Historical checks are not a current kernel replay. |
| H1 existing bank | 12,019 historical ready certificate inputs in the replay sizing model | Object and metadata availability do not establish a completed kernel replay. |
| H1 gaps | 1,288 capacity tags lack listed certificate objects in the banked snapshot; 1,161 residual Phase B roots are a related, overlapping decomposition | Two independent verdict-only solver runs and receipts are planned. Any cap hit stays open; no proof certificate is produced. |

The last row is unfinished at this draft revision. Its final reported count
must come from exact tag and CNF joins of the solver receipts, not a sum of
the overlapping inventory counts. A complete set of two-solver UNSAT verdicts
would support Result A computationally; it would still leave the formal
nonexistence theorem unproved.

The mathematical dependency chain is independent of how the computation is
scheduled. The checked witness module `Erdos85FiniteDropWitnesses.lean`
supplies `boza48_degreeSeven_witness` and
`orderFortyNine_degreeSix_witness`. Its exact-value theorem still takes
`hno49 : ¬ C4FreeMinDegreeWitness 49 7`. No completed-certificate count by
itself supplies this hypothesis.

The source-level consumer
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks` in
`Erdos85OrderFortyNineSmallHighVerifiedFrontier.lean` requires four inputs:

| Sector | Required input to this consumer |
|---|---|
| H1 | `OrderFortyNineStratumExcluded 1` |
| H3 | Checked LRAT proofs for both representative indices `index ≤ 1` |
| H5 | Checked LRAT proofs for all three representative indices `index ≤ 2` |
| H7 | `OrderFortyNineStratumExcluded 7` |

For H3 and H5, the checked formulas are precisely
`orderFortyNineGeneratedCanonicalSatCnf` applied to
`threeHighRepresentativeMasks` or `fiveHighRepresentativeMasks`. This is an
interface description, not a claim that five monolithic certificates are
available or that five jobs suffice. The finer cube route instead supplies
seven base-CNF `Unsat` proofs to
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat`
in `Erdos85OrderFortyNineSmallHighCubeGridTerminal.lean`. It reaches the same
`hno49` conclusion without constructing the five existential LRAT arrays of
the older consumer. The finite-drop core accepts either route. H1 capacity
rows still need the full row-to-stratum assembly. The H7 structural ledger
`H7_CLOSURE_20260915.md` covers all 28 roots that survive the 15 singleton
capacity exclusions at the paper/computation level. This does not yet
instantiate the Lean capstone
`orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors`, whose
statement still takes four evidence-vector arguments of lengths 19/15/7/2.
H1 still has a root-coverage campaign; H7's formal evidence bridge and the
final generated aggregate remain open proof obligations.

The companion closure inventory records the chosen route for each sector,
its missing artifacts, and replay obligations. Its counts and cost estimates
are operational evidence, not additional theorem hypotheses. A future formal
closure would require the exact cover and semantic bridges, certificate
replay for every necessary row, the generated aggregate, and a cold build
with literal axiom audits of the two public exact-value/drop endpoints.
None of these steps follows from verdict-only UNSAT results.

### Cost to verify Result A formally

The cancelled replay plan is retained as a reproducible cost model, not an
active launch plan. For 12,019 historical ready certificate inputs, its
byte-weighted model estimates 4,831 compile box-hours. With the plan's 25%
noncompile allowance, 10% spot-loss factor, and eight bootstrap hours, this
becomes about 6,651 box-hours: **17.32 ideal allocated days on 16 hosts** and
**about $1,276 of infrastructure** at the sampled spot, gp3 and IPv4 rates
(`sat49/H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md`). Retrieval is additional: a
full 6.06 TB pass at the cited Glacier Instant Retrieval rate of $0.03/GB
would cost about $182 before requests, repeat reads, output storage or other
services. No replay wave is authorized by this estimate.

The missing-certificate production cost is unresolved. An early **rough
$2,600 proxy** multiplied 1,288 gaps by a 10-hour claim-to-ledger interval;
the worker logs show that interval includes queue and pipeline time, so it
must not be used as a solver-time forecast. The later v3 readback finds
574 verified-UNSAT solves with a 4,011-second median and a 4,539-second mean,
and 22 UNKNOWN rows at a 14,400-second cap
(`sat49/H1_V3_SOLVER_TIMING_20260916.md`). The unproved rows are selected for
difficulty, and proof logging, trimming, splits and retries have no measured
cost model here. Thus the gap-certificate figure is a historical planning
proxy, not a credible fixed price. A public requester-pays copy of the
existing certificate bank could let others fund independent verification,
subject to the operator's publication gate and an exact release manifest.

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

- The identity `det(A)² = q⁴ τ(D)` makes a square spanning-tree count
  necessary when `D` is connected. Controls show that this condition alone
  does not force singularity (outline §A.5.3(i), `0ed91c72d6`). This does
  not exclude stronger integral or local arithmetic tests: later examples
  fail precisely such tests.
- Real spectral controls satisfy the particular scalar conditions recorded
  in their reports (`f6ee2ed421`; divergence #66). They do not establish
  integral adjacency realizability or compatibility with every odd-trace
  condition. Later Hoffman-diagonal and odd-power arguments reject
  particular proposed spectra; these rejections and the remaining scope
  are recorded in outline versions 2.66–2.69.3.
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

The subsequent cycle produced several further boundaries with independently
reviewed scope (`CUTS_LEDGER_DRAFT.md`, rows 172–186):

- A core-Lean partial common-neighbour reconstruction identifies the exact
  graph problem in operation form. A separate prose construction, checked
  at finite field examples, refutes same-carrier Hamming stability based
  only on the total central law's failure rate. It does not refute every
  possible additional operation identity
  (`PARTIAL_CENTRAL_OPERATION_AUDIT.md`).
- The interval circulant defect family with steps
  `{q²/2, ±1, …, ±(q/2−1)}` is excluded for every binary `q ≥ 4` by a
  reviewed cyclotomic argument (`l6-cyclic-trace/UNIFORM.md`). Specific
  order-256 defects also fail rational congruence to the identity form,
  as witnessed by local Hasse invariants (`l6-representability/`). The
  recorded D16 additionally fails the mod-2 alternating-root test; the
  interval `r = 4` example passes the 2-adic representability test but
  fails at odd primes. These are family exclusions, with no reduction of
  arbitrary defect graphs to those families.
- No proper divisible design graph has odd degree `k ≥ 3` and
  common-neighbour parameters `λ₁ = 0, λ₂ = 1`. Reviewed geometric
  arguments also rule out loopless polarities preserving the
  Baer-deleted incidence structure. Matching-repair and retained-pencil bounds rule out stated
  support and deletion budgets. None excludes arbitrary global repairs
  (`baer-repair-gate/`, `BAER_POLARITY_EXTENSION.md`,
  `retained-subplane-gate/`).
- Explicit regular connected nonbipartite defect graphs pass the full
  alternating symmetric square-root test over `F₂`, but the same family
  fails the determinant-square condition uniformly. This separates the
  two necessary tests; it supplies no survivor of their conjunction
  (`mod2-root-gate/`).

- The stated five-vertex flag relaxation is feasible uniformly for binary
  `q ≥ 16` after repairing the original witnesses to satisfy
  `tr(A D²) ≥ 0`; this includes the listed 23 identities and eight Gram
  families, not every possible five-vertex constraint (ledger row 175).
  The aggregate mod-3 census is feasible for every odd exponent `k ≥ 5`
  (row 174), and the projected fixed-shore bound `z ≤ q−1` is refuted by
  a uniform `z = q` construction (row 176). The specified enlargement of
  an even-order polarity graph to degree `q+1` on `(q+1)²−3` vertices
  requires at least `q²/4` old-edge deletions for `q ≥ 16` (row 180);
  it excludes repairs with only linearly many deletions, not all repairs.

The algebraic and geometric arguments in these reports are reviewed prose
unless a named Lean result is explicitly identified. Their computational
checks are evidence for their stated examples, not universal certificates.

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

The same discipline keeps Result A at its computational evidence level.
The operator cancelled certificate production and replay for this paper;
the two-solver H1 census is the remaining empirical gate. Even a completed
census would not prove eventual monotonicity false, since one drop does not
settle an eventual property. The release manuscript will distinguish a
computationally supported 48-to-49 drop from the Lean-checked conditional
reduction A-REG-to-`¬ Erdos85Question`.

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
formal claims still pass through Lean or certificate replay, and nothing goes
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
  One recorded order-49 decomposition uses the checked-grid interface
  `orderFortyNineSmallHigh_unsat_of_checkedCubeGrid`: 406 jobs comprising
  seven 7-by-8 positive-cube grids and fourteen negative-cover checks
  (room msgs 31965 and 31971). This historical decomposition is not a
  current pending-job count; the closure inventory must reconcile it with
  later covers and completed artifacts.
- **Census tooling**: exhaustive B&B sweeps over partition/atom spaces
  with every constraint tied to a named Lean lemma (loads, budgets,
  balance integrality, the equal-LCM law, oriented-cover kernels).

## Results and evidence map

The paper has two different logical endpoints and keeps them separate.
Result A is a finite computational claim whose H1 verdict-only census remains
open at this revision. It does not carry the status of an unconditional Lean
theorem. Theorem B is a uniform conditional result: the negation
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

### The computational 48-to-49 campaign

Result A combines two checked witness ingredients—a 48-vertex degree-seven
`C₄`-free witness and a 49-vertex degree-six witness—with heterogeneous
evidence against a 49-vertex minimum-degree-seven witness. The graph-to-CNF consumer
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat`
assembles the one-, three-, five-, and seven-high exclusions. The finite-drop
core would yield the exact thresholds and strict inequality if the
nonexistence hypothesis were proved. The certificate universe, its structural
decomposition, and the dependency-cone audit describe what formal
verification would require; they are not a third headline result.

The order-48 existence input deserves separate notice. An independent NetworkX
check over archived graph6 artifacts finds the checked extremal witness
non-isomorphic to the Afzaly–McKay record, providing a second realization at
the same extremal parameters. This comparison is reproducible computation
rather than a Lean theorem; its script and graph6 inputs must be included in
the release artifact and cited separately from the generated Lean endpoint.
They are archived in `sat49/verify_boza48_nonisomorphism.py` and
`sat49/data/`.

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

### Plane-order censuses and the literature boundary

The order-80 search for a 9-regular `C₄`-free graph, which would supply the
`q=9` existence jaw, is unresolved. All 20 authorized q9 solver attempts
ended UNKNOWN under their caps; the independently checked positive controls
returned SAT, but neither is an order-80 witness. The same campaign also
left the order-78 existence cases open. Its 48-hour ledger is frozen in
`q9_solver_controls/Q9_EXISTENCE_DECISION_20260911.md`. An UNKNOWN is not
evidence of nonexistence.

The complete finite-group Cayley census examined 52 groups of order 80,
47 of order 120, and 57 of order 168 with inverse-closed connection sets
of degree 9, 11, and 13 respectively. Every input returned UNSAT; the
reviewed encoding and table audits cover all these groups
(`cayley-census-q11-q13/CAYLEY_CENSUS_Q11_Q13_20260913.md`). This excludes
the specified Cayley families, not arbitrary graphs at those orders. The
same census found one order-48, degree-7 Cayley witness among 52 groups.

The deductions from [Zhang–Chen–Cheng's polarity-graph result](https://doi.org/10.1016/j.disc.2016.12.005)
and [Boza's bounds](https://arxiv.org/abs/2409.12770) put the adjacent
star-Ramsey values at
`r(109) ∈ {120,121}` and `r(155) ∈ {168,169}`, where
`r(s)=R(C₄,K₁,ₛ)` (`cayley-census-q11-q13/LITERATURE_CHECK_20260915.md`).
The upper choice in either pair is equivalent to existence of the relevant
11- or 13-regular graph on 120 or 168 vertices. The Cayley census cannot
select the unrestricted value. The cited literature check found no exact
determination of these two values within its stated search scope; this is
not a claim that none exists.

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

## 8. Interpretation: a computational drop, an honest infinite frontier, and the price of certainty

Result A is computational evidence, not a theorem, and this section is
written so that it can be read standing alone. The lower sides of both values
are explicit witnesses elaborated in Lean through `native_decide`, which adds
six named trust axioms beyond Lean's standard three; only Theorem B is
standard-axiom-only in the preliminary `#print axioms` audit. The upper side at order 49 is a case split into
the strata H1, H3, H5 and H7. Three of the four are closed at the level of a
paper argument backed by reproducible, independently reviewed computation with
banked receipts; the H1 rows are to be settled by a verdict-only census, still
in progress at this draft revision, in which two independent SAT solvers must
both return UNSAT under a declared cap, and every row that reaches the cap is
listed as open in the final table rather than absorbed. If that table shows no
open row, the honest statement will be that we have strong computational evidence that `f(48) = 8` and `f(49) = 7`, and
therefore that the threshold drops between two adjacent orders. Erdős
Problem 85 asks whether `f(n+1) ≥ f(n)` holds for all large `n`. One drop at
48-to-49 is a data point against monotonicity at small order; it is
compatible with either answer to the problem as posed, which a finite
computation cannot settle, and we make no claim about the problem itself.

We chose to stop at belief and publish the price of certainty. A bank of
12,019 historical ready certificate inputs for the H1 rows is inventoried
(objects and metadata, not yet validated payload by payload); replaying it
through the Lean kernel is a priced, bounded task (about $1,276 of spot infrastructure
and 17 ideal allocated days on 16 hosts, plus about $182 of retrieval), and the
remaining rows have no credible fixed price because they were selected by
difficulty. The certificate bank can be released as a requester-pays object
store with an exact manifest, so that anyone who wants Result A promoted to a
kernel-checked theorem can pay for exactly that and nothing else. The trust
boundary is stated rather than hidden: two solvers agreeing under a cap is
evidence about solver behaviour, not a proof; the H7 source enumeration rests
on an audited program rather than an independent replay; and the archived H1
certificates were checked by `drat-trim` at production time, not by a current
kernel replay.

Theorem B identifies what would turn a single drop into an infinite family.
It is deliberately stated as a reduction from the one proposition A-REG. The
evidence is mixed. Even-characteristic polarity graphs supply the cofinal
existence jaw, and the binary-square defect calculus removes unit and
bipartite components. Against that, the Lean-checked orders 15 and 16 and the
published order-35/36 table entries show no drop, the `q = 4` analogue is
false, and every attempted generic terminal for the remaining non-bipartite
completion problem has failed or exposed a weaker hypothesis. A-REG is the
live mathematical frontier, not a conclusion licensed by the finite data. The
operator's plane-order interpretation is the principal rival: special orders
may organize both the constructions and the obstructions without the binary
regular-exclusion pattern persisting uniformly. Publishing the twin result
makes that disagreement useful: the checked reduction states exactly what a
proof of the negative answer must supply, the negative map states which
plausible shortcuts do not supply it, and Result A provides a concrete
calibration point for future theory.

This section is owned by Claude Fable for the final scope-honesty read.
Before external release it must be reconciled with three artifacts and
nothing else: the receipt-derived H1 census table (an exact join of the
two-solver UNSAT rows to the 1,288 gap tags, the 96 historical rows and the
12,019 certificate rows, with the open list, if any, printed in full); the
exact Lean theorem names and the literal `#print axioms` output for every
checked piece cited above (the witnesses, the conditional finite-drop core,
and Theorem B); and, if the requester-pays copy is published, the release
manifest of the certificate bank. No operational receipt, fleet count or
verdict summary substitutes for those artifacts.
