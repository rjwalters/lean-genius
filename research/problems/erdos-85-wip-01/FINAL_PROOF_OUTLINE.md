# Final proof outline: Erdős 85 is false

**Version 2.12 — 2026-08-20 (packing-bound node: q-generic reciprocity-vs-uniformity mechanism PROVEN, scale gap recorded).**

As of v2.5, `PROVEN` means **green on a cold build of `erdos85/integration`**.
The v2.2 baseline was tip `e304275e85` (1,645/1,649 modules; audit logs in
`erdos85-cayley-sidon/integ_capstone_audit.log`). Its three named failures
have since been repaired and banked; 32 dead importers of deleted roots were
removed. Cold sweep #3 is running at the v2.3 bump, with one known live drift
candidate (`Erdos85SquareOrderResidualFourthMoment`) and no capstone failure.

This is the single authoritative outline. It supersedes the four divergent v1
copies, archived unchanged beside it as `FINAL_PROOF_OUTLINE_v1a.md` (sol-1
branch, 1,510 lines), `_v1b.md` (sol-2, 3,639 lines), `_v1c.md` (sol-3, 1,624
lines), `_v1d.md` (Claude, 1,359 lines). Those are the ledger of what was
proved and tried through 2026-08-18 14:00Z; nothing in them is lost, and
nothing in them is the map any more.

Rules of this document:

- It lives on `erdos85/integration` at this path. There is exactly one copy. Per-branch
  copies are frozen; do not edit them.
- It is a critical-path map, not a ledger. A theorem earns a line here only if
  it changes the status of a node below. Everything else is recorded in the
  ledger (v1b remains the fullest one) or in the room.
- Labels: `PROVEN` (uniform Lean theorem, name given) · `PROVEN-AT-64` (q=8
  only; if certificate-backed, `Lean.ofReduceBool` is in the axiom set and
  the label says `CERT`) · `EXTERNAL` (solver signal, no certificate) ·
  `AXIOM` (precise conjecture that would close its parent) · `GAP` (no
  candidate statement).
- Version bumps: patch (2.0 → 2.1) when a node's status changes; minor
  (2 → 3) when the tree's shape changes. Every bump appends to the change
  log at the end. The room is self-directed: any agent may edit, then posts
  the delta and theorem names for a red-team window.
- The document must stay short enough for the operator to read in one
  sitting. If it does not, that is the defect to fix first.

---

## 0. The theorem and the root — implications PROVEN; root CONDITIONAL on A-REG

Erdős 85 asks whether `f(n) = minDegreeForC4 n` is eventually monotone. The
campaign's claim: it is not; `f` drops at plane-order squares infinitely often.

- `PROVEN` `erdos85Negation_iff_not_question` — negation ⇔ arbitrarily large
  strict drops `f(n+1) < f(n)`.
- `PROVEN` `PlaneOrderDropWitness.strict_drop` — a witness on `q²−1`
  vertices with min degree `q`, plus nonexistence on `q²`, gives one drop.
- `PROVEN` `not_erdos85Question_of_cofinalPlaneOrderDropFamily` — cofinally
  many such pincers refute Erdős 85.

**Root task:** exhibit pincers for an unbounded set of `q`. Two families;
either alone suffices. Branch A is the critical path.

---

## A. Binary branch, `q = 2^k`, `k ≥ 3` — the critical path

| node | status | theorem |
|---|---|---|
| A.1 existence jaw on `q²−1` | `PROVEN` | `Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus`; cofinal via `cofinalEvenFieldSquareExclusion_of_binary` |
| A.2 reduce `q²` nonexistence to a normalized tight core | `PROVEN` | `squareOrderTightCoreExists_iff_witness`, `binarySquareOrderTightCoreExclusion_iff` |
| A.3 tight core is regular for even `q` | `PROVEN` | `squareOrder_regular_of_even` |
| A.4 capstone: A-REG ⇒ ¬Erdős 85 | `PROVEN` | `binarySquareOrderTightCoreExclusion_of_regularExclusion`, `not_erdos85Question_of_binarySquareRegularExclusion` (integration-built, standard axioms) |
| **A.5 AXIOM A-REG** | **`AXIOM` — the only open node of Branch A** | `BinarySquareRegularExclusion`: for every `k ≥ 3`, no `2^k`-regular C4-free graph on `4^k` vertices |

Everything below this line is inside A.5.

### A.5.1 What is proven uniformly beneath A-REG (all `q = 2^k`, standard axioms)

- Defect operator `A² = (q−1)I + J − D`, commuting with `A`
  (`adjMatrix_sq_eq_sub_secondOrderDefect_of_regular`,
  `adjMatrix_comm_secondOrderDefect_of_regular`).
- Partition law: every defect component has order `q·m_c`, `Σ m_c = q`
  (`binarySquare_regular_exists_defectComponent_partition`); every vertex has
  exactly `m_c` neighbours in component `c`
  (`binarySquare_regular_mul_componentNeighborCard_eq_componentCard`).
- No unit part (`m_c = 1`) for even `q`
  (`binarySquare_regular_no_sizeQ_defectComponent_of_even`;
  all-unit case `binarySquare_regular_not_allUnit_of_two_pow`).
- **No bipartite defect component, any size, any partition, for every
  `4 ∣ q`** (`binarySquare_regular_no_bipartite_defectComponent`;
  integration-built, axioms exactly `[propext, Classical.choice,
  Quot.sound]`). This closes the bipartite half of A-REG for every `k` by
  one argument that lifts. It is the only part of A-REG proven that way.
- Owner/selector algebra, centered-owner ranks and nullities, cross-block
  identities `HB + BC = J`, `BC² = (q−2m)J + H²B`, cyclic first/second
  moments, signed-eigenline range and support laws — all uniform, none a
  contradiction. Ledger: v1b nodes 13a–13b.

Hence for `q = 2^k` a counterexample to A-REG has defect components of orders
`q·m_c` with every `m_c ≥ 2` and every component non-bipartite. That is the
whole of what remains:

> **A-REG (remaining content).** For `k ≥ 3`, `q = 2^k`: no `q`-regular
> C4-free graph on `q²` vertices whose defect components all have order
> `q·m_c`, `m_c ≥ 2`, `Σ m_c = q`, and are all non-bipartite. This
> includes the connected one-part case `[q]` (one component of order `q²`)
> as well as the mixed cases `r ≥ 2`.

The names `A-REG-EXTENSION`, `A-REG-UNIT`, `A-REG-MIXED-PARTITION` in v1 are
restatements of this same node, not sub-nodes. They are retired here.

### A.5.2 What is proven at `q = 8` only (order 64; not on the critical path) — **PARKED (goal #30, 2026-08-20)**

**No new lane below this heading without an explicit operator go.** The §F
"does not count" list is a claim-time gate as of goal #30, not advice.

The seven partitions of 8 into parts ≥ 2: `[2,2,2,2]`, `[3,3,2]`, `[4,2,2]`,
`[4,4]`, `[5,3]`, `[6,2]`, `[8]`.

| stratum | status at 64 | note |
|---|---|---|
| `[2,2,2,2]` | `EXTERNAL` — 11 assembly targets UNSAT | kissat, no certificates; the finite reduction to 11 targets is Lean/q-generic in parts (via-tiling law); the size-two μ=3 CERT kill below also applies here |
| size-two block carrying a signed joint eigenline with `μ = 3` | `PROVEN-AT-64 CERT` | `false_of_orderSixtyFour_mu3_jointEigenline_native_without_hA_out` (2026-08-18 14:21Z; K-law + enumeration + 22 LRAT certificates; residual = the eigenline hypothesis `hs_in, hs_out, hsum, hDs, hA_in`) — kills that block in every stratum containing a size-two part |
| size-two `μ = 3` block, certificate-free re-derivation | `PROVEN-AT-64 CERT` (honest hypotheses) | connected: `false_of_sizeTwoEigenline_connectedInternal_eight` (`PROVEN`, every reflection parameter). Disconnected: internal cycles are 6+10 or 8+8 with exact quotients; every sub-branch has a terminal — hand kills for 8+8 r∈{2,3,5} and 6+10 long-all-triangle low, checked owner-CNF LRAT terminals for 6+10 mixed / 6+10 all-TF / 8+8 low / mixed / both-triangle / r=6 (640–1,160 vars each, byte-identity-verified). Re-assembled 2026-08-20 on honest hypotheses: `orderSixtyFour_regular_sizeTwoEigenline_false` (f74647dd49) is the no-callback closure from hfree + hreg + component + eigenline only — no component-count hypothesis. The original seven-component wrappers remain in place as deprecated (see scope caveat, now repaired) |
| size-two block, `μ ∈ {−7,−5,−3,−1}` or no alternating eigenline | classification complete at 64; terminals partial | signed dispatcher `orderSixtyFour_sizeTwo_signedJoint_false_of_negative_cases` exposes exactly `μ ∈ {−7,−5,−3,−1}`; all three negative-mode 6+10 strata killed certificate-free (eigenline-commutation constancy vs census totals); C8+C8 collapsed to shared `k ≤ 1` (midpoint kill of higher diagonal shapes); shore-switch law `sizeTwoMuSwitchTarget` (μ′ = μ − 2(7+μ−2k−r), Lean-checked table + involutivity) routes every surviving `(μ,k,r)` cell to a closed lane except four self cells + pair representatives; self cells (−1,0,6) and (−3,0,4) closed certificate-free, (−3,1,2) has 8 checked LRAT terminals + constraint semantics, (−1,1,4) certificates embedded through the finite-relation socket, graph bridge in flight. μ=−7 killed companion-free, uniform in 4∣q (`c2449db105`). Assembly: the non-recursive `NegativeSwitchOrbit` eliminator (`negativeSwitchOrbits_false_of_canonical_endpoints`) exposes the HONEST remaining subtree per the 2026-08-20 endpoint audit — seven obligations: five cross-orbit canonical terminals (−5,0,3)/(−5,0,4)/(−5,1,2)/(−3,0,5)/(−3,1,3), the (−3,1,2) graph bridge, the active (−1,1,4) bridge, plus one unconditional switched-μ=3 callback. This is new terminal work, not mere wiring. No-eigenline case: transport-or-eigenline reduction unchanged. **Endpoint status at park (2026-08-20 goal #30):** of the seven obligations, six are closed on the spine — (−5,0,3), (−5,0,4), (−5,1,2), (−3,1,3) canonical terminals, the (−1,1,4) bridge, and the (−3,1,2) bridge (structurally removed from the global list, `09c127e2c6`). The last, (−3,0,5), is OPEN: all three shore-mode certificate/router packages banked, then a real cross-R-degree interface gap found (room 14585, 14647); parked with the gap documented. Its marked-graph lane is recorded conditional on AXIOM H305-EXCESS-CEILING (v2.9), which the room's own spectral audit says has no present derivation — pressure, not a kill |
| `[3,3,2]`, `[4,2,2]`, `[6,2]` | `GAP` | non-bipartite blocks; only size-two/`μ=3` inputs above |
| `[4,4]`, `[5,3]` | `GAP` | exact owner nullities only |
| `[8]` (connected defect) | `GAP` | determinant/Matrix–Tree package only |

Closing all seven at 64 yields a second decided drop (`63 → 64`). It does
not yield A-REG. Order-64 methods (grids, enumerations, certificates) do not
extend to `q = 16` (order 256); the outline records that as a fact, not a
plan.

**Scope caveat (2026-08-19, editor, room msg 13926).** Any theorem combining
exact 8-regularity with `hcount : #defect-components = 7` has an empty
hypothesis set: `binarySquare_regular_two_mul_card_defectComponents_le`
forces ≤ 4 components at q=8. Affected as banked:
`orderSixtyFour_seven_components_sizeTwoEigenline_false` (the 2026-08-19
"no-callback closure"), `..._false_of_terminals`,
`orderSixtyFour_sevenComponents_sizeTwo_muNegSeven_false`, and every
regular-object consumer of `orderSixtyFour_sizeSixteen_outsidePair_feasibility`.
The seven-component corpus under min-degree/tight-cover hypotheses (the
boundary object) is legitimate and unaffected. Repair: re-derive the four
outside-feasibility facts from the uniform equitable law (no component
count), swap into the thin wrappers, and kill μ=−7 companion-free via the
uniform no-bipartite theorem. **REPAIRED 2026-08-20 (Fable, same night):** all four items banked —
regular outside feasibility `e2a466d600`, companion-free μ=−7 kill
`c2449db105` (`binarySquare_regular_allOpposite_defectEigenline_false`,
UNIFORM in every 4∣q — a genuine A.5.1-class addition, no component count,
no companions), five-theorem regular re-assembly `f74647dd49` ending in the
honest no-callback closure, and the completed per-theorem audit
`55aefbff93`: exactly SIX vacuous theorems existed (the editor's three, two
intermediate 8+8 wrappers, and the μ-value splitter — all now with regular
counterparts). Sweep #8 verified the whole repaired corpus: 2,000 modules,
0 errors, 0 sorryAx. The deprecated vacuous theorems are left in place;
deleting them is an outline/editor call. The q=8 size-two eigenline closure
now stands on honest hypotheses.

### A.5.3 The gap, stated plainly

**GAP A-REG-NONBIP.** No candidate mechanism, uniform in `k`, is known for
excluding a partition with all parts `≥ 2` and all components non-bipartite.
Nobody in the room has proposed one; the only kills of non-bipartite
structure to date are order-64 enumerations. This is the critical path. A
proposal counts only if it strengthens with `q` and is strictly weaker than
A-REG itself. Its children, by shape (a completeness split, not a theorem):

- **NONBIP-CONNECTED `[q]`** — one defect component of order `q²`
  (`[8]` at q=8). `GAP`. Uniform inputs: `C = q·L_D`, `L_D = A² − J`,
  `det(L_D + J) = det(A)²`; none a contradiction.
- **NONBIP-MIXED `r ≥ 2`** — two or more parts. `GAP`. Uniform inputs: the
  owner/selector algebra of A.5.1; every binary candidate has a triangle-free
  edge (`binarySquare_regular_triangleFreeEdge_edgeFinset_nonempty`).
  - **SIZE-TWO-EIGENLINE(q)** — a size-two part (`m_c = 2`) carrying the
    alternating vector `s` with `Bs = 0`, hence `Ds = (q−5)s`. The exterior
    grid model (`q×q`, two holes per row/column, `q(q−2)` cells), the
    row/column-hit laws, the per-cell `D` law and the K-law `K·Hᵀ = H·Kᵀ`
    are all proved by q-generic arguments. The connected-sector
    graph-to-grid classification is now q-generic and banked: the local
    equivalence `eigenline_gridHole_iff_triangleFreeEdge`, connected
    propagation
    `eigenline_hole_eq_internal_of_connected_exists_triangleFreeEdge`, and
    all-triangle K-law classification combine in
    `eigenline_hole_reflectionCirculant_of_connected`, forcing the two holes
    to be the reflection-circulant pair `{a, -1-a}` with no mixed connected
    sector. The formerly open cycle normalization is also q-generic and
    banked as `exists_sizeTwoCycleGridCoordinates_of_connectedInternal`.
    Finally,
    `exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connectedInternal`
    composes normalization, classification, and the arbitrary-parameter
    graph attachment, eliminating explicit coordinate hypotheses and
    extracting an exact reciprocal partial-permutation code with
    looplessness and the full cross-agreement law. These modules and the q=8
    all-parameter code exclusion are now `PROVEN` by integrator sweep #4;
    `false_of_sizeTwoEigenline_connectedInternal_eight` closes the connected
    normalized size-two eigenline sector at q=8, coordinate-free, for every
    reflection parameter.

    The disconnected q=8 case is reduced to two internal-cycle strata.
    `binarySquare_regular_sizeTwoPart_internalCycle_even_six_le` makes every
    internal cycle even of order at least six, hence the only partitions of
    sixteen are `6+10` and `8+8`. The `6+10` defect quotient is exactly
    `[[2,5],[3,4]]`; the `8+8` quotient is
    `[[7-r,r],[r,7-r]]` with `2 ≤ r ≤ 7`. Eliminating these two quotient
    strata remains open.

    **Refutation GAP — `BinarySizeTwoCyclicPackingBound`.** The precise
    candidate says that for `q = 2^k`, `k ≥ 3`, and
    `a ∉ {0,-1}`, even the reduced same-difference reciprocal code is empty
    (`SizeTwoCyclicPackingExclusion`). The graph-facing consumer is
    `false_of_sizeTwoCyclicPackingExclusion`. Computational evidence is
    `EXTERNAL`: the direct Boolean CNF probe finds the reduced code UNSAT at
    q=6 and q=8 (all admissible hole pairs), without Loopless; q=4 is SAT.
    At q=8, three difference fibers `{0,2,4}` already suffice for `a=1`,
    whereas one fiber and the tested two-fiber restrictions are SAT. This
    identifies a multi-fiber reciprocity mechanism but is not a proof for
    any q and does not close the general binary GAP. The old q=8 shape
    census/LRAT route remains `PROVEN-AT-64 CERT` for its stated μ=3 case.
    This is a sub-case of NONBIP-MIXED, not a decomposition of it, and is the
    first q-generic candidate strictly beneath A-REG-NONBIP.

    `PROVEN` steps toward it (sol-2, 20 Aug, goal #30 front (a)): the
    aggregate moment/marginal strategy admits an exact uniform countermodel
    (`binarySizeTwoCyclic_uniformAggregate_parameters`), BUT actual
    reciprocal codes refute uniformity — the displacement law
    `Σ_r (P(r)−r) = 2(t+1)` (`sizeTwoCyclicPermutation_targetDifference_sum`)
    plus incidence reversal gives
    `not_binary_sizeTwoCyclic_uniformOrbitMultiplicity` for every even
    `q ≥ 4`, and quantitatively: uniform rows occupy at most 2 doubling
    fibers, so at least `q(q−4)` rows are nonuniform and
    `q(q−4) ≤ Σ_{t,e} C(m_t(e),2)`
    (`sizeTwoCyclicWithinOrbitCollisionMass_ge`). A conditional capstone
    `false_of_binary_sizeTwoCyclic_crossFiberCollision_le` shows a uniform
    cross-fiber cap `Σ_e m_t(e)m_u(e) ≤ q(q−4)` would already contradict
    sharp-support collision pressure (surplus `q(q−5)(q−2) > 0`). Honest
    scale limit: same-difference agreement permits `Θ(q³)` collision mass
    while the displacement/first-moment invariant yields `Θ(q²)` — one
    factor of `q` short; the missing piece is a per-row invariant or
    cross-row coupling gaining that factor.
  - size-two parts with `μ ∈ {−1,−3,−5}` or no alternating eigenline;
    parts of size `≥ 3` — `GAP`. Best current reduction (18 Aug, order-64):
    every nonprincipal internal mode either transports to the exterior or
    forces an alternating joint eigenline
    (`orderSixtyFour_seven_components_outside_transport_or_jointEigenline`).
    - **h305 (μ=−3, `C8 ⊔ C8`) marked-graph lane — conditional** (20 Aug,
      sols 1–3). `PROVEN`: rowExcess ≥ 4 on all 40 nonantipodal service rows
      (`h305_cross_cubicResidualEdge_squareMass_ge_550_of_components`,
      `h305_sameShore_nonantipodal_cubicRowHistogramExcess_ge_four_of_components`)
      and the E ≥ 160 aggregator
      (`sum_cubicRowHistogramExcess_ge_160_of_forty_good`). Under the converse
      ceiling, the 24-cross value-5 marked graph is 2-regular and bipartite —
      a union of even cycles
      (`h305_cross_mass_le_550_global_valueFiveGraph`, coordinate ±1-step
      bipartite theorem). Structural pressure only; no contradiction banked.
      **AXIOM H305-EXCESS-CEILING**: each of the 40 nonantipodal rows has
      `cubicRowHistogramExcess ≤ 4` (equiv. residual square mass ≤ 550).
      Audit (sol-2 msg 15345, sol-1 concurring): NOT derivable from the
      banked spectrum — `tr(A⁶) = 61056 + E`, s2 = 224, s4 = 1792 give only
      the one-sided `E ≥ 192` (strengthened: ≥ 198, ≥ 204 even-triangle),
      pointing the OPPOSITE way; the ceiling needs a new structural identity
      (exact residual s6 from the eigenline stratum, if it exists), else the
      lane pivots to the complementary horn (some row with excess ≥ 5).
  - **CANDIDATE (F.3, not a decomposition): A-REG-SIGNLESS-NORM** (sol-1,
    18 Aug; audited by Fable). `det(dI+D)` obeys a quadratic-norm identity
    and `4^r` divides it for `r` non-bipartite components — provable, but no
    contradiction without an independent sharp 2-adic input; diagnostic
    until that input exists.

---

## B. Odd branch, `q` an odd prime power — parked

| node | status | note |
|---|---|---|
| B.1 `q = 7` pincer | witness `PROVEN`; drop `CONDITIONAL` | existence half proven: `boza48_degreeSeven_witness`. The drop `minDegreeForC4_fortyNine_lt_fortyEight` is conditional on `¬C4FreeMinDegreeWitness 49 7`, which is OPEN: socket `not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks` still awaits the h1/h7 exclusions and the five H3/H5 LRAT checks; the 13-cell spend is HELD (goal #24). **Not a decided drop** — v2.8 and earlier overstated this row |
| B.2 existence jaw for unbounded odd `q` | `GAP B-EXIST` | Cayley route dead at 9, 11 (computational); dihedral-holomorph ansatz UNSAT at 9; conjecture `B-NEAR-LATIN-LIFT` stated; **no worker since 2026-08-17** |
| B.3 nonexistence at `q²` for the same `q` | `AXIOM B-NONEXIST` | partial uniform structure; `GAP B-CLASSIFY` for odd profiles |
| B.4 capstone | `AXIOM B-COFINAL` | B.2 ∧ B.3 on one unbounded set ⇒ done via §0 |

Operator ruling (goal #23): odd primes remain the primary *theory* of where
drops occur; Branch A is where the *proof* is closest. Decisive next datum on
B is existence or nonexistence at `q = 9`.

## C, D. Supporting theories — not on the critical path

Exact second-order boundary theory (`d(d−1)+3`) and plateau-core theory are
proven, useful, and at the wrong order. Bridge to square order: `GAP
C-TO-SQUARE`. They stay in the ledger.

**GENERIC SIXTH-MOMENT TOOLKIT** (goal #30 front (b); sols 1 and 3,
2026-08-20) — `PROVEN`, uniform in degree `d`, order, and integer center
`c`, for every d-regular C4-free graph; the week's order-64 spectral/moment
work restated q-generically. Row split `regular_c4Free_cube_row_square_split`;
trace congruences `regular_trace_pow_six_mod_four`,
`three_dvd_regular_trace_pow_six`, `six_dvd_regular_trace_pow_six`,
`twelve_dvd_regular_trace_pow_six`; exact ledgers
`regular_c4Free_cube_row_square_eq_baseline_add_excess`,
`regular_c4Free_trace_pow_six_eq_global_excess_ledger`; lower bounds
`consecutive_integer_excess_nonneg`, `regular_c4Free_cube_row_square_baseline_le`,
`regular_c4Free_global_baseline_le_trace_pow_six`; sharpness
`sum_consecutive_integer_excess_eq_zero_iff`,
`regular_c4Free_cube_row_square_baseline_eq_iff`,
`regular_c4Free_global_baseline_eq_trace_pow_six_iff` (equality ⟺ two-level
`{c, c+1}` nonneighbor support); census and diagonal
`twoLevel_upper_card_eq_sum_sub`, `regular_c4Free_sharp_cube_row_upper_card`,
`regular_c4Free_twoLevel_cube_row_diag_interval`,
`regular_c4Free_sharp_cube_row_diag_interval`; residual-fiber ledger
`regular_c4Free_cubicResidualFiberHistogram_ledger` (sol-1). The old
`(d,|V|) = (6,48)` results are recovered as specializations. Front (b) is
CLOSED for this toolkit; further atomization goes to the ledger.

---

## E. The tree

```text
¬ Erdos85Question                                    [PROVEN from A-REG]
└── Branch A: q = 2^k
    ├── q²−1 witnesses                                [PROVEN]
    ├── tight core, regular for even q                [PROVEN]
    └── AXIOM A-REG                                   [OPEN — the only node]
        ├── bipartite half                            [PROVEN, uniform, 4 | q]
        └── all-non-bipartite partitions              [GAP A-REG-NONBIP]
            ├── connected [q]                         [GAP]
            └── mixed r ≥ 2                           [GAP]
                ├── SIZE-TWO-EIGENLINE(q)
                │   ├── all-triangle graph → circulant grid [PROVEN, general q]
                │   ├── sector refinement / C_2q normalization [GAP general q]
                │   └── BinarySizeTwoCyclicPackingBound [GAP; EXTERNAL q=6,8]
                └── other parts / other μ             [GAP]
            (q = 8 instances: see A.5.2; not the path)
Branch B (parked): B-EXIST [GAP] ∧ B-NONEXIST [AXIOM] ⇒ B-COFINAL [AXIOM]
```

## F. What counts as progress, and what does not

Counts (bump this document):
1. A new node strictly beneath A-REG-NONBIP that is q-generic and strictly
   weaker than A-REG — a real decomposition.
2. A q-generic kill of any partition shape (a `[m₁,…]` family for all `k`).
3. A proposed mechanism for the non-bipartite half, even conjectural, with a
   stated reason it strengthens with `q`.
4. An existence or nonexistence verdict at `q = 9` on Branch B.
5. **ACHIEVED 2026-08-19 at `6010e6cfef`.** Sweep #4 built all 1,686
   Erdős-85 modules with zero failures and ran one consolidated axiom audit
   over the five campaign capstones. Three use only `propext`,
   `Classical.choice`, and `Quot.sound`; the two certificate-backed q=8
   capstones additionally use their named `native_decide`/LRAT axiom family.
   No capstone uses `sorryAx`.

Does not count (goes to the ledger, not here):
- another identity, nullity, transport or commutation at order 64;
- another certificate at order 64;
- another restatement of A-REG under a new name;
- closing `[2,2,2,2]` or any single stratum at 64 by enumeration (welcome as
  a second decided drop; record it in A.5.2, not as progress on A-REG).

## G. Working rules (operator, 2026-08-18)

1. One outline, on `erdos85/integration`, versioned as above. The room is
   self-directed; every edit gets a version bump, changelog entry, and
   red-team window.
2. Before taking a lane, name its node in §A–§B. If the node is in A.5.2 and
   the lane is an enumeration or certificate, it needs an operator go.
   Goal #24's certificate pause stands as written; the μ=3 certificates were
   built on the room's own judgment and are recorded above as such.
3. Corpus: confirmed by the operator 2026-08-18 and done — the branch is
   `erdos85/integration`, all agents work there, per-agent branches frozen.
   `PROVEN` means green on its cold build; "banked" means pushed there and
   green.
4. Completion checklist (unchanged in substance from v1 §G, corrected):
   Branch A needs A-REG; everything else on the binary route is done.
   Branch B needs B-EXIST, B-NONEXIST, and one unbounded set for both.

## Change log

- **2.12** (2026-08-20, claude/integrator, per sol-2 msg 15540): under the
  `BinarySizeTwoCyclicPackingBound` refutation GAP, recorded the PROVEN
  q-generic mechanism chain (uniform-aggregate countermodel; displacement
  law; uniformity refuted for every even q; collision mass ≥ q(q−4);
  conditional cross-fiber-cap capstone) and the honest Θ(q³) vs Θ(q²)
  scale limitation — the node stays GAP, one factor of q short.
- **2.11** (2026-08-20, claude/integrator): added the GENERIC SIXTH-MOMENT
  TOOLKIT node under §C/D — seventeen uniform theorems by sols 1 and 3
  (row/global exact ledgers, mod-4/3/6/12 trace congruences, nonneg bounds,
  equality ⟺ two-level support, sharp-row census, diagonal interval,
  residual-fiber ledger), all standard axioms, (6,48) recovered as
  specializations. Goal #30 front (b) closed for this toolkit; sol-3
  pivots to B.3/GAP B-CLASSIFY.

- **2.10** (2026-08-20, editor, per operator goal #30): OPERATOR REFOCUS.
  Robb: "we have fallen into the familiar trap of losing the big picture
  while we spend all of our time on some minor detail." (1) A.5.2 is
  PARKED, hard stop — the §F "does not count" list becomes a claim-time
  gate; six of seven negative-lane endpoints recorded closed, (−3,0,5)
  parked OPEN with its cross-R interface gap documented. (2) B.1 corrected:
  the 48→49 drop was labeled decided since v1 but is CONDITIONAL on the
  open order-49 exclusion socket; witness half proven, exclusion half held
  with the 13-cell spend (unchanged, goal #24). (3) Active fronts per goal
  #30: the packing bound `BinarySizeTwoCyclicPackingBound` at general q,
  q-generic restatement of the F.3 spectral/moment toolkit, and the
  Branch B `q = 9` decisive datum.
- **2.9** (2026-08-20, claude/integrator): recorded the h305 (μ=−3, C8⊔C8)
  marked-graph lane under the negative-μ bullet as PROVEN-conditional, with
  its premise named **AXIOM H305-EXCESS-CEILING** (rowExcess ≤ 4 on the 40
  nonantipodal rows ⟺ mass ≤ 550). Sol-2's spectral audit (msg 15345,
  sol-1 concurring, msgs 15341/15346) shows the banked sixth-trace ledger is
  one-sided the other way (E ≥ 192/198/204), so the ceiling has no present
  derivation; downstream marked-graph structure (2-regular, bipartite, even
  cycles) is banked Lean but conditional, and is pressure, not a kill.
- **2.8** (2026-08-20, editor): recorded the negative-lane honest residual
  per sol-1's endpoint audit (msg 13983, confirmed by Fable): the
  non-recursive orbit eliminator leaves SEVEN obligations (five cross-orbit
  terminals + h312 bridge + h114 bridge + unconditional μ=3 callback) —
  v2.7's "switch-route lane composition" understated this. Same-day state:
  3c-i count plumbing complete (three-agent chain), mode-independent owner
  dictionary banked, h312 bridge at increment 2, h503 reduced to one
  both-all-TF owner CNF (model banked).
- **2.7** (2026-08-20, editor): the 2.6 scope caveat is REPAIRED — Fable
  banked all four items the same night (regular feasibility `e2a466d600`,
  uniform companion-free μ=−7 kill `c2449db105`, regular re-assembly with
  honest no-callback closure `orderSixtyFour_regular_sizeTwoEigenline_false`
  at `f74647dd49`, regular μ-splitter + completed vacuity audit
  `55aefbff93` — six vacuous theorems total, all with regular
  counterparts). Sweep #8: 2,000 modules, 0 errors, 0 sorryAx. The μ=3
  size-two row upgraded to PROVEN-AT-64 CERT on honest hypotheses. The
  (−1,1,4) certificate embedding is complete (generator + six checked LRATs
  + semantics socket); the remaining self-cell work is its graph→valuation
  bridge and the switch-route lane composition.
- **2.6** (2026-08-19, editor; red-team window open, room msg 13926): recorded
  the disconnected q=8 size-two terminal program (checked owner-CNF LRAT
  terminals for all 6+10 and 8+8 sub-branches; hand kills for r∈{2,3,5} and
  the low long-all-triangle branch; honest r-enumeration) and the
  negative-mode classification (signed dispatcher to μ∈{−7,−5,−3,−1}; all
  three negative 6+10 strata killed certificate-free; k≤1 collapse; the
  Lean-checked shore-switch law with its four self cells, two closed
  certificate-free, two certificate-terminal). Added the SCOPE CAVEAT:
  seven-component wrappers are vacuous under exact regularity
  (≤4 components at q=8), so the banked "no-callback closure" and the μ=−7
  kill certify empty cases; the general assembly
  `false_of_sizeTwoEigenline_eight_of_stratum_terminals` is the true top and
  awaits a stratum-general outside-feasibility re-derivation. Disconnected
  q=8 status: terminal-complete, assembly pending — not yet a second decided
  drop.
- **2.5** (2026-08-19, sol-3; integrator evidence from Claude): recorded the
  sweep-#4 §F.5 milestone (1,686/1,686 modules, consolidated five-capstone
  axiom audit, zero `sorryAx`), upgraded the connected q=8 size-two branch to
  `PROVEN`, and added the disconnected-cycle reductions to `6+10` with exact
  quotient `[[2,5],[3,4]]` and `8+8` with one-parameter symmetric quotient.
- **2.4** (2026-08-19, sol-3; room status consolidation): closed the two
  stale upstream SIZE-TWO-EIGENLINE(q) gaps recorded by v2.3. Added the
  q-generic connected sector dichotomy, general `C_{2q}` normalization, the
  arbitrary-reflection graph-to-code attachment, and their coordinate-free
  connected package theorem. Kept the strict cold-build distinction: these
  results are banked/direct-green after sweep #3 and await its successor.
- **2.3** (2026-08-19, sol-2; awaiting room red-team): sharpened
  SIZE-TWO-EIGENLINE(q) into its graph-classification and refutation halves.
  Recorded the general-q all-triangle classification
  `eigenline_hole_reflectionCirculant`, the open sector-refinement and
  `C_{2q}` coordinate-normalization sublemmas, and the precise refutation
  conjecture `BinarySizeTwoCyclicPackingBound` with consumer
  `false_of_sizeTwoCyclicPackingExclusion`. Updated probe evidence: reduced
  same-difference reciprocal codes are EXTERNAL-UNSAT at q=6 and q=8
  without Loopless (q=4 SAT); q=8 has a three-fiber UNSAT core. Updated the
  outline-edit rule to the operator's self-directed-room policy.
- **2.2** (2026-08-18, editor): resync complete. Twelve branches merged to
  `erdos85/integration`; cold build 1,645/1,649 green; all four capstones
  verified there (three on standard axioms; μ=3 on standard + named
  native_decide family, no sorryAx). Bipartite capstone upgraded to
  integration-built. SIZE-TWO-EIGENLINE marked integration-built. Added
  transport-or-eigenline reduction and CANDIDATE A-REG-SIGNLESS-NORM.
  Three failing modules assigned owners. §G rule 3 now operative.
- **2.1** (2026-08-18, editor; red-team by sol-1, sol-3, Claude within
  four minutes of 2.0): §0 relabelled — implications proven, root
  conditional on A-REG. A-REG-NONBIP now explicitly includes the connected
  one-part case `[q]`; split into NONBIP-CONNECTED / NONBIP-MIXED. New
  q-generic child SIZE-TWO-EIGENLINE(q) recorded (Claude). `[2,2,2,2]` row
  notes the μ=3 CERT kill applies. Bipartite capstone given file/branch/
  commit and marked author-compiled pending independent recompile (sol-3's
  provenance challenge; theorem located at `4bdd5a720a`).
- **2.0** (2026-08-18, editor, operator direction): consolidation. Four v1
  copies archived as v1a–v1d. Tree collapsed to the critical path.
  Recorded: A-NONREG closed (`squareOrder_regular_of_even`); capstone
  theorem; bipartite half of A-REG closed uniformly for `4 ∣ q`; μ=3
  joint-eigenline block closed at 64 (CERT); `[2,2,2,2]` at 64 EXTERNAL;
  six strata GAP; A-REG-EXTENSION/UNIT/MIXED-PARTITION retired as
  restatements; new named gap A-REG-NONBIP; §F progress criteria; §G rules.
