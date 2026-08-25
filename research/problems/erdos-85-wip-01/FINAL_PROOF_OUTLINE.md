# Final proof outline: Erdős 85 is false

**Version 2.52 — 2026-08-25 ~06:30Z (v2.51 + the Goal #7 compensated-surgery boundary recorded).**

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
  candidate statement) · **`PROVEN-SKETCH`** (argued in prose and red-teamed
  in the room, **NOT machine-checked**; must name its report file and its
  reviewers). The last label was added 2026-08-22 at sol-1's request and its
  boundary is deliberately hard: **a `PROVEN-SKETCH` does not satisfy §G
  rule 4's completion checklist and never counts toward closing a node.**
  It exists so that paper results are recorded honestly instead of being
  pushed into `PROVEN` (which they are not) or `AXIOM` (which understates
  them). If a `PROVEN-SKETCH` is load-bearing for anything, formalising it
  is the next task, not a later one.
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

**Reproducibility caveat (integrator sweep #18, 2026-08-20):** 37 modules
load LRAT payloads via `include_str` with absolute host paths under
`/Volumes/Stripe/lean-genius/artifacts/` (the four MuThree native/LRAT
certificate modules and 33 `Erdos85H1V2CertP2I*` files). They fail in a
containerized cold build; prior sweeps ran on the host where the paths
resolve. Until the payloads are tracked in-repo or fetched to a
repo-relative path, every `CERT` label backed by them means "green on a
host build with the artifacts volume present", not "green from the branch
alone". Repair is parked with A.5.2; needs an operator call on payload
storage.

The seven partitions of 8 into parts ≥ 2: `[2,2,2,2]`, `[3,3,2]`, `[4,2,2]`,
`[4,4]`, `[5,3]`, `[6,2]`, `[8]`.

| stratum | status at 64 | note |
|---|---|---|
| `[2,2,2,2]` | `EXTERNAL` — 11 assembly targets UNSAT | kissat, no certificates; the finite reduction to 11 targets is Lean/q-generic in parts (via-tiling law); the size-two μ=3 CERT kill below also applies here |
| size-two block carrying a signed joint eigenline with `μ = 3` | `PROVEN-AT-64 CERT` | `false_of_orderSixtyFour_mu3_jointEigenline_native_without_hA_out` (2026-08-18 14:21Z; K-law + enumeration + 22 LRAT certificates; residual = the eigenline hypothesis `hs_in, hs_out, hsum, hDs, hA_in`) — kills that block in every stratum containing a size-two part |
| size-two `μ = 3` block, certificate-free re-derivation | `PROVEN-AT-64 CERT` (honest hypotheses) | connected: `false_of_sizeTwoEigenline_connectedInternal_eight` (`PROVEN`, every reflection parameter). Disconnected: internal cycles are 6+10 or 8+8 with exact quotients; every sub-branch has a terminal — hand kills for 8+8 r∈{2,3,5} and 6+10 long-all-triangle low, checked owner-CNF LRAT terminals for 6+10 mixed / 6+10 all-TF / 8+8 low / mixed / both-triangle / r=6 (640–1,160 vars each, byte-identity-verified). Re-assembled 2026-08-20 on honest hypotheses: `orderSixtyFour_regular_sizeTwoEigenline_false` (f74647dd49) is the no-callback closure from hfree + hreg + component + eigenline only — no component-count hypothesis. The six deprecated seven-component wrappers are DELETED (eeaa44c4fe, per goal #30 item 3); the regular counterparts are the only assembly |
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
  (`[8]` at q=8). `GAP`, first owned 2026-08-22 (sol-1), and the node moved
  twice in its first hour.

  **(i) The determinant / D-spectrum route is ELIMINATED, uniformly**
  (`0ed91c72d6`). The listed uniform inputs `C = q·L_D`, `L_D = A² − J`,
  `det(L_D + J) = det(A)²` are not merely non-contradictory, they are
  satisfiable: connected non-bipartite `(q−1)`-regular circulants `D_q` with
  `charpoly(L+J) = (x−q²)(x−4)P²` and a square tree count clear every one of
  them. Scope stated by the owner and kept here: these are controls against
  the invariants, **not ambient countermodels** — no graph `G` is claimed.
  This is the quantified negative goal #34 asked for, and it retires a route
  the map had carried as live since the node was named.

  **(ii) A candidate mechanism, the first beneath A-REG-NONBIP since the
  sign/holonomy family died the same night** (Fable, on goal #13's orbit
  lemma). The integral-square-root trace condition is strictly finer than
  `det` and `τ`: for each `D`-eigenvalue `μ` with eigenspace dimension `k`,
  `A` acts with eigenvalues `±√(q−1−μ)`; when `√(q−1−μ) ∉ ℚ(μ)` the two
  conjugates carry equal multiplicity, forcing `k` EVEN and zero contribution
  to `tr(A)` and `tr(A³)`. Every surviving class must then satisfy
  `q + Σ m_θ·θ = tr(A) = 0`. It kills sol-1's own controls: at q=8 all 31
  irrational classes pair with `k = 2`, the sole unpaired class `μ = 3` gives
  `θ = ±2`, `k = 1`, hence `tr(A) = 8 ± 2 ≠ 0`; at q=4 an exhaustive sweep of
  all 4,374 sign splits yields no integer charpoly with zero trace. Confirmed
  independently by exact residual factor norms — `[2,2,194]` at q=4 and
  `[6,62,958,409534,93049333140734]` at q=8, all nonsquares (`05a9fd229a`).
  Why this one is worth taking seriously: it needs no ambient `G` beyond
  `A ∈ Sym_n(ℤ) ∩ {0,1}`, `A² = (q−1)I + J − D`, `tr A = 0`, so it is
  Lean-statable as a proper child of this node; and the hard half is ALREADY
  BANKED — `Erdos85AbstractTraceEscape.abstract_residual_trace_eq_zero` is
  operator-abstract over finite-dimensional ℚ-spaces and carries the
  Galois/norm argument, so what remains is a graph-facing wrapper restricting
  `A, D` to a J-killed residual sector. Do not re-extract it.

  **(iii) The graph-facing interface is now PROVEN** (`55b7a058cd`,
  `Erdos85BinarySquareConnectedTraceEscape`). `binarySquare_regular_shiftedDefect_residual_trace_eq_zero`
  takes the shifted `T = D − J`, proves `A² = (q−1)I − T` with `A` and `T`
  commuting, and applies `abstract_residual_trace_eq_zero`. Cold-verified,
  standard axioms only. The owner's own framing is kept: **this is an
  interface, not a connected exclusion.**

  **The gap, narrowed on the owner's correction (v2.25 stated it too
  widely).** Do NOT label the existence of designated factors a gap — it is
  `PROVEN`: `exists_nonprincipal_defectEigenvalue_with_square`
  (`Erdos85GlobalOrbitSquare`) gives a genuine nonprincipal
  square-in-`ℚ(μ)` defect orbit, and every certified residual factor has zero
  trace (`55b7a058cd`). **The exact remaining GAP is to classify or bound ALL
  designated factors strongly enough that their signed trace contributions
  cannot total `−q`** — optionally meeting the cubic trace at the same time.

  **First quantitative child that strengthens with q** (sol-1, 07:24Z, NOT
  yet banked — spectral-bound APIs under audit, and it is recorded here as a
  proposal). A connected non-bipartite `(q−1)`-regular `D` has every
  nonprincipal `μ > −(q−1)`, so every associated adjacency root satisfies
  `|θ| < √(2q−2)`. Since certified residual sectors cancel and the total
  nonprincipal trace is `−q`, the TOTAL DIMENSION of designated
  square-in-`ℚ(μ)` sectors must exceed `q/√(2q−2) ≈ √(q/2)`. That upgrades
  `GlobalOrbitSquare` from bare existence to a **growing multiplicity
  requirement**, which is the first thing beneath this node to meet §A.5.3's
  standing bar that a proposal counts only if it strengthens with `q`.

  **Scope discipline, and the owner said it before anyone asked:** the
  trace-condition verification remains finite, q = 4 and q = 8. The node
  stays `GAP` and this outline does not upgrade it.

  **(iv) The quantitative child of v2.26 is now `PROVEN` — and proved
  INSUFFICIENT in the same half hour** (`593c27aa4b`, refined to
  `87b722316f`). `connectedNonbipartite_designatedFactor_finrank_sq_growth`
  concludes `q² < 2(q−1)·(finrank_ℚ ker g(T))²` directly, with the proof
  internally identifying mapped root-list length = root multiset card =
  mapped charpoly degree = rational restriction charpoly degree = sector
  finrank, so the bound is on the INTRINSIC designated dimension and not on
  an encoding artifact. Cold-verified, standard axioms.

  It cannot close on its own, and the owner audited that within two minutes
  of banking it: ambient dimension gives only `m ≤ q²`, which is entirely
  compatible with `m > √(q/2)`, and the already-eliminated determinant/tree
  package supplies no upper bound. **What is now required is an UPPER bound
  on the intrinsic designated primary dimension.** No banked theorem
  constrains the number or degree of square-in-`ℚ(μ)` factors for a
  connected `(q−1)`-regular `D`.

  **(v) Three routes closed the same half hour, all before any Lean file was
  opened.** Recorded because each would otherwise be re-proposed.
  1. *The growth bound alone* — insufficient, as above.
  2. *Local vertexwise cancellation / the two-budget currency* — REFUTED by
     abstract satisfiability before formalization. The budgets are
     continuously satisfiable at designated rank `Θ(√q)`, so they are a
     lower-bound interface and carry no upper bound. The one genuinely
     discrete fact underneath was extracted and is worth keeping: since
     `A² = (q−1)I + J − D`, for `y ~ x` one has `(A²)_xy = 1 − D_xy`, hence
     `Σ_nonprincipal (q−1−μ)·a_μ(x) = −|N_A(x) ∩ N_D(x)|` — minus the
     `triangleFreeEdgeGraph` degree at `x`. No pigeonhole follows: `a_μ(x) ∈
     ℚ(μ)` has unbounded denominators coming from the D-charpoly
     discriminant. Lane deliberately not opened.
  3. *Smith normal form* — CLOSED at the abstract level. `B = L_D + J = A²`
     is nonsingular over ℚ, so `coker(B)` sits in
     `0 → coker(A) → coker(A²) → coker(A) → 0`, but that self-extension need
     not split: `A = [2]` already gives `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0`.

  **(vi) Current candidate, audited and explicitly NOT a terminal.** The
  incidence bottleneck `E := AD − (J − A) = qA − A³ + (q−1)J`. Row `x`
  records occupancy-minus-one of the `q−1` defect-neighbour blocks on the
  `q²−q` points outside `B_x`; it vanishes identically on `B_x` and has row
  sum zero. A wholly vanishing row would make `N_D[x]` a `K_q` component
  (the `q−1` neighbour blocks pairwise disjoint), impossible for connected
  `D` on `q² > q` — so every row is a nonzero integral zero-sum vector and
  `‖E‖_F² ≥ 2q²`. Spectrally `E` has multiplier `θ(μ+1) = θ(q−θ²)`; **the
  exact blind spot is `μ = −1`**, and when `q` is a square the designated
  trace can concentrate in that kernel, so this does not yet upper-bound the
  designated dimension. The sharper question it isolates: bound the `−1`
  multiplicity or trace imbalance of connected `(q−1)`-regular deficiency
  graphs, or separate designated `E`-mass from residual `E`-mass. The owner
  is holding off on a Lean file until one of those has a closing
  inequality.

  **(vii) THE SURVIVOR IS NOW ONE QUESTION, and every spectral route to it is
  closed** (divergence round #1, sol-1 and Fable independently, 08:34–08:37Z).

  *The reduction, and it is clean.* At `q = s²` the canonical survivor was
  posed as the joint kernel `W₋ = ker(D + I) ∩ ker(A + sI)`. The stacked
  system is REDUNDANT: `Av = −s·v` forces `v ⊥ 𝟙` (since `−s ≠ q`), and then
  `Dv = ((q−1)I + J − A²)v = −v` follows automatically. So
  **`W₋ = ker(A + sI)`**, `W₊ ⊕ W₋ = ker(D + I) ∩ 𝟙^⊥`, and the survivor
  exists **iff `mult_D(−1) ≥ √q`**. One multiplicity question, no joint
  system.

  *And it cannot be answered spectrally.* Both independent submissions
  produced objects whose multiplicity is enormous under every spectral
  hypothesis on the table: sol-1's connected clique-blowup `D = H[K_s]`,
  which has a real (non-0/1) square root, reaches `mult_D(−1) = s³(s−1)`;
  Fable's moment-feasibility model permits `dim W₋ ≈ q²/2`. The `ER_q`
  comparison seals it — order `q²+q+1` carries `±√q` multiplicities
  `q(q+1)/2`, so nothing spectral distinguishes order `q²` at all.
  **CLOSED: the signed/PSD route, the joint-system route, and
  minimum-rank / zero-forcing.**

  *The consequence is a direction, and it is the most useful sentence on this
  node:* **any terminal must use the fact that `A` is entrywise 0/1 —
  incidence, nonlinearly.** Proving `mult_D(−1) < √q` from binary
  realizability would be a design-level theorem, not a spectral sublemma.

  *Corroborating control (sol-1, 08:32Z).* For `q = s²` take
  `g(X) = (X+s)^s`: monic, integral, degree `s`, root trace `−s² = −q`, every
  root with `θ² = q` (`μ = −1`). It satisfies the real-root, spectral-radius,
  Cauchy and mod-2-square interfaces simultaneously. It need not be
  graph-realizable — that is the point. **No theorem about the designated
  polynomial's coefficients alone can kill the canonical survivor**, so
  further Newton/congruence wrappers are not the missing currency and should
  not be built.

  **(viii) THE THEOREM THE NODE NEEDS NOW HAS A NAME AND A LITERATURE
  ANCHOR** (Fable, 09:30Z, offered explicitly as a framing rather than a lane
  claim; numerically checked at q = 3, 5, 7).

  *The classical control.* Take the `(q²_q)` configuration `AG(2,q)` minus
  one parallel class, with the polarity `(a,b) ↔ {y = ax − b}`. Incidence
  `d = ac − b` is symmetric in the two points, so `A` is symmetric,
  `q`-regular and C4-free on `q²` vertices — it satisfies EVERYTHING in
  A-REG except two things, and it fails both in the most instructive way:
  1. `tr A = q`, not 0 — exactly `q` absolute points, the `(a,b)` with
     `2b = a²` (for even `q`, the column `a = 0`);
  2. `D = q·K_q`, the dropped parallel class — DISCONNECTED, with
     `mult_D(−1) = q² − q`.

  So the classical object sits exactly at the union-of-cliques extreme that
  (vii)'s clique-blowup identified, and differs from a counterexample only by
  having trace `+q` instead of 0. That is a very sharp place for the known
  model to sit.

  *The theorem to port.* `tr A = 0` is precisely the statement that the
  polarity is FIXED-POINT-FREE — no absolute points. So what A-REG needs
  beneath this node is a **Baer-type absolute-point theorem for self-polar
  `(q²_q)` configurations**: *a polarity of a `(q²_q)` configuration whose
  non-collinearity graph is connected has at least one absolute point.*
  Baer's own theorem for projective planes gives `≥ n+1` absolute points, and
  — this is why it fits (vii)'s direction — **its proof is combinatorial, not
  spectral.** That is the technique to port, and it is the first candidate
  beneath A-REG-NONBIP that is anchored in existing mathematics rather than
  invented here.

  Status: `GAP` still. Nothing is proven, no Lean file is open, the
  connected-vs-disconnected hypothesis is exactly the hard part, and Baer's
  argument is for planes rather than for configurations with a parallel class
  removed. But the node has moved from *"a terminal must use binary incidence
  nonlinearly"* to *"port Baer"*, which is a materially better place to
  restart from.

  **`PROVEN-SKETCH` (43)–(68)** — `A_REG_BAER_INVOLUTION_COUPLING_AUDIT.md`,
  tips through `22198a5430` (sol-1, 22:23Z). Any nontrivial kernel shore has
  a least dyadic digit `j ≤ k−1`; the final `j` forces a nonconstant layer
  whose complement `C` is even with `2 ≤ c ≤ 2q−2`, subcubic in `A`,
  four-typed, with full–empty `D`-complete and exact energy and design
  moments. **Remaining `AXIOM`/`GAP`: eliminate the resulting pure or
  smaller-mixed bounded exceptional design uniformly in `q`.** Prose and
  Python only; nothing here is in Lean.

  **PURE `c=q` ENDPOINT — the exceptional design above, at its extreme, now
  has a Lean spine** (2026-08-25 00:35–02:00Z; sols 1–3 building, Fable
  cold-verifying every bank; 25 commits `3950298a6e..bd5188264f`, all
  `PROVEN` on cold recompiles with standard axioms). Vocabulary, fixed by
  sol-3's census (29231): the `c` full lines are a maximal intersecting
  block clique `F`; at the endpoint `c = q` they realise `K_q` linearly with
  one **private point** `p_f` per full line, `C(q,2)` pair points `x_fg`,
  and `|U| = q(q−1)/2` uncovered points; every other line is exactly
  half-occupied (`q` full, `q²−q` half, `0` empty). For a half line `b`,
  `r_b = deg_D(b, F)` counts its private points, `h_b = r_b − 1`, and the
  **private cut** `s = Σ_b (r_b − 1)²`. Status, each item a named theorem:
  1. `n₃ = 0` and exact `n₁/n₂` populations of the pure Baer layers
     (`ba59fda0e7`, `e534734f99`, sol-1): after `r` is chosen the pure
     branch has no remaining arithmetic population parameter.
  2. **The all-`r=1` child is CLOSED** —
     `c4Free_binarySquare_pureEndpoint_not_uniform_private_halfOccupancy`
     (`b78e4a659c`, sol-3). The kill is two lines (29324, verified
     independently by Fable 29329): if no half line carries two private
     points, two private points share no line, so they have no common
     `A`-neighbour and are `D`-adjacent; `D[P] = K_q` with `D`
     `(q−1)`-regular makes `P` an isolated component. General form
     `e_D(P) = C(q,2) − s/2`, so **connectedness forces `s > 0`**. This
     retires the decorated/near-one-factorisation reformulations (29266,
     29275: cross-orthogonal punctured near-factors, outside Howell/MOOF
     bounds) and sol-2's routing-defect control (29327: a connected `q=4`
     switch with `τ = 288²` shows tree arithmetic alone never forces `E=0`)
     — the private-collision route was the right one and the `U`-shore was
     never the obstruction.
  3. `n₀ ≥ q/2` uniformly in `s` (`48be5a4d51`), the minimum-cut row profile
     (`f48b3e7ed7`, `e9e21003ba`, `df5ad28e04`: `s = q` ⇒ exactly `q/2` zero
     rows and `q/2` double rows), the equality-rigidity grid for linear
     uniform trades (`aeea267651`, `547c3c98bd`, `0a7467b9a8`), and the
     pair-point trade identity `Σ_{b∋x} r_b + d_D(x,P) = q−2`
     (`ab5defea93`, `c50b560c35`).
  4. `s = q` is IMPOSSIBLE (`f9b24f6a58`), and then **`s ≥ 2q−4` at every
     preconnected pure endpoint, `q ≥ 8`**
     (`c4Free_binarySquare_pureEndpoint_privateCut_gap_and_boundary_zero_card`,
     graph wrapper `815ee9055b` sol-2, projection `bd5188264f` sol-3; the
     `s = q` terminal `f9b24f6a58` is sol-2's, the arithmetic classifier
     `6824631dba`/`084d410b28` and collision API `2ae47599cb`/`728e82ffdf`
     sol-3's, the moments API `54a2b854e1` sol-1's, and the interval
     observation `m ≤ Z ≤ s/2 ⇒ s ≥ min(m², 2q−4)` Fable's — attribution
     corrected in v2.50 per 29644): the whole band
     `q ≤ s < 2q−4` is closed uniformly. At the boundary `s = 2q−4`,
     `|Z| = q−2` is forced (`084d410b28`) with every positive `h = 1`
     (`n₀ = n₂ = q−2`) and both collision bounds tight.

  **Live residue: `2q−4 ≤ s ≤ q(q−1)`**, the upper bound from linearity
  alone. The two bounds are of different orders in `q`, and the room spent
  01:40–02:00Z establishing that *no more of the same trade* can meet in the
  middle: owner-Gram Schur trace (sol-3 29591, sols 1–2 29601/29603 — the
  trace is affine in `s` with the WRONG sign, and the entire range of `s`
  moves it by `< 1`), fourth-moment centre compression (29609 — reproduces
  the energy identity, best bound cubic), principal owner-graph (29596),
  private-row local switching (29611 — no local shore freedom at fixed `F`),
  even-configuration code transfer (29613 — Tanner girth ≥ 6 forces
  nothing at `Θ(q²)`), and even-blind multiplicity parity (29618) are all
  CUT. **The sharp statement of why** is sol-3's abstract feasibility model
  (29622): for any `q−2 ≤ z ≤ N/2` the profile `(z × r=0, z × r=2, rest
  r=1)` satisfies every scalar occupancy identity AND realises the full
  combined-shore collision hypotheses, with `s = 2z` ranging from the banked
  boundary to `Θ(q²)`. So every banked inequality is sharp on models with
  large cut, and the next ingredient must use **self-indexing / reciprocity
  among the points themselves** (a bound on unused-owner correlations
  `|K_b ∩ K_c|`, or the polarity) — not block linearity or shore balance.
  That is the same sentence the node ended on before the restart, now with
  a witness family showing where the generic tools stop.

  **The perfect-matching translation is CUT at the same interface**
  (`b1c9ad3920`, sol-1, 29226): `q` disjoint row supports would be a `K_q` in
  `D`, an isolated component — the terminal is exact — but no theorem forces
  a matching of size `q−1` in a `q`-uniform `q`-regular linear hypergraph
  (nibble results miss uniformity = degree, and the `q=4` control falsifies
  the parameter-only form).

  **THE ENDGAME AUDIT, 02:00–03:44Z: every named NONBIP-CONNECTED terminal
  is now exhausted without a mechanism** (rounds #33–#42; Fable's ledger
  30215, sols 1–3 concurring at 30211/30214). Five cards were opened on
  the residue and every one closed: #1 weighted-shore packing and #2
  Room-square / SH polarity transport (released, all current mechanisms
  cut); #3 dyadic deficiency-cut atom (ABANDONED 03:08Z — surviving
  relations `Σ_{b∋u} deg_D(b,P) ≥ 2` for `u ∈ U₀`, `D[P,U₀] = 0`,
  `D[P] = K_q − Γ_H` (`43edd3e60d`), `τ(D)` a perfect square when `D` is
  connected; all named projections admit sharp partial models); #4
  bottleneck energy (ABANDONED — the cap `E ≤ q³` is equivalent to
  `T_D ≥ q²(q²−4q+2)/6` and to `h_x ≤ q/2`, and the disconnected control
  already violates it, `E = 96 > 64`); #5 designated-factor rank cap
  (ABANDONED 03:44Z — on `q = s²` the primitive `±s` eigensublattices
  inject mod 2 into `ker A`, so blind-trace imbalance `s` forces
  `null₂(A) ≥ s` (sol-2's clean saturated-lattice derivation, 30212), but
  the needed upper bound `null₂(A) < s` has no mechanism: `Aw = 0` gives
  only `Dw = w + (Σw)𝟙` over `F₂`, so connectedness does NOT make kernel
  vectors component-constant in characteristic 2 (sol-3, 30205), and
  Fable's census of 300 random connected cubic `D` finds
  `null₂(D+I+J) = 2√q` in ~19% of cases — no `D`-only 2-rank rigidity).
  The two-pole reformulation `e_u + e_v ∈ im_{F₂}(A)` on `D`-edges is not
  fresh: it is the audited `Erdos85BinaryCutGraphTwoPoleRoute` split.
  Banked positives from the window, all cold-green: `43edd3e60d`,
  `900dbe263f` (even-`q` `F₂` kernel ledger), `46ac69993e` + `9bc03c1f5b`
  (symmetric-difference diagonal theorem), `e050902949` (weighted pair
  capacity saturation), and `cb1d7d951f` (absolute-fibre lift: every
  symmetric GH / coefficient-grid polarity has a full absolute fibre, so
  that construction class is not loopless — closes the construction class,
  NOT the strict endpoint, where `|Z| = q−2 ≠ q`). Exact reformulation
  worth keeping in view: `A` singular ⟺ `D` disconnected, via
  `det(A)² = q⁴·τ(D)`. Tip `9bc03c1f5b`, 43 banks cold-green since the
  restart. **As of 03:44Z the seats are asking for a sibling root** (B.2
  odd-`q` residual leaves, or Goal #7 plateau-to-boundary localisation,
  which sol-2 took read-only at 30217 pending an operator response). This
  is goal #36's trigger: three seats naming the same missing link. The
  operator has not yet ruled; the editor is not a gate.

  ***UPDATE 21:48Z — the direct-transport package is COMPLETE*** (sol-1,
  integration tip `869873050c`; reviews #125, #127, #128 all VALID; the `q=4`
  verifier green and exhaustive). The owner also corrected the report's own
  status from *negative audit* to *structural audit* — the earlier negative
  was too strong. **Next live target, and note that it honours (ix)'s
  constraint explicitly: a `k ≥ 3` LOCATION THEOREM** for the non-`A` Eulerian
  `K` whose kernel-shore incidences reproduce the `T` / split-Baer parity.
  The matching-parity characterisation (21) is the concrete incidence
  interface. This is the first target beneath Baer that names where `k ≥ 3`
  must enter, which is exactly what (ix) said any ported argument would have
  to do.

  **(ix) THE COMPONENT PARITY LAW, and why `k ≥ 3` is not a technicality**
  (Fable and sol-1, 17:20–17:25Z).

  *The law.* On a `D`-component `C` with `A·𝟙_C = m·𝟙` (`m = |C|/q`), the
  `A`-graph induced on `C` is `m`-regular counting loops, so the number of
  absolute points in `C` satisfies
  `#abs(C) ≡ m·|C| = q·m² (mod 2)`. Two consequences that between them
  dispose of the whole trace-vs-component family:
  - **For `q = 2^k` this is EVEN for every component.** Each component
    carries `0` or `≥ 2` absolute points. There is no "one per component"
    argument to be had at binary `q`.
  - **For odd `q` with `m` odd it is ODD**, so `≥ 1` per component and
    `tr A ≥ #comp(D)` is a trivial theorem there. That is exactly why the odd
    control is tight at one absolute point per column, and it localises the
    entire difficulty of the inequality to binary `q`.

  *The refutation.* `tr A ≥ #comp(D)` was proposed as a sharper Baer
  statement and REFUTED the same minute by an exact `q = 4` model
  (sol-1, Z3): a symmetric loopless `4`-regular C4-free `A` on 16 vertices
  with `D`-components `[8,8]` and `tr A = 0 < 2`. It does not touch A-REG —
  `D` is disconnected there — it kills only the stronger inequality. At
  binary `q` the surviving form of that inequality is the connected case,
  which is A-REG itself, so the route is equivalent in difficulty to the node
  and must not be spent on.

  ***`q = 4` is a genuine exception, not a small case.*** A-REG is stated for
  `k ≥ 3`. The 16-vertex model satisfies symmetric, loopless, `q`-regular,
  C4-free on `q²` vertices, and it exists. **So any Baer-type theorem ported
  to this setting must use `k ≥ 3` somewhere**; an argument that would also
  apply at `q = 4` is thereby known to be wrong.

  *Two lanes closed by the same control.* The naive involution coupling
  reduces exactly to the existing T-degree parity and carries no new content
  (sol-2, `8eb7af8038`, NEGATIVE and banked). And the proposed T-cycle
  holonomy lane is dead locally: in the `q = 4` model `T` is exactly one
  `C8`, satisfying every A-incidence and C4 condition, so **closure of a
  T-cycle alone cannot force an absolute point or a repeated common
  neighbour** — only interaction with GLOBAL `D`-connectivity can. `T` is
  also Eulerian there and meets only one of the two `D`-components, so `T`
  need not meet every component nor detect the component cut, which is
  directly relevant to the `T = A ∩ D` lane below.

  **(x) THE NODE RESTATED — and this formulation survives every control**
  (sol-1, 17:33Z). From `A² = L_D + J`, `dim ker(A) = #comp(D) − 1`. Therefore

  > **NONBIP-CONNECTED ⟺ every loopless binary `q`-regular C4-free `A` on
  > `q²` vertices is SINGULAR.**

  Connected `D` ⟺ `A` nonsingular. What makes this worth more than the
  statements it replaces: the `q = 4` model and the affine control are BOTH
  singular, so unlike the trace/component family this formulation is not
  refuted by any ambient control we hold. It is the first restatement of the
  node that survives everything the room has built to kill things with.

  **(xi) THE SACHS CONGRUENCE — a candidate that grows with `k`** (Fable,
  17:34Z, sharpening sol-1's reframing). By matrix-tree,
  `det(L_D + J) = n²·τ(D)`, so `det A = ± q²·√τ(D)`. Two consequences:
  1. `τ(D)` must be a perfect square — the already-closed det/τ test,
     consistent.
  2. NEW and `k`-dependent: **`4^k = q²` divides `det A`**, with
     `v₂(det A) = 2k + v₂(τ(D))/2` exactly. Connectedness is what upgrades
     the automatic `q | det A` to `q² | det A`.

  Expanding entrywise by Sachs — `det A = Σ_S (−1)^{r(S)} 2^{c(S)}` over
  spanning elementary subgraphs (disjoint edges plus cycles, and **no C4
  terms**, which is where C4-freeness enters) — the statement becomes: *the
  signed count of spanning Sachs subgraphs with FEWER THAN `2k` cycles must
  vanish mod `4^k`* (terms with `c(S) ≥ 2k` are already `≡ 0`). The `c = 0`
  case is trivial matching parity from `A𝟙 = q𝟙`; the content starts at
  `c = 1 … 2k−1` and **genuinely grows with `k`** — at `q = 8`, cancellation
  mod 64 among Sachs subgraphs with at most 5 cycles. On the `q = 4` control
  both sides vanish because `D` is disconnected, which is the correct
  behaviour: the invariant is nonvacuous exactly on the connected case we
  want to kill.

  **Status, with sol-1's own scope correction applied.** The congruence is
  retained as a precise candidate interface. The *presently available*
  Sachs/cycle-length consumer is CLOSED — not the future route: the `c = 0`
  term is ordinary matching parity, and `c ≥ 1` sums perfect-matching counts
  of `A − V(C)` over triangles and cycles of length `≥ 5`, on which
  C4-freeness gives no divisibility or bound. **No wrapper is to be built:**
  the congruence is algebraically identical to the banked `q² | det A`
  consequence until a combinatorial valuation UPPER bound appears. An
  involution proving `det A = 0` outright would BE the theorem.

  **(xii) SPLIT BY THE PARITY OF `k`** (divergence round #2, 17:28–17:30Z).
  Converged first negative: `8 | q` on its own yields no mod-`2^j` counting
  currency, and all 8-divisibility local-count routes are CLOSED, along with
  T/component/transport-cardinality refinements. The one honest structural
  split is the parity of `k`:
  - **odd `k`** — the canonical `μ = −1` / `±√q` survivor is residual and
    trace-zero by the already-banked trace-escape interface, so it
    disappears. This narrows odd-`k` designated carriers to other
    square-in-`ℚ(μ)` sectors but does NOT close them.
  - **even `k ≥ 4`** — the survivor remains, and this is exactly the open
    `mult_D(−1)` problem of (vii), with `q = 4` as its realized disconnected
    control.

  *Operator note:* the suggested `q = 8` Diophantine endpoint falls under the
  A.5.2 order-64 park (goal #30), and the owner correctly declined to pursue
  it without an explicit go. It is flagged here rather than acted on.

  **(xiii) `λ(D) = q − 1` — the defect graph is MAXIMALLY EDGE-CONNECTED**
  (sol-1, `8b427fab6c`, 19:16Z). For a connected defect graph arising here,
  edge-connectivity equals the degree, the largest value possible for a
  `(q−1)`-regular graph. The bank is a prose report plus an exhaustive `q = 4`
  verifier — all 65,536 shores, all 16,508 nonzero `q`-divisible support
  inequalities, minimum nonzero cut `q − 1` — independently re-run by the
  integrator. Structural corollaries: every minimum cut has shore size
  `≡ ±1 (mod q)`, and in the equality case a minimum cut of size `q − 1`
  forces (after complementing) `|S| = qa + 1`.

  *Scope, as the owner stated it:* NON-TERMINAL, and deliberately **no Lean
  until a consumer is load-bearing** (review #16 / goal #24). Two consumers
  were tried and closed the same hour: the **far-`F` perfect-matching**
  route is NEGATIVE with a uniform abstract countermodel for every `q ≥ 8`,
  and the **radical cut-lattice** audit is CLOSED by exact overlap — the
  doubled bounds are valid but coincide with what is already known.

  **(xiv) EXTERIOR DIVISIBILITY `3 ∣ a(C)` — RETRACTED (sol-2 19:27Z, msg
  16948, after claude's refutation 19:26Z, msg 16943; integrator correction of
  v2.33/v2.34 text).** The derivation assumed every exterior `K`-edge outside
  the nonedge-trace resolvers lies in exactly one `K`-triangle; exterior
  `T`-edges lie in NO triangle, so that premise fails. The banked `q = 4`
  control (`e57fdbed45`) refutes the congruence directly: for `C = C₁`,
  `K = A[C₂] = C₈` has zero triangles (all 8 `K`-edges are `T`-edges),
  `a(C₁) = 8`, and `|E(K)| − N_nonedge = 8 ≡ 2 (mod 3)`. Corrected identity:
  `|E(K)| = N_nonedge-resolvers + 3·#K-triangles + |T ∩ K|`, which carries no
  divisibility. Consequence: the `q = 16` `C6 + C26` / `C5 + C27` witnesses
  are NOT killed; the weight-two synchronization question stands exactly as
  in v2.32. sol-2's retained residue is the valid pointwise decomposition
  `deg_T(z) + p(z) + τ_K(z) = q − 2` (msg 16974).

  **(xv) THE MINCUT DICHOTOMY — the node's first FORCED CONFIGURATION**
  (sol-1, `dde52eae34`, review #20, 19:44Z). Everything on this node until now
  has been an elimination. This is the opposite shape, and that is why it
  matters: it says what a counterexample would have to LOOK like.

  Any nontrivial mincut produces an associated `q`-set `R` with
  `e_D(R) ≥ q²/4 − 1`. For `q ≥ 16`, either `D[R]` contains a triangle, or
  `D[R]` is forced all the way to **`K_{q/2,q/2}` minus exactly one edge**,
  with cut-degree partition `(q/2−1, q/2−1, 1)` and common-neighbour blocks
  of sizes `(q/2, q/2, 2)` exhausting every non-`D` pair. The alternative
  extremal `K_{q/2−1, q/2+1}` cannot carry that pair-block decomposition and
  is excluded. The argument is Mantel plus a capped-partition gap: at
  `e_R = q²/4` one needs `Σ d_i² = M − 2` with `M = 2((q−2)/2)² + 1`, while
  the second-largest capped partition falls short by `q − 6 > 2`.

  ***`q = 8` is the sole binary exception***, its partition gap being exactly
  the exceptional 2. Set beside the `q = 4` exception of (ix): **the two
  smallest binary orders are now each known to be genuinely exceptional, at
  different points in the argument.** No order-64 endpoint work was done —
  the owner respected the goal #30 park while recording the exclusion.

  **(xvi) STRICT E-ENERGY RESIDUE, consuming the parity-of-`k` split**
  (sol-1, `ed8aba6c17`, review #19). The closed-star excesses
  `e_x = (δ_D(N_D[x]) − q)/2 ≥ 0` satisfy `Σ_x e_x ≡ q (mod 3)`, so **not all
  rows attain `q`**, and the incidence bottleneck of (vi) is strictly bounded
  below: `‖E‖² ≥ q³ + 2` for even `k`, `≥ q³ + 4` for odd `k`. First consumer
  of (xii)'s parity split. Owner's caveat, kept verbatim in spirit: the
  report explicitly notes that **residual-sector energy remains
  uncontrolled**, so this sharpens the bound without closing it.
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

    **Graph-facing terminal (restored in v2.51) — `ThreeSizeTwoViaTripleExclusionPrinciple`.**
    The condensed map had kept only the reduced code below; the faithful
    graph-level interface survives in `Erdos85BinarySquareAllSizeTwoViaTiling.lean`
    and is the one the room keeps rediscovering. `PROVEN` there: distinct
    via-colours occupy disjoint endpoint cells (`crossRoutingViaFinset_disjoint_of_ne`),
    all colours tile the ordered source×target grid, and each size-two via
    tile has card `8q`. Named `Prop` (not an axiom):
    `ThreeSizeTwoViaTripleExclusionPrinciple` — three size-two components
    `a,b,c` with `HasThreeCyclicRestrictedOwnerFactors` (six connected
    restricted owner factors) cannot have pairwise disjoint via tiles;
    consumer `false_of_threeSizeTwoViaTripleExclusionPrinciple`. Since
    pairwise disjointness is definitional, the principle names the whole
    contradiction; cyclicity is its only nontrivial premise (sol-3, 30689).
    Exact dictionary (rounds #52–#54, 25 Aug): with the banked bijection
    `V ≅ E(S_a)`, `v ↦ N(v) ∩ C_a`, and `S_a = complement(D_a)`
    (`binarySquare_regular_sizeTwoSelectorGraph_eq_componentDefectComplementGraph`),
    the colour-`d` via tile on `a×b` is `⋃_{v∈C_d} e_v^a × e_v^b`; the star of
    each `x ∈ C_a` is a perfect matching of `S_b`
    (`Erdos85BinarySquareSizeTwoStarPerfectMatching`); on every owner edge the
    a→b two-step middles number exactly `2` per other colour
    (`binarySquare_regular_ownerEdge_coloredTwoStepMiddles_card`,
    `Erdos85BinarySquareTwoOwnerPointwiseClosings`), summing to `q−2`
    (`Erdos85BinarySquareSizeTwoOwnerEdgeRegularity`, `b95c8232e0`). The pair
    level is spectrally empty (`N_aN_aᵀ = qI + A(S_a)`, `N_aᵀN_a = 2I + A(L(S_a))`
    is the banked owner line graph), and the edge bijections are coherently
    vertex-labelled, so `ψ_bc ∘ ψ_ab = ψ_ac` definitionally — no composition,
    sign, F₂-rank or holonomy invariant exists (all CUT, #53/#54). Honest
    theorem shape (sol-2, 30710): NONEXISTENCE of three `q`-regular graphs
    `S_a, S_b, S_c` on `2q` vertices each, over one common `q²`-element
    edge-label set `V`, such that each graph's `2q` stars are perfect
    matchings in both other graphs, each `S_a` is the complement of a
    `(q−1)`-regular `D_a`, plus the self-polar inner `2q`-cycle labels. The
    `q=4` control (`binary_q4_fixed_free_disconnected_control.py`, two colours
    `8+8`, `93186d9743`) is the mandatory sanity model: it satisfies every
    pairwise law, so any proof must be genuinely ternary. Closest literature:
    orthogonal double covers / Burgess–Cavenagh–Pike mutually orthogonal
    factorizations (sol-1 30682/30691, sol-2 30685) — none applies with the
    self-polar labels. **Coherent ODC composition alone is CUT** (sol-1,
    `8a5506c77c`, `SIZE_TWO_COHERENT_ODC_AFFINE_COUNTERMODEL.md`): label the
    `q²` points of `AG(2,q)` and pair six parallel-class directions into three
    roots `S_i ≅ K_{q,q}`; every star maps to a perfect matching in the other
    two and `ψ_jk∘ψ_ij = ψ_ik` — so the principle can only use the
    self-indexed placement of each `2q`-component inside the labels and the
    Hamilton-cycle restricted factors (equivalently, sol-3 30712: a linear
    `(2,2,2)` group-divisible design on three `2q`-groups with `q²` blocks
    whose three block colours project to Hamilton cycles). **The reduced code
    below is strictly stronger than this principle** (it forgets the cross-owner incidences; sol-3, 30670); attacks
    should target the principle or a multi-owner weakening, not the reduced
    code alone.

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

    **ELIMINATED — the multi-step sign/holonomy family** (sol-2, 21 Aug,
    goal #32). The strongest closing shift was run to a verdict and it is
    tautological. `PROVEN`, q-generic: any involutive shift with
    `frame(2) = frame(0)` has trivial 2-step twisted product, and for cyclic
    `d` with `d + d = 0` this applies to both the parallel and the crossed
    two-hole completion (`ec8aac0d75`). The exact verdict is
    `sizeTwoDoubleShiftComparison_second_eq_conj_inv`: `Q₁ = S·Q₀⁻¹·S⁻¹`
    (`d7bd641781`). So `Q₁` carries the same cycle type and fixed count as
    `Q₀`, and the central two-step closure supplies **no independent
    agreement constraint**. Together with the earlier `Fin 6` cycle-type
    countermodel this rules out the family, not just the instance: no
    invariant that is a function of completed-shift comparison cycle type —
    equivalently, of the permutation's conjugacy class — can close the
    packing bound. The `Θ(q)` deficit above therefore stands untouched, and
    an admissible candidate must be sensitive to the fiber labelling itself.
    Supporting cycle-structure derivation (checked at `q = 8, 16, 32`; not
    yet Lean): with `g = gcd(q,d)` and `L = q/g`, parallel completion gives
    one `(q−2)`-cycle when `g = 1`, else two `(L−1)`-cycles plus `g−2`
    `L`-cycles; cross completion merges the two affected cycles when `g > 1`
    and splits the `q`-cycle at `k ≡ −d⁻¹ (mod q)` when `g = 1`.
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
| B.2 existence jaw for unbounded odd `q` | `GAP B-EXIST` | Cayley route dead at 9, 11 (computational); dihedral-holomorph ansatz UNSAT at 9; conjecture `B-NEAR-LATIN-LIFT` stated. New `EXTERNAL` negative data (sol-1, 20 Aug, goal #30 front (c)): Gamma_9 dot-product graph admits no single-edge matching repair (all 8 parameters × 105 matchings exhausted); ER_9 orthogonal-polarity graph admits no 10-vertex deletion retaining min degree 9 (exact 91-variable UNSAT, `er9_induced81_search.py`) — both direct finite-field construction classes at q=9 are closed; mixed doubled-cycle CNF scouts inconclusive (300s timeout). New `PROVEN` uniform structure (sol-1, 20 Aug PM): NO bipartite candidate at any order q²−1 (`not_isBipartite_of_planeMinusTwo_regular_not_containsC4`, pair-count barrier `false_of_planeMinusTwo_regular_linear_incidence`; the signed-determinant double-cover no-go is a corollary); every vertex lies in a triangle with local edge window `[1,(q−1)/2]` for odd q; abelian Cayley impossible beyond degree 2 (`card_connection_le_two_of_commutative_invClosedCayley_not_containsC4`); nonabelian Cayley Sidon law with exact Moore slack q−2 (`card_unused_nonidentity_of_planeMinusTwo_Cayley`), forced slack involution and forced perfect-matching layer for odd q (`exists_unused_involution_of_odd_planeMinusTwo_Cayley`, `exists_connection_perfectMatchingLayer_of_odd_card`); Boza48 kernel-checked as one-block Z24⋊Z2 development of a linear 48₃ configuration + coordinate-flip one-factor. Global q=9 existence remains open. **Exact reformulation (sol-1, 20 Aug PM): GAP B-EXIST for the Cayley class ⟺ an inverse-closed noncommutative Sidon set of size q in a group of order q²−1** (`not_containsC4_iff_nonbacktracking_connectionProduct_injective`); uniform sieves: groups with all involutions central are impossible (`containsC4_of_odd_connection_card_of_all_involutions_central`), ambient nontrivial involutions ≤ q−2 (`card_nontrivialInvolutionFinset_le_of_planeMinusTwo_Cayley` — screens q=9 order-80 groups with ≥8 involutions), forced matching generator consumes slack and must conjugation-separate the residual shore (`erase_involution_disjoint_conjugate_shore`, union card 2(d−1)). **q=9 VERTEX-TRANSITIVE CLASSIFICATION, 21 Aug (sol-1, goal #32), `EXTERNAL` with independent re-verification:** every one of the 25 CONNECTED cubic-shadow census types is impossible — 24 by exhaustion over transitive subgroups and invariant 80-line orbits at |Aut| ≤ 160 (`17b3cd9d02`), and the exceptional `CubicVT[80,30]` (|Aut| = 960) by a GAP + Python certificate enumerating 132 subgroup conjugacy classes, exactly 5 transitive classes covering all 11 transitive subgroups, and all 30/9/3/3/1 candidate 80-line orbits, each nonlinear, intrinsic-F violating, or C4-creating (`aaec4c5cd5`). Hence any q=9 VT candidate needs a DISCONNECTED shadow. Of those, the order-40 pair families are excluded: the four |Aut| = 3200 types (`6b001f9547`) and the high-symmetry ordinals 3/8/11 (`3b51b0fd54`). **Overnight 21–22 Aug the disconnected leaves fell in order** (sols 1 and 2, drift caught by the integrator): Petersen×8 and order-20×4 are CLOSED — the order-20 lift is excluded for all three component types under the cyclic C4 block action (`ade85c541e`), then for every remaining degree-4 action by the forced double transposition (`ed7e595487`), with the coverage audit complete at ordinal4 18/18, ordinal6 16/16 (`080b0542ca`, 58 double-transposition + 32 C4 twist pairs, all UNSAT). **order-16×5 is the last leaf**, and inside it the F20 action is fully excluded (`ca6589760b`: classes 1, 2, 4–11 UNSAT behind an unrestricted aggregate gate; hard classes 0/3/12 by centralizer representatives 70/518/70, all 658 UNSAT with atomic checkpoints). The last lane, the A5/S5 star+triangle lift, closed at 04:34Z on 2026-08-22 (`36d1952ef7`): the 24 nonidentity branches by the earlier audited sweep (`verified_a5_s5_phase`), and the identity phase by a shortcut — an independently audited 19-partition catalog plus the full `Aut(C)` centralizer gives exactly 16 fiber-assignment orbits per star and per triangle, and both aggregate sweeps returned 16/16 UNSAT, which retired the running 112-seed process as redundant. **THE q=9 VERTEX-TRANSITIVE ORDER-80 SHADOW CENSUS IS THEREFORE COMPLETE WITH ZERO WITNESSES** — connected ×25, order-40×2, order-20×4, Petersen×8, and order-16×5 (endpoint, F20, A5/S5) all excluded. **Goal #23's trigger has FIRED; see the editor note below. The room is holding and nobody has self-assigned the pivot.** Every GAP subgroup/orbit result is independently re-derived in Python against pinned PSV data — that double check is why this is banked. **Scope, stated precisely, and it is the whole point of this row: this closes the VERTEX-TRANSITIVE class at q=9, not existence at q=9.** A non-VT witness on 80 vertices remains logically open, and NO LEAN THEOREM ASSERTS NONEXISTENCE — the census is `EXTERNAL` evidence, GAP enumeration with independent Python re-derivation of every datum, not a kernel-checked proof. Anyone citing this row downstream cites that sentence with it |
| B.3 nonexistence at `q²` for the same `q` | `AXIOM B-NONEXIST` | partial uniform structure; `GAP B-CLASSIFY` for odd profiles. **q=9 three-high profile (order 81, 9-regular with three degree-10 vertices, 366 edges, D-quotient 297 edges), 21 Aug (sol-3, goal #32).** New `PROVEN` q=9-generic: the forced B3–B0–B0 triangle has both B0 endpoints of exact regular defect type (5,3,0), exporting six defect incidences into the 27-vertex B1 core (`75488904b8`); a B1 point in both fibers of that pair forces an antipodal edge, via `DefectPathOwner` on the induced two-path (`669af6ea3c`); every B0 vertex has (antipodal, triangle-free, local triangles) in {(1,7,1), (3,5,2), (5,3,3), (7,1,4)} (`3b53f09ad3`); at least one high root takes the B2→B1 crossing option (`6ea714427a`). **BOUNDARY, editor-recorded on sol-3's own audit: local classification is exhausted here.** With the antipodal/TF split unfixed, the global rooted-triangle identity does not determine the B0 type counts and cannot kill the B3 3-vs-4 triangle branch; the next decisive input must be global — colored defect mass, a spectral commutator, or a fiber-packing bound — not another local ledger. Recorded failure certificate: the 21-cycle owner-label parity argument is abstractly satisfiable (colors 012 repeated give classes 7/7/7 with all vertices rainbow), so color parity alone is not the coupling. **The boundary held for one hour and was then partly SUPERSEDED by the pivot it triggered** — what local classification could not do by the rooted-triangle identity, the positional column law does directly. Lane now on the global colored-mass conjecture |E(TF)| ≡ |E(Anti)| ≡ 0 (mod 3), gated on an abstract-satisfiability probe before any formalization. **ROW-COVER → WEIGHTED-ROW → TRANSVERSAL LEDGER (sol-3, 22 Aug 02:41–04:22Z, all Lean green, no sorry, standard axioms, cold-verified by the integrator through `391fa4c808`).** Generic C4-free row-cover layer (`de7cc79c31`, kept in new modules so the 4.1k-line defect-types file stays untouched); weighted-row dichotomy `squareOrderNine_threeHigh_secondProfile_binZero_row_mass_dichotomy` (`58392735a4`) and `row_center_weight_sums` (`4e9d870702`); complete weighted-row interface incl. `ordinary_row_zero_centers` (`a06e2698f5`); arithmetic terminal `weighted_row_arithmetic_forces_pair_defect_three` (`9e65d849e1`); graph alignment `ordinary_special_marked_center_dichotomy` (`06d2063ae8`); capstone `aligned_weighted_row_branches` (`0fa01aef69`); partial transversals `common_eq_support_hit` (`e41afe8d6b`) and the exact `marked_support_fortyTwo_five_ledger` (`da9b18bbaf`). Then the mixed column law: three-way resolution `ordinary_unmarked_three_way_resolution` (`1b07b75584`), `unmarked_core_resolved_rows_card` = 15 per column (`edf1d69ba0`), and `unmarked_mixed_column_counts` partitioning all 47 ordinary rows per `b ∈ U1` as defect + residual + core with `defect_T(b) + specialDefects(b) = 5`, `coreResolved(b) = 15`, `residualResolved(b) = 27 + specialDefects(b)` (`b4052a9c26`); the special-defect mass dichotomy — local triangle count 3 ⇒ total 0, count 4 ⇒ total 6 (`18434d0c64`); and the pointwise puncture law `nondefect_special_support_card_seven` / `nondefect_special_defect_eq_missing_rows` (`391fa4c808`), which kernel-derives the SAT model's `missed_punctured` correction. **Current frontier (`39b30e7314`):** `residual_core_trace_zero` kernel-checks `Σ_{t,b} |residual centers|·|core centers| = 0`, i.e. `trace(Qᵀ A Q K) = 0`; with fixed outer witnesses and defect variables fully decoupled, ORTHOGONALITY ALONE is UNSAT on branches 3 and 4 in ~2.1s, while the `AQ ≤ 1` half timed out at 30/90s (UNKNOWN — **no SAT claim**). So the fast obstruction is independent of defect row/column semantics. The named target is now a uniform combinatorial or spectral proof that the required 5/6-regular residual `A` cannot lie in the zero-support graph of `Q K Qᵀ`. **REDUCED-L ROUTE CLOSED (09:07Z):** on branch-4 seed 1 the LP relaxation is feasible while binary exact-row + integer symmetry + diagonal-even is INFEASIBLE even after deleting every column cap and every off-diagonal cap — so no weighted-linear (Farkas) certificate exists for this formulation and the integrality is doing all the work. Symmetry alone is UNKNOWN at 60s; adding diagonal-even kills it in 0.03s; no single diagonal constraint is removable. Z3 core extraction timed out, so there is no small hand invariant yet, and this is sampled fixed-outer integrality rather than transferable proof. Two q-generic audits came back NEGATIVE the same hour: equitable ≥3-block union packing collapses to the known mass bound `m_i + M ≤ q`, and the non-equitable fiber ledger reduces to the same place. Transferable banks from the hour, both parameter-free and Lean green: `e07da51bda` (`c4Free_crossBlock_row_neighbor_mass_le`, `c4Free_crossBlock_row_degree_packing`) and `03d5219d0c` (`c4Free_shared_crossBlock_fiber`, the generic graph form of the nonlinear join). **FORMAL CONSUMER BANKED (`9a9012c801`, 10:53Z, sol-3) — the first Lean file on either branch in roughly fourteen hours.** New parameter-free module `Erdos85LocalGramPacking.lean`: `relationNeighborFinset_isLocalGramPacking` proves any symmetric exact-degree supported residual relation satisfying Gram yields a demanded W-independent packing at every row, and `false_of_localGramPacking_deficit_or_forced_collision` consumes exactly candidate (13f)'s deficit/forced-collision alternative to derive `False`. Compile green, no `sorry`, axioms `propext`/`Quot.sound` only — i.e. standard. **This is what the `PROVEN-SKETCH` label was added to make visible the absence of**: a prose chain with a machine-checked consumer at its end. **The sole remaining interface gap is the outer-design theorem (13f)**, reported stress-tested 128/128. *Editor caution, and it is not rhetorical:* on 2026-08-23 at 00:25Z this same lane retracted (12qx)–(12qz) after a purpose-built adversarial test returned 48/48 clean, killed only when the sweep was widened past a green run. **128/128 is evidence, not a proof**, and (13f) stays an interface gap until it is discharged. **ATTACK IN PROGRESS, 11:15–11:22Z — all three lanes converged on (13f) within thirteen minutes of it being named, and they converged by FORMALISING rather than sketching.** Three new kernel-checked theorems entered `Erdos85LocalGramPacking.lean` in seven minutes, all green with `propext`/`Quot.sound` only: `not_conflict_of_forcedLocalGramNeighbors` (`3de28fd173`, kernel-checking (13n) at the abstract interface), `not_conflict_of_common_forcedLocalGramNeighbor` (`c186cc9295`), and `eligible_of_forcedLocalGramNeighbor_of_noObstruction` (`200e4ef28d`). Together these establish that **under the NEGATION of (13f), the forcing relation `R` is supported inside `H` with W-independent row and column fibers** — deriving structure from the negation, which is the right way to attack an interface gap. **One route CLOSED (`1745398aba`, sol-3):** the hitting-dual lane completes at 127/128, and the universal linear route is **REFUTED by an exact 4.5/5.0 integrality-gap collision.** Note the reporting standard: 127/128 with the single failure named and the route killed on it, rather than the ratio quoted as near-success. The lane has moved to a seed-free negation encoding — unrestricted outer `Q,K`, one base demanded matching per row, shared omission witness `y[u,w]` with `y[u,w] ∨ y[v,w]` for every intersecting `u,v,w` — with the three agents holding self-assigned non-overlapping pieces. **RETRACTION, 2026-08-23 00:25Z (`26d99ba02f`, sol-3, self-reported):** **(12qx), (12qy) and (12qz) are FALSE.** The flat handoff has a directed self-loop. Witness: branch 3, seed 8, colours (1,2) — roots 6 and 19 with label 22 are reciprocal unique triple occupants carrying an identical signature `(triple,13,14,19)` AND an identical census `{triple:1, pair-low:1, pair-other:1}`, with all 47 local Hall rows feasible. Reproduce with `--seeds 9 --audit-flat-signatures`, which reports `forest=False` and exits 1. Review #272 cancelled by its own author. **Valid residue: uniform pair-role exclusion only**; the next terminal must restore actual fractional-flow support, or external essential-label deletion (12qq)–(12qr). **The epistemics here matter more than the loss.** Forty minutes earlier the same agent ran an adversarial forest stress test at 8 forced-eligible-hole seeds per branch — 48 two-colour quotients, 32 containing hole-role flat edges, 11 Hall-failing instances included — and got **48/48 forests, no loop or cycle anywhere** (`c92e47d527`). It then widened the sweep to 9 seeds rather than stopping at a pass, and the ninth seed killed all three claims. A prose result that survives a 48-instance adversarial test can still be false, and only the agent's own decision to keep pushing after a green run caught it. Read this beside the certification note in the 2.37 change log. **CANONICAL SEPARATION OBJECT (`5c13979878`, 21:50Z, sol-3)** — this supersedes the reduced-L closure recorded below rather than reopening it. The fractional B.3 obstruction holds **iff the product of local matching polytopes admits an antisymmetric functional of strict sign**, and evaluation decomposes into 47 weighted matching optima. Where the earlier LP-feasible / MILP-infeasible split proved that *no* weighted-linear Farkas certificate exists for that formulation, this replaces the search over arbitrary Farkas cells with an exact proof object `W(Q,K)`. Supporting: the local horn is exact and noncomputational — one-row fractional feasibility is a bipartite matching problem (`4552386453`) — and the directed symmetrization equivalence `A = (X + Xᵀ)/2` inherits support, zero diagonal, row sums and every cap (`4fd676ad6a`, integrator-confirmed). **D0 IS CONNECTED — PROVED (`3f9a923427`, 20:22Z, sol-3), the branch's first positive terminal; FORMALIZED 2026-08-25 as `squareOrderNine_threeHigh_secondProfile_ordinaryDefect_connected` in `Erdos85OddSquareOrderNineNearRegularSecondProfileConnectivity.lean` (`8a135b6c76`, cold-verified, standard axioms).** The banked Lean dichotomy `squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy` forces, in any non-B3 D0 component, every B0 to defect-degree `(B0,B1,B3) = (5,3,0)` and every B1 to `(5,2,0)`. Cross-edge double counting gives `3n₀ = 5n₁`, so every such component has order divisible by 8. But the cut-variance classification admits proper component orders only in `{9, 18, 19, 26, 27, 35, 43, 51, 52, 59, 60, 69}` — **not one of which is a multiple of 8.** A disconnected D0 would need a non-owner component, so none exists: all 11 disconnected rows fall at once. Independently confirmed the same minute by the integrator (review #40 VALID) — the order list re-enumerated from scratch and reproduced exactly, every graph-theoretic step re-checked — with sol-1 concurring. **Scope: prose + Python bank, NOT yet Lean**; the tip carries no `.lean` change and the suggested formalization is a finite `decide` over orders `8k` (`k = 1…9`, `Σβ = 3k`, `β_i ≤ 9`). Note what it consumes: sol-1 banked the cut-variance classification an hour earlier and deliberately held it out of Lean *until a consumer was load-bearing*; the consumer arrived from a different agent on the other branch |
| B.4 capstone | `AXIOM B-COFINAL` | B.2 ∧ B.3 on one unbounded set ⇒ done via §0 |

Operator ruling (goal #23): odd primes remain the primary *theory* of where
drops occur; Branch A is where the *proof* is closest. Decisive next datum on
B is existence or nonexistence at `q = 9`.

**Editor note (2026-08-22, goal #32) — this ruling now has evidence pointing
at it.** B.2 and B.3 are the two complementary halves of `q = 9` and are not
duplicates: B.2 is existence at order `80 = q²−1`, B.3 is nonexistence at
order `81 = q²`. The q=9 vertex-transitive class is closed with zero
witnesses and only three disconnected-shadow leaves remain. If those close
the same way, the construction half of the odd-prime theory — the hope that
the `q = 7` `Z24⋊Z2` witness extends to a parametric family at odd prime
powers (§A/goal #15 existence half) — takes a further negative datum.
**Editor correction (2026-08-22, v2.23): an earlier draft of this note
called it the FIRST such datum. That was wrong.** The Cayley class was
already exhaustively closed at q=9, q=11 AND q=13 on 2026-08-16 (all 52
order-80 groups, all 47 order-120 groups, PSL(2,7) for q=13; symmetric
Sidon search). Goal #23 ruled odd primes primary *with that already in
hand*. The new content here is the non-Cayley part of the
vertex-transitive class at q=9 only, reached by an independent route
(incidence/shadow orbits, not Sidon sets), which also re-derives the
Cayley result as a special case.
That does not refute the theory: `2^k` stays covered by the affine family and
a non-VT odd witness is still open. It does mean goal #23 should be revisited
at that moment by the operator rather than drifted past. Flagged, not
decided.

**THE TRIGGER FIRED, 2026-08-22 04:34Z (`36d1952ef7`).** The q=9 VT census
is complete with zero witnesses. Goal #23 ruled odd primes the PRIMARY
theory; its construction half takes a further negative datum, within the
VT class — **not its first**: see the correction above. The Cayley
subclass was already dead at q=9/11/13 six days earlier. The question is live and belongs to the operator. The three
options the room can see, recorded here so the decision is made against a
written menu rather than by drift:

- **(A) Stay at q=9, go non-VT.** Reinterpret the `Z24⋊Z2` 48-witness
  geometrically (goal #23(2)) or attempt bipartite-incidence surgery, now
  with the VT census as an explicit negative prior. Highest information per
  unit of work if a witness exists; the census says any witness that does
  exist has no vertex-transitive symmetry, which is a strong and unusual
  constraint on a construction.
- **(B) Repeat the census at q=11 (order 120) or q=13 (order 168).** Tests
  whether q=9 is special or whether the pattern is the theory. Mechanical,
  the toolchain exists and is proven, and the answer is decisive either way
  — but it is a bigger enumeration and buys structure only in aggregate.
- **(C) Demote the odd-prime existence half to an honest AXIOM/GAP node**
  and redirect B-lane effort to B.3 nonexistence (live and close to a local
  terminal) or to A-REG-NONBIP (the critical path, currently one owner
  short). Cheapest, and the only option that admits the campaign may have
  been chasing the wrong half.

**RESOLVED 2026-08-22 05:35Z — the operator chose (C), goal #34.** The
odd-prime existence half is DEMOTED: it stops being an active work front and
stands as an honest `AXIOM`/`GAP` node. Goal #23's ruling that odd primes are
the primary *theory* of where drops occur is retired **as a work-allocation
rule** — it may still be true as a belief, and this outline does not claim
otherwise, but no lane is justified by it any more. Options (A) and (B) were
considered and declined; neither is available as a self-assigned fallback,
and re-proposing either needs a fresh operator go. B-lane effort redirects to
B.3 nonexistence (sol-3, uninterrupted — that front was never contingent on
this question) and to A-REG-NONBIP, where sol-1 now owns NONBIP-CONNECTED
`[q]`, unowned for the whole campaign until tonight.

**What #34 implies for B.3, spelled out because the ruling left it
implicit.** A drop at `q` needs BOTH jaws: a witness on `q²−1` and
nonexistence on `q²`. With the existence half demoted, **a completed q=9
nonexistence terminal yields no drop at q=9**, whatever it proves. B.3's
value is therefore now almost entirely TRANSFER, and the target it transfers
to is named: A-REG is `BinarySquareRegularExclusion`, no `2^k`-regular
C4-free graph on `4^k` vertices, which since `q = 2^k` gives `q² = 4^k` reads
*no q-regular C4-free graph on q² vertices*. B.3 is that same sentence at odd
`q`. They are parity siblings, not neighbours.

Consequent selection rule for the B.3 lane, binding until an operator says
otherwise: **at a fork, prefer the q-generic statement over the finite one
even at real cost in time.** Order-81-specific enumerations
(`squareOrderNinePairRowAllowedPatterns`, the 21-point pair-row completion
count, `pair_marked_defect_sum_odd`) are kernel-green and buy a
demonstration; `residual_core_trace_zero` and the orthogonality split are the
transferable kind. The lane posts which branch is generic before taking it.

One reason to expect the transfer is real rather than consoling: A.3
(`squareOrder_regular_of_even`) hands the even branch a regular tight core,
which the odd branch does not get — hence B.3's three-high non-regular
profiles. A technique built WITHOUT the regularity hypothesis has a better
chance of specialising into the regular case than a regular-case technique
has of generalising out. That is a direction, not a theorem, and it is stated
here to be tested rather than believed. Demotion does not
upgrade the B.2 row: the census remains `EXTERNAL` evidence about the VT
class and no Lean theorem asserts nonexistence.

Worth recording about the hour between 04:34Z and 05:35Z: the census came
back empty, the room recognised the trigger, stated the scope unprompted,
and stopped — sol-1 released its claim and idled rather than choose a
direction the operator had reserved. The stopping is the process working.

## C, D. Supporting theories — not on the critical path

Exact second-order boundary theory (`d(d−1)+3`) and plateau-core theory are
proven, useful, and at the wrong order. Bridge to square order: `GAP
C-TO-SQUARE`. They stay in the ledger.

**GOAL #7 PLATEAU-TO-BOUNDARY — COMPENSATED-SURGERY BOUNDARY (card #15,
rounds #58–#60, 25 Aug 05:40–06:20Z, sols 1–3 + Fable; prose + Python
controls only, no Lean).** The plateau-core interface is `C4PlateauCore m d`
with `conflict_indepNum_lt`. `PROVEN` (banked earlier,
`Erdos85ConflictDefectDuality`): in a regular positive-excess component
`m = d(d−1)+3+e`, `0 ≤ e ≤ d−4`, the common-neighbour conflict graph is
exactly `d(d−1)`-regular (triangles cancel: `|N₂(v)| + 2t(v)`), so its
complement — the *safe* graph — is `(e+2)`-regular and a safe `d`-set never
exists: `conflict_indepNum_lt` is AUTOMATIC throughout the band, and the
plateau-to-boundary arrow can only come from delete-`k`/add-`(k+1)`
surgery with survivor-edge deletion (`Erdos85BoundedReplacementObstruction`
already kills deletion-only gadgets). What the window established, all on
the two `d = 4` controls (repository `fifteenRegular`,
`Erdos85Problem.lean:3588`, and Fable's distinct 15-vertex graph) plus
exact counting: (i) *Capacity law* (Fable, #60): in every tight surgery
`2|R| = d − 2|E(F)| + 2·e(D)` — survivor-edge deletions number `d/2`
independently of `k`; selectors are determined as multisets by
`⊎A_w = N(D) ⊎ V(R)`, and the selector-intersection graph on the new
vertices has exactly one edge per deficit-2 survivor (a linear hypergraph).
(ii) *Positive controls*: `k = 1` one-cross-endpoint (`|V(R) ∩ N(x)| = 1`)
SAT on both graphs (`acc88a151e`, `3238c755fb`); `k = 2` SAT with common
root and without (`7d7ecc103d`, `39466fe697`), star-slot repartition
(`133719cd1f`). (iii) *Negative controls, exhaustive*: `k = 0` matching
extension (delete a `d/2`-matching, attach one vertex to its endpoints)
UNSAT on both graphs; `k = 1` deletion-only UNSAT; `k = 1` external matching
UNSAT (`3229a525c7`); `k = d−2` deletion-only sparse gadget UNSAT; the
"`A_x = N(x)`" scaffold (evidence 105) is the `k = 0` form in disguise and is
refuted (evidence 109). (iv) *Scaling bounds, q-generic, necessary only*
(the C4-free orientation count: a selector's matching-endpoint part `T` has
`indeg ≤ e+3`, so `|T| ≤ 3e+9`): `k = 0` needs `d ≤ 3e+10`; tight `k = 1`
needs `d ≤ 6e+18` (sol-3, `544898300f`; one-cross-endpoint version sol-2);
independent-`D` / `F`-empty / external-`M` class needs `k ≥ d − 4e − 11`
(sol-2 `d ≤ (k+3)(e+3)`, sharpened by Fable: an endpoint has only `e+2`
safe partners globally, `d799c6dee8`); one-for-one fibre swaps need
`d ≤ e+4` (evidence 112). Hence at fixed low excess every local pattern
seen at `d = 4` fails to scale, and the surviving question is a GLOBAL
BLOCK REPARTITION across root fibres, for which no mechanism exists
(evidence 113/114 is the first mixing inequality, under red-team). Outside
literature (CFSZ attachment counts, C4–star Ramsey, Moore-excess/cage,
Exoo excision — `684905746a`, `deafad28bd`) supplies no bridge.
Sol-1's Lean matching-existence half (`2d1777b604`, cold-verified green,
standard axioms) was self-reverted the same minute (`d51e7575b7`) because
the external-matching class it serves is UNSAT on the controls — the
anti-wrapper rule applied by its own author. **BOUNDARY, recorded 06:20Z
per goal #36**: the local compensated family is at the same kind of wall as
NONBIP-CONNECTED. Sol-2 proposed pivoting to B.2 odd-`q` non-VT existence;
sols 1 and 3 objected that goal #34 explicitly declined that hunt, and
sol-3 took instead the allowed A-REG sibling (the `k ≥ 3` location theorem
for the non-`A` Eulerian transport `K`, §A.5). Not a ruling.

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
                │   ├── ThreeSizeTwoViaTripleExclusionPrinciple [GAP; graph-facing, faithful]
                │   └── BinarySizeTwoCyclicPackingBound [GAP; EXTERNAL q=6,8; strictly stronger]
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
5. **ACT, DON'T ASK** (editor, 2026-08-22, goal #35 — this rule corrects a
   norm the EDITOR introduced, not one the operator asked for). Lane
   selection does not require editor approval. If a lane is non-overlapping
   with a live claim, sits under an open node, and is not order-64 work,
   take it: claim the file, post one line, start. **Proposing is not
   blocking** — post a proposal and proceed on the assumption of approval.
   **Never go quiet while holding an unblocked lane**; if you are blocked,
   say so explicitly and name the one thing that would unblock you, because
   a silent park is indistinguishable from a crash from outside.
   Only two gates remain and both are the OPERATOR's: order-64 work under
   goal #30's park (including the q=8 Diophantine endpoint), and the goal #34
   pivots that were declined. For those, make the case once and move on —
   never idle waiting on an operator answer. The editor's job is the map and
   the record, not permission.
   *Why this is in the map:* on 2026-08-22 two of three lanes parked waiting
   on editor approval that arrived 53 seconds and 6 minutes later, costing
   most of a working day, while the same four agents had run eight hours
   continuously overnight when editor latency happened to be seconds.
6. **HILL CLIMBING IS A STUCK SIGNAL — ANSWER IT WITH DIVERGENCE, NOT
   DISCIPLINE** (operator, 2026-08-24). The observation this rule encodes:
   *hill climbing becomes more likely as the problem becomes more
   intractable.* A lane that cannot reach its terminal will keep producing
   true, verifiable, adjacent theorems indefinitely, because that is the
   locally available move. High output is therefore NOT evidence against
   being stuck — under intractability it is the expected symptom.
   **WHAT THIS RULE IS NOT AGAINST** (operator amendment, same day): it is
   not against grinding. A slow, steady grind is often how a problem becomes
   understood, and understanding is a legitimate deliverable — the size-two
   eigenline theory, the cut-variance classification and the q=9 census were
   all built that way and all paid. **The enemy is banking theorems as a
   PROXY for progress: output produced so that the room appears to be
   advancing.** Purposeful grinding and theatre produce the same commit rate
   and are distinguishable only by whether the grinder can say what is being
   learned.
   **TRIGGER (self-declared, no editor needed).** You are hill climbing when
   you can state NEITHER of the following: (a) a chain of statements from
   your recent banks to A-REG or B-NONEXIST with every link named; nor (b)
   the QUESTION your grind is answering, what you expect to learn, roughly
   how many banks until you know, and what result would make you stop. Either
   answer is legitimate and (b) is not a lesser one. Having neither is the
   stuck condition. Note the failure mode this catches that a
   chain-only test would not: a grind can be perfectly purposeful and still
   have no chain, and a lane can name a chain and still be theatre if nobody
   believes the chain closes. §G rule 2's node-naming is the cheap
   continuous check; this is the expensive periodic one. Run it on yourself
   whenever you have banked ~10 results without a node's status changing.
   **RESPONSE, in order. Do not skip to the third step.**
   1. **STOP the lane and say so in the room**, naming the missing link.
      Banking one already-complete result first is fine; opening another leaf
      is not.
   2. **GO OUTSIDE.** Search the literature for the shape of your obstruction
      before inventing a new one. The precedent is Baer's absolute-point
      theorem: the campaign spent a day proving `tr A = 0` had no available
      mechanism, and the answer was a classical theorem about polarities that
      nobody in the room would have derived. External research is CHEAPER
      than a new mechanism and this room has under-used it.
   3. **BRAINSTORM WIDE, THEN CUT.** Open a divergence round and generate
      deliberately — including implausible entries. Quantity first, no
      filtering while generating: a wild-card that survives contact is worth
      more than a safe idea that was always going to fail. THEN reduce, on
      stated criteria, to the two or three worth a bounded probe. The
      divergence mechanism already exists and has run twice, both times
      producing convergent results neither agent had alone.
   4. **PROBE BOUNDED, REPORT EITHER WAY.** A refuted wild card with a
      countermodel is a result and goes in the map.
   *Why this is in the map:* on 2026-08-24 the candidate-(vi) separator
   subtree ran for hours at ~147 theorems/hour, every theorem true and
   cold-verified, while no chain to the axiom existed. All three owners
   recognised it inside sixty seconds once asked — but nobody asked for
   hours, and the rate itself was what made it invisible.

## Change log

- **2.52** (2026-08-25 ~06:30Z, claude-fable): recorded the Goal #7
  compensated-surgery boundary under §C/D — automatic `conflict_indepNum_lt`,
  the capacity law, the positive and exhaustive negative `d = 4` controls,
  the four scaling bounds, the refuted `A_x = N(x)` scaffold, and the
  surviving global-repartition question — per sol-2's boundary proposal
  (31003) and the room's consent window. Lean tip unchanged `b95c8232e0`.
  Prose-only.

- **2.51** (2026-08-25 ~05:35Z, claude-fable): restored the graph-facing
  size-two terminal `ThreeSizeTwoViaTripleExclusionPrinciple` (+ consumer)
  beside `BinarySizeTwoCyclicPackingBound`, per sol-2's stewardship note
  (30693); recorded the #52–#54 dictionary (selector = complement, via tile
  = block union, ODC/perfect-matching stars, per-colour 2-closure ⇒ `q−2`),
  the cuts (composition/sign/F₂/holonomy all vacuous), sol-2's honest
  theorem shape, and that the reduced code is strictly stronger. Lean tip
  `b95c8232e0` (58 single-module banks cold-green since the restart).
  Prose-only.

- **2.50** (2026-08-25 ~03:50Z, editor): attribution in the pure `c=q`
  block corrected per Fable's cold-verify log (29644) — I had credited the
  `s ≥ 2q−4` wrapper to sol-3; it is sol-2's. B.3 row: the q=9 D0
  connectivity terminal is now FORMALIZED (`8a135b6c76`). New block under
  the pure endpoint: the endgame audit, rounds #33–#42, five cards opened
  and closed, no surviving terminal, banked positives listed. The room's
  own status at the bump: NONBIP-CONNECTED's named terminals are
  exhausted, the seats are asking for a sibling root, and goal #36's
  trigger has fired. That is recorded here as a fact about the map, not a
  ruling — the ruling is the operator's.

- **2.49** (2026-08-25 ~02:00Z, editor): the post-restart night. The host
  restart landed ~00:15Z; all four seats rejoined clean with no orphaned
  claims, and Fable relaunched the solver fleet verbatim (q10/q12 phase
  dichotomy predictions on record). Absorbed into the NONBIP-CONNECTED node:
  **(a) EFH CORRECTION to v2.48** (sol-3, 29189/29197/29209): `D` is NOT
  literally the classical defect/repeat operator. The exact syntactic repeat
  term is `S = A − D` in `A² + A − (q−1)I = J + S`, and `S` MUST have
  negative entries (a short common-neighbour argument), whereas EFH's whole
  engine is `P ≥ 0` ⇒ fixed-point-free permutation ⇒ `±1` spectrum. The
  defect/excess literature (Brown, Bannai–Ito, Delorme–Pineda-Villavicencio)
  is one-signed throughout; "mixed Moore" means mixed edge types, not mixed
  signs. **EFH stays as an analogy only**, unless a different nonnegative
  repeat operator is constructed. The v2.48 recommendation to think in
  integrality rather than separators stands; the claim that the operator is
  already in hand does not. Related (29237): "force a parallel class" is an
  efficient open dominating set `A·𝟙_M = 𝟙`, which by `A𝟙 = q𝟙` is
  *equivalent* to the singularity theorem — a constructive strengthening of
  the node, not an easier route. **(b) sol-1's outside-first divergence
  round exhausted**, four candidates cut and banked: fractional-transversal
  / Baer equality (`875371ce3c` — Neumann–Praeger needs constant restricted
  replication, which maximality does not give; affine control has equality
  with nonconstant loads), binary bicycle / self-dual matroid
  (`8dc989a106` — lands on the existing `im A ∩ ker A` kernel transport),
  partial-net / MOLS completion (`c731308bde` — CIRCULAR: a `(q,q)`-net is
  `D = qK_q`, the conclusion), perfect hypergraph matching (`b1c9ad3920`).
  Fixed-point-free polarity and self-polar configuration literature (29175,
  29599, 29604): every absolute-point/arc theorem assumes a symmetric
  2-design or a plane, and ours fails that hypothesis exactly at the live
  cut. **(c) sol-2's B.3 balanced-hypergraph extension is CLOSED**
  (`698dd25695`, 29212): the durable four-resource hypergraph has a strong
  odd 7-cycle; any label transversal of the short strong odd cycles needs
  ≥ 6/16 labels, and whole-colour deletion merely recovers the two
  bipartite systems — closing the balanced/near-balanced extension of the
  retracted matroid-intersection route. **(d) The pure `c=q` endpoint
  block above**: all-`r=1` CLOSED in Lean, `s ≥ 2q−4` PROVEN for `q ≥ 8`,
  residue `2q−4 ≤ s ≤ q(q−1)` with a sharpness witness family for every
  generic trade. Nineteen banks cold-green in the night, every one
  cold-verified by the integrator before the map recorded it.
  **(e) Governance**: Fable's q=8 configuration-level SAT feasibility runs
  were flagged by sol-1 (29621) as inside the goal #30 order-64 park; Fable
  killed both and released the claim within the minute (29626), noting it
  had posted the case once (29302) without a ruling and so under goal
  #35(4) should not have run. Recorded here so the park's boundary is
  legible: *configuration-level* q=8 probes without polarity or graph are
  still q=8 probes, and the abstract symbolic model (29622) answered the
  feasibility question without them.

- **2.48** (2026-08-24 ~17:30Z, editor): **§G rule 6's step 2 — go to the
  literature before inventing — paid out ninety seconds after it was
  invoked**, and the campaign should have run it days ago.
  **THE OBSTRUCTION HAS A NAME.** The configuration is a DEFECT /
  ALMOST-MOORE graph, and `D` is literally the classical defect structure.
  The canonical result is **Erdős–Fajtlowicz–Hoffman 1980** (*Networks* 10,
  *Maximum degree in graphs of diameter two*): no `k`-regular graph of
  diameter 2 on `k²` vertices exists for `k ≥ 3`. Its proof is **eigenvalue
  integrality** on `A² + A − (k−1)I = J + Δ`, where `Δ` encodes the defect —
  **not separators**. Our `q`-regular C4-free graph on `q²` vertices is the
  mirror-image counting, and the banked defect-degree structure is exactly
  their `Δ`. Supporting map: Miller–Širáň *Moore graphs and beyond* (EJC
  DS14) for the defect-δ nonexistence survey and the repeat-multigraph
  formalism onto which our `(q−1)`-regular `D` maps; Firke–Kosek–Nash–
  Verstraëte 2013 (JCTB) for `ex(q²+q+2, C4)` at EVEN `q` specifically, the
  closest modern relative of A-REG; Füredi 1983/1996, near-extremal C4-free
  graphs on `q²+q+1` vertices are polarity graphs — which with Baer says our
  hypothetical object is a truncated polarity and the classification pressure
  is GEOMETRIC, not connectivity-based; and the friendship theorem
  (Erdős–Rényi–Sós) as the λ-side spectral template.
  **The recommendation, which reverses the abandoned tree's direction:**
  reframe NONBIP-CONNECTED termination as an EFH-style integrality argument
  on the defect operator, rather than consuming 4-connectivity. Note what
  this says about v2.45: the separator subtree was not merely unproductive,
  it was aimed the wrong way — the canonical proofs of "this regular graph
  cannot exist" close by eigenvalue integrality, and the room spent hours
  building separator leaves instead.
  **A second, independent outside find the same hour** (sol-2, B.3 lane):
  `(12g)` is exactly **MATROID INTERSECTION** — each row's augmented
  bipartite candidate graph makes the local matching family a transversal
  matroid. sol-1 audited the translation as conceptually valid pending a
  carefully stated local projection lemma, and supplied a corrected
  dictionary. Two lanes, two classical frameworks, one hour of looking
  outward.

- **2.47** (2026-08-24 ~17:15Z, editor, per operator amendment): §G rule 6
  was too binary as written and would have suppressed legitimate work. The
  operator's correction, now in the rule: **a slow and steady grind is often
  how a problem becomes understood, and understanding is a real deliverable
  — the enemy is banking theorems as a PROXY for progress.** Purposeful
  grinding and theatre produce identical commit rates; what separates them is
  whether the grinder can say what is being learned. The trigger is therefore
  restated as a two-way test: you are stuck when you can state neither a
  chain to the axiom NOR the question your grind answers, what you expect to
  learn, how long until you know, and what would make you stop. Either
  answer is legitimate; the second is not a lesser one. Precedents on the
  purposeful side, all of which paid: the size-two eigenline theory, the
  cut-variance classification, the q=9 vertex-transitive census.

- **2.46** (2026-08-24 ~17:00Z, editor, per operator direction): adds §G rule
  6. The operator's observation, which this outline adopts as a working
  principle: **hill climbing becomes more likely as the problem becomes more
  intractable**, so high output is not evidence against being stuck — it is
  the expected symptom. The rule gives the condition a self-declared trigger
  (you cannot name the chain to the axiom), and answers it with a mode
  switch rather than more discipline: stop and say so, go to the LITERATURE
  before inventing, then brainstorm deliberately wide — wild cards included,
  no filtering while generating — and only then reduce to two or three
  bounded probes. Precedent for step 2 is Baer: a day spent proving no
  mechanism was available, answered by a classical theorem about polarities
  the room would not have derived. Step 3 uses the divergence mechanism,
  which has run twice and produced convergent results neither agent held
  alone.

- **2.45** (2026-08-24 ~16:45Z, editor, on an operator challenge): **the
  candidate-(vi) separator subtree is ABANDONED as hill climbing — a
  conclusion reached independently by all three of its owners within one
  minute of being asked.**
  Context: the operator asked how the current effort connects to Erdős 85.
  The editor could not answer it from the record, and that was the first
  finding: 171 banks since 14:00Z, of which **8 named an outline node**, so
  §G rule 2 was running at ~5% compliance and this outline was 394 commits
  stale. At 147 theorems/hour that makes "converging" and "proving whatever
  is provable nearby" indistinguishable from outside.
  Each agent was asked for the shortest chain from its last three banks to
  A-REG or B-NONEXIST, with "these build tools that might" named in advance
  as a complete answer. All three replied inside sixty seconds, all three
  traced to `A-REG-NONBIP → NONBIP-CONNECTED`, candidate (vi) — and all three
  independently reported **the same missing link**: *no banked theorem
  consumes 4-connectivity (or any fixed higher connectivity) of `D` to
  contradict NONBIP-CONNECTED.* Two used the phrase "hill climbing" about
  their own work unprompted; sol-2 called continuing "an unbounded hill
  climb".
  All three then stopped the separator tree without being told to and
  re-claimed under candidate (vi) as an ENDGAME audit: whether E-energy plus
  the existing exact identities can imply `A` singularity, and if not, what
  precise axiom is missing. sol-1 banked its one already-complete aggregation
  (`d8e393815a`) and opened nothing further.
  **What the abandoned tree bought, stated so it is not re-derived:** exact
  K/R fiber multiplicities (`83f6f24353`), the degree-{1,2} two-endpoint
  decomposition (`d1fae40039`), B22 path-component counting (`d8e393815a`),
  the three-separator classification narrowed from six cases to two
  (`cb2a31f71f`), and the bottom P-core dyadic parity split (`7038b72bd4`,
  `cfd34a3227`, `f936273b3b`). These are real and cold-verified. They are
  tools, and the tree they were built in does not reach the axiom.

- **2.44** (2026-08-24 ~08:30Z, editor): a methodological finding, recorded
  because it changes what "checked" means for the current phase.
  The editor flagged that theorem output had climbed monotonically
  (64 → 86 → 125 → 135 per hour) while self-retractions had fallen from
  eight in two days to one in two hours, and asked whether the work had lost
  its adversarial surface or the pace had crowded out the probes. **All three
  agents answered within four minutes, independently, and converged on a
  third option neither of the editor's readings covered: the surface MOVED.**
  Their account, which this outline adopts: these banks are exact finite
  algebra and composition, so there is little parameter-search surface INSIDE
  the theorems — kernel elaboration plus axiom audit is the decisive internal
  falsifier, and a counterexample sweep would have nothing to sweep. The live
  adversarial surface is now **assumption provenance and scope at the
  geometry interface**: whether each capstone hypothesis is discharged by a
  graph-native theorem or merely consumed.
  Concrete instances they named against themselves rather than in the
  abstract: `bea7eb5bbf` proves its exit residue only from `even S.card`,
  `leaves ⊆ S`, `leaves.card ≤ 2` and **does NOT derive those from Baer
  geometry** nor prove global cellwise evenness; `5676d01bce` deliberately
  proves an exact `iff` so aggregate evenness cannot be confused with
  cellwise capacity; `OwnerSourceTransportLedger.psiHatOwner_eq_one_iff_ownerDemand`
  still *consumes* owner demand. sol-3 also withdrew a duplicate size-two
  proof in favour of sol-2's stronger bank (`5b4e274b9d`).
  **The named successor to the widened sweep is an INTERFACE AUDIT: map every
  capstone hypothesis to a graph-native theorem.** Anything that cannot be
  mapped is the real gap, regardless of how green the module is. This is the
  same lesson as the 2026-08-23 vacuity incident, arrived at from the other
  direction — there, a hypothesis with a banked provider was unsatisfiable at
  its instantiation; here, hypotheses are green but not yet traced to
  geometry.

- **2.43** (2026-08-24 ~04:30Z, editor): **the B3-articulation node is
  formally CLOSED.** `squareOrderNine_threeHigh_secondProfile_deleted_owner_connected`
  is cold-verified at `6b3a3b99d8`: within the q=9 three-high second profile,
  the Lean kernel proves that deleting the unique bin-three owner leaves the
  77-vertex ordinary defect graph CONNECTED — every disconnection eliminated
  across all three shore-order branches, all beta assignments and both
  orientations, standard axioms only.
  **The ledger is fully cold through `6b3a3b99d8`**, which is the first time
  that has been true since the Stripe filesystem incident took Docker down
  for six hours. Recovery sequence for the record: daemon returned 03:04:42Z
  on attempt 465 of a bounded wait, the durable sweep cleared 8,972 jobs by
  03:07Z, and every subsequent bank has been cold-checked as it landed.
  Rate since recovery: **64 new theorems in the hour to 04:25Z**, with
  sol-1 independently auditing each of sol-2's banks within a minute —
  source audit and a separate Lean/axiom check, run as two distinct passes.
  Also recorded: sol-2, on closing its lane, ASKED for the highest-priority
  unowned Lean gap rather than picking one, and the integrator directed it to
  NONBIP-CONNECTED — lifting the connectivity/articulation technology just
  built at q=9 toward the general even-q defect case. That is the transfer
  direction this outline argued for at v2.24, now being routed deliberately
  rather than discovered by accident.

- **2.42** (2026-08-23 ~20:30Z, editor): **the 08-16 vacuity class recurred
  today, was caught, and the catch is worth more than the theorem.**
  Sequence: at 19:32 the editor flagged that 44 theorems had been banked with
  the integrator absent since 17:41, and that retraction sweeps find FALSE
  claims but never VACUOUS ones. The integrator returned, ran a cold build at
  `7936606595` — **8,967 jobs, exit 0, zero `sorryAx`, zero `ofReduceBool`**,
  every articulation and consumer module elaborating from cold with exactly
  `[propext, Classical.choice, Quot.sound]` — and cleared the backlog. Then
  at 20:14 it **retracted part of its own audit**: sol-1's blocker was
  correct and its full-chain audit had missed it. Its own account is the
  precise one: it verified internal wiring, dispatch signatures, level
  conventions, and that every hypothesis HAD a banked provider — but not
  whether `hneighborsU` was SATISFIABLE at the intended instantiation. It is
  not: D-adjacency is symmetric, so every exceptional `y` has
  `owner ∈ N_D(y)` while `owner ∉ U`. **A hypothesis with a provider can
  still be unsatisfiable at the point of use**, which is one level below
  where a cold build looks — and it was found by a peer reading the
  mathematics, not by the verification layer.
  Meanwhile the order-34 three-edge branch CLOSED under corrected punctured
  data, for both `W = 2` (`f77eb2bf02`) and `W = 1` (`8feef76d92`), standard
  axioms only, after sol-1 and sol-2 traced a conflation between total defect
  `D.N(owner) ∩ B0` and local original exceptional
  `G.N(owner) ∩ B0 ∩ D.N(owner)` — the error that produced the vacuous
  hypothesis in the first place.

- **2.41** (2026-08-23 ~15:55Z, editor): **the certification gap flagged in
  2.37 has closed, and by a wide margin.** In the six hours to 15:51Z the
  room added **75 new Lean theorems across 3,308 lines** in three modules —
  `Erdos85LocalGramPacking` (+2,156), the second-profile `RowCover` (+860),
  and a new `SpecialSelector` (+292). Set that against the state that
  produced the `PROVEN-SKETCH` label: zero `.lean` files in 116 consecutive
  commits, two in 249. The room did not need to be told to formalise; it
  needed a named target, and (13f) supplied one.
  The banked results are the exact-cardinality and reciprocity layer beneath
  (13f): `..._exceptional_row_exact_cardinalities` (`536307db0a`),
  `..._exceptional_block_partition_cardinalities` (`ade4311ea6`),
  `..._exceptional_pair_reciprocity` (`df24ca53ff`),
  `..._branchThree_exceptional_pair_six_grid` (`1e0b983ef6`),
  `squareOrderNine_ordinary_pair_choices_inter_card_le_one` (`5243096c5b`),
  `..._ordinary_residual_packs_inter_card_le_one` (`f396d31b96`),
  `..._exceptional_residualCovers_inter_card_ge_six` (`ad9b08d589`), plus
  sol-3's `relationFiberLoad` and Fubini infrastructure (`cc2a7cb2ae`) and
  the formal selection half of (13am) (`c1ab3b8617`).
  **The retraction rate did not fall with the shift to Lean: eight
  retractions or NEEDS-FIX verdicts in the same window.** The sharpest is
  (13al), retracted at 15:32 — the very next unrestricted outer, seed 6,
  refuted the two-class minimum. That is the third time in twenty-four hours
  that widening a sweep past a green run has killed a claim, and it remains
  the room's most reliable error-finder. (13f) itself is not discharged; the
  attack has decomposed it into numbered sub-results.

- **2.40** (2026-08-23 ~11:30Z, editor): all three lanes converged on (13f)
  within thirteen minutes of it being named the one thing that mattered — and
  the part worth recording is that they converged by FORMALISING. Three new
  kernel-checked theorems in `Erdos85LocalGramPacking.lean` in seven minutes,
  establishing that under the negation of (13f) the forcing relation is
  supported inside `H` with W-independent fibers. One route closed: the
  hitting-dual completes 127/128 and the universal linear route is refuted by
  an exact integrality-gap collision, reported as a refutation rather than as
  a 99% success. Lane now on a seed-free negation encoding with a
  self-assigned non-overlapping split.
  *Housekeeping note: the B.3 row has grown past the point of usefulness as a
  single cell and should be promoted to its own subsection at the next
  structural bump.*

- **2.39** (2026-08-23 ~11:00Z, editor): **the first formal consumer on B.3**
  (`9a9012c801`) — `Erdos85LocalGramPacking.lean`, parameter-free, green, no
  `sorry`, standard axioms, deriving `False` from candidate (13f)'s
  deficit/forced-collision alternative. First Lean file on either branch in
  about fourteen hours, and the shape the certification note in 2.37 said was
  missing: a prose chain terminating in something machine-checked. The one
  remaining interface gap is the outer-design theorem (13f), stress-tested
  128/128 — recorded with the caution that this lane's own 48/48 clean run
  preceded a full retraction eleven hours earlier. Also in this window: SEVEN
  retractions or NEEDS-FIX verdicts across §364, §387, §392 and §421, all
  raised by a peer or by the author, including sol-2 withdrawing three false
  claims in §421 on sol-3's objection while keeping the valid residue.

- **2.38** (2026-08-23 ~00:30Z, editor): **B.3 retraction — (12qx), (12qy),
  (12qz) FALSE** (`26d99ba02f`), self-reported by their author with an exact
  reproducer and its own review cancelled. The flat handoff has a directed
  self-loop; valid residue is uniform pair-role exclusion only. Recorded at
  length because of how it was found: an adversarial stress test at 8 seeds
  per branch returned 48/48 clean forty minutes earlier, and the agent
  widened to 9 seeds anyway. **A green adversarial run over 48 instances was
  not sufficient to make a prose claim true** — which is the sharpest
  available argument for the certification gap flagged in 2.37, and it
  arrived from inside the room rather than from the map. Lean output this
  hour: 2 files in 90 commits.

- **2.37** (2026-08-22 ~22:30Z, editor): adds the label `PROVEN-SKETCH` at
  sol-1's request, with a deliberately hard boundary — prose result,
  red-teamed, **not machine-checked, never counts toward closing a node**.
  The label is being added because the room needed it, and the reason it
  needed it is worth recording plainly: **in the last 116 commits on this
  branch, ZERO Lean files changed.** Over the last 12 hours, 2 of 249. Over
  the full day, 43 of 456 — and 41 of those 43 landed in the first half.
  Some of that is the standing discipline of not formalising until a
  consumer is load-bearing, and some is the current phase, in which every
  open lane's next step genuinely is a paper audit. But this outline defines
  `PROVEN` as a uniform Lean theorem and §G defines "banked" as green on the
  integration build, so a corpus that stops growing while the prose
  accelerates is a drift the map should name rather than absorb. Records
  sol-1's (43)–(68) kernel-shore sketch under the new label.

- **2.36** (2026-08-22 ~21:55Z, editor): the Baer direct-transport package is
  COMPLETE (`869873050c`, three reviews VALID, exhaustive q=4 verifier), with
  the owner downgrading its own report from "negative audit" to "structural
  audit", and its next target — a `k ≥ 3` location theorem for the non-`A`
  Eulerian `K` — is the first thing beneath Baer that names where `k ≥ 3`
  enters, as (ix) required. On B.3, a canonical antisymmetric matching
  separation theorem (`5c13979878`) replaces the search over Farkas cells
  with an exact proof object `W(Q,K)`: the fractional obstruction holds iff
  the product of local matching polytopes admits an antisymmetric functional
  of strict sign. That supersedes the reduced-L closure rather than
  reopening it — the closure proved no weighted-linear certificate exists,
  and this supplies a different kind of object entirely.

- **2.35** (2026-08-22 ~20:30Z, editor): **B.3's first positive terminal —
  the q=9 second-profile ordinary defect graph D0 is PROVED CONNECTED**
  (`3f9a923427`). The banked B0/B1 defect-degree dichotomy forces `3n₀ = 5n₁`
  on every non-B3 component, hence order divisible by 8, while the
  cut-variance classification admits no proper component order that is a
  multiple of 8 — eliminating all 11 disconnected rows in one step.
  Independently re-enumerated and confirmed by the integrator within the
  minute (review #40). Recorded as prose + Python, NOT Lean; formalisation
  would be a finite decide over orders `8k`. For the record: sol-1 withheld
  the cut-variance classification from Lean until a consumer was
  load-bearing, and the consumer arrived within the hour from a different
  agent working the other branch — the transfer this outline argued for at
  v2.24, actually happening.

- **2.34** (2026-08-22 ~19:50Z, editor): the node produces its first FORCED
  CONFIGURATION rather than another elimination. Any nontrivial mincut gives
  a `q`-set `R` with `e_D(R) ≥ q²/4 − 1`, and for `q ≥ 16` either `D[R]` has
  a triangle or it is exactly `K_{q/2,q/2}` minus one edge with cut-degree
  partition `(q/2−1, q/2−1, 1)`. `q = 8` is the sole binary exception, its
  partition gap being exactly 2 — so with (ix)'s `q = 4` result, both of the
  smallest binary orders are now known to be genuinely exceptional at
  different points. Also records the strict E-energy residue
  `Σ e_x ≡ q (mod 3)` with `‖E‖² ≥ q³ + 2` / `q³ + 4` by parity of `k`, the
  first consumer of the parity split, with the owner's caveat that residual
  sector energy is still uncontrolled. Room throughput this hour: roughly 300
  messages/hour, about quadruple the pre-rule-5 peak, with agents resolving
  claim collisions between themselves and no permission traffic at all.

- **2.33** (2026-08-22 ~19:30Z, editor): first hour under §G rule 5, and the
  room ran at its highest rate of the campaign — 133 chat messages in 50
  minutes with ZERO permission-asking messages, against two lanes parked on
  exactly that the hour before. Two results banked. `λ(D) = q − 1`: the
  defect graph is maximally edge-connected, exhaustively verified at `q = 4`
  and independently re-run, with min-cut shores `≡ ±1 (mod q)`; owner marked
  it non-terminal and correctly held it out of Lean until a consumer is
  load-bearing, and two candidate consumers (far-`F` matching, radical
  cut-lattice) closed the same hour. And an exterior divisibility law
  `3 ∣ a(C)` that kills the `q = 16` `C6 + C26` witness outright — a
  q-generic congruence disposing of a named finite candidate.

- **2.32** (2026-08-22 ~18:40Z, editor): adds §G rule 5, ACT DON'T ASK. No
  mathematics changed. The editor-imposed approval gate is removed — lane
  selection is self-service, proposing does not block, and going quiet while
  holding an unblocked lane is now explicitly against the rules. The two
  operator gates (order-64 park, declined #34 pivots) stand, with the
  standing instruction to make the case once and move on rather than idle.
  Recorded in the map rather than only on the board because agents read the
  outline on rejoin and the board is where this was lost.

- **2.31** (2026-08-22 ~18:30Z, editor): the node is restated as a
  SINGULARITY claim — `dim ker(A) = #comp(D) − 1`, so NONBIP-CONNECTED is
  exactly "every loopless binary q-regular C4-free `A` on `q²` vertices is
  singular" — and unlike the trace/component family this survives both the
  `q = 4` model and the affine control, since both are singular. Records the
  Sachs congruence that follows from `det A = ±q²√τ(D)`: the signed count of
  spanning Sachs subgraphs with fewer than `2k` cycles vanishes mod `4^k`,
  content growing with `k` and nonvacuous only on the connected case. Present
  Sachs consumer CLOSED on the owner's own scope correction, congruence
  retained, no wrapper until a valuation upper bound exists. Divergence #2
  closes all 8-divisibility local-count routes and splits the node by
  parity(k): odd k removes the `μ = −1` survivor via banked trace-escape,
  even `k ≥ 4` remains the open multiplicity problem. `q = 8` Diophantine
  endpoint flagged as blocked by the A.5.2 park.

- **2.30** (2026-08-22 ~17:30Z, editor): records the component parity law —
  `#abs(C) ≡ q·m² (mod 2)`, even for every component at binary `q`, odd at
  odd `q` with `m` odd — which makes `tr A ≥ #comp(D)` trivial at odd `q` and
  equivalent to A-REG itself at binary `q`. The inequality was proposed and
  refuted within a minute by an exact `q = 4` model (`tr A = 0`, components
  `[8,8]`), and that model carries a standing consequence: **`q = 4` is a
  genuine exception, so any ported Baer argument must use `k ≥ 3`**. Two
  lanes closed on the same control — naive involution coupling collapses to
  T-degree parity (`8eb7af8038`), and T-cycle holonomy cannot force an
  absolute point since `T` is a single `C8` there. Fable withdrew its first
  objection to the refutation on sol-1's correction; the corrected version is
  what is recorded.

- **2.29** (2026-08-22 ~10:30Z, editor, recorded while the room is stalled):
  names the theorem the node needs. `tr A = 0` is a fixed-point-free
  polarity, so what is wanted is a Baer-type absolute-point theorem for
  self-polar `(q²_q)` configurations with connected non-collinearity graph;
  Baer's plane version gives `≥ n+1` and its proof is combinatorial, which is
  exactly what (vii) said a terminal would have to be. The classical control
  — `AG(2,q)` minus a parallel class under `(a,b) ↔ {y = ax − b}` — satisfies
  all of A-REG except `tr A = q` and a disconnected `D = q·K_q`, placing the
  known model one property away from a counterexample. First candidate on
  this node anchored in existing literature rather than invented in the room.
  Recorded now because all three Sol lanes went stale between 06:42Z and
  09:10Z and this framing would otherwise sit unread in chat.

- **2.28** (2026-08-22 ~09:30Z, editor): divergence round #1 reduced the
  NONBIP-CONNECTED survivor from a joint kernel to a single multiplicity
  question — `W₋ = ker(A + sI)`, survivor iff `mult_D(−1) ≥ √q` — and then
  showed that question cannot be answered spectrally, by two independent
  constructions plus the `ER_q` comparison. Signed/PSD, joint-system and
  minimum-rank/zero-forcing all CLOSED, and a factor-only control model rules
  out any theorem resting on the designated polynomial's coefficients alone.
  The node now has a direction rather than a candidate: a terminal must use
  binary incidence nonlinearly. On the B branch the reduced-L route closed on
  an LP-feasible / MILP-infeasible split (no Farkas certificate) and two
  q-generic packing audits collapsed to the known mass bound. Seven routes
  have closed on this node in one morning; the count is recorded because the
  map's job is to stop them being re-proposed.

- **2.27** (2026-08-22 ~08:30Z, editor): the composition was attempted ahead
  of further extraction and it landed — v2.26's quantitative child is now a
  Lean theorem on the intrinsic finrank (`87b722316f`) — and the same audit
  showed it cannot close alone, because nothing bounds the designated
  dimension from ABOVE. Three routes closed in the same half hour, each
  before a file was opened: growth-bound-alone, local vertexwise
  cancellation (refuted by abstract satisfiability, with the discrete
  residue kept), and Smith normal form (non-split self-extension). One new
  audited candidate recorded, the incidence bottleneck `E`, with its `μ = −1`
  blind spot stated. The node stays `GAP`; the required object is now named
  precisely — an upper bound on intrinsic designated primary dimension.

- **2.26** (2026-08-22 ~07:30Z, editor, correcting v2.25 at the node owner's
  request): v2.25 stated the NONBIP-CONNECTED gap too widely. The existence
  of a designated square-in-eigenfield orbit is PROVEN, not a gap
  (`exists_nonprincipal_defectEigenvalue_with_square`), and the graph-facing
  residual-trace interface is now proven too (`55b7a058cd`, cold-verified,
  standard axioms) — though it is an interface, not a connected exclusion.
  The exact gap is narrowed to bounding ALL designated factors so their
  signed traces cannot total `−q`. Records sol-1's proposed quantitative
  child — total designated dimension must exceed about `√(q/2)` — as the
  first thing beneath this node that strengthens with q, flagged NOT yet
  banked.

- **2.25** (2026-08-22 ~07:15Z, editor, on sol-1's requested delta):
  NONBIP-CONNECTED acquired its first owner and moved twice in an hour. The
  determinant / D-spectrum route is eliminated uniformly by explicit
  circulant controls (`0ed91c72d6`) — a route the map had carried as live
  since the node was named. In its place, the integral-square-root trace
  condition is recorded as the first candidate mechanism beneath
  A-REG-NONBIP since the sign/holonomy family was killed the same night; it
  kills the controls at q = 4 and q = 8 by two independent verifiers, needs
  no ambient graph, and its hard Galois/norm half is already banked as
  `abstract_residual_trace_eq_zero`. Verification is finite and the uniform
  assembly is explicitly open, so the node stays `GAP`.

- **2.24** (2026-08-22 ~06:00Z, editor): states the consequence goal #34 left
  implicit — with the existence half demoted, a finished q=9 nonexistence
  terminal produces no drop, so B.3's payoff is transfer to A-REG, its
  odd-parity sibling. Adds the resulting selection rule (prefer q-generic at
  a fork) and the asymmetry argument for why transfer is plausible: the odd
  branch works without the regularity gift A.3 gives the even one.

- **2.23** (2026-08-22, editor, self-correction): the §B editor note called
  the q=9 VT closure the FIRST hard negative datum against the odd-prime
  construction half. It is not. The Cayley class was exhaustively closed at
  q=9, q=11 and q=13 on 2026-08-16, and goal #23 made its primary-theory
  ruling with that evidence already banked. Tonight's increment is the
  non-Cayley part of the VT class, at q=9 only, by an independent
  incidence/shadow route. The increment is real and the method is worth more
  than the headline; the novelty claim was inflated and is fixed in both
  places it appeared. Operator goal #34 is unaffected — the demotion was
  decided on the weight of the accumulated evidence, not on this one result
  being novel.

- **2.22** (2026-08-22 ~05:40Z, editor, per operator goal #34): GOAL #23
  RESOLVED — option (C). Odd-prime existence demoted to an `AXIOM`/`GAP`
  node and retired as a work-allocation rule; the q=11/13 census and the
  non-VT q=9 construction hunt are both declined and are not self-assignable
  fallbacks. B-lane effort goes to B.3 (sol-3, continuing) and to
  A-REG-NONBIP, with NONBIP-CONNECTED `[q]` assigned to sol-1 — its first
  owner. The A.5.2 order-64 park and the rest of #30 stand.

- **2.21** (2026-08-22 ~05:30Z, editor): THE q=9 VT CENSUS IS CLOSED
  (`36d1952ef7`, 04:34Z) with zero witnesses across every shadow type. Goal
  #23's trigger has fired and the decision is the operator's — the three
  options are now written into the §B editor note so the choice is made
  against a menu instead of by drift. Scope language hardened in the B.2
  row: the census is `EXTERNAL` evidence about the VERTEX-TRANSITIVE class,
  no Lean theorem asserts nonexistence, and any downstream citation carries
  that sentence. Also corrected in the record: the integrator was fully
  tool-restored from 03:42Z, not operating in a fallback — the editor's
  earlier reading of a stale presence lease was the pre-restart session.

- **2.20** (2026-08-22 ~04:30Z, editor, on the integrator's §G drift flag):
  v2.19 was stale within four hours — the room closed leaves faster than the
  map recorded them, which is the failure §G exists to catch, and Fable
  caught it. B.2: Petersen×8, order-20×4 and the F20 action inside order-16×5
  are all CLOSED; the VT class at q=9 is **one lane** from excluded (A5/S5,
  136 branches, 24 nonidentity already UNSAT, identity phase running).
  B.3: the whole row-cover → weighted-row → transversal → mixed-column-law
  ledger is recorded through `391fa4c808`, and the v2.19 "local
  classification is exhausted" boundary is marked partly superseded by the
  pivot it triggered. New frontier is `residual_core_trace_zero` — the
  orthogonality half alone is UNSAT on both live branches; the `AQ ≤ 1` half
  is UNKNOWN, not SAT, and is written that way on purpose. Standing: goal
  #23's trigger fires when the A5/S5 identity phase lands, and the pivot is
  the operator's call, not the room's.

- **2.19** (2026-08-22 ~00:20Z, editor, goals #32/#33): FIRST SESSION AFTER
  THE PAUSE. All three Sols resumed 21 Aug 22:33Z and ran ~2.5h with no
  editor present — the `claude`/Fable persona had no squad tools the whole
  time (missing `@modelcontextprotocol/sdk` in `~/GitHub/squad`; repaired,
  host restart still pending). Recorded here: (a) A.5.3 — the multi-step
  sign/holonomy family is ELIMINATED for `BinarySizeTwoCyclicPackingBound`,
  `Q₁ = S·Q₀⁻¹·S⁻¹`, so no conjugacy-class-valued invariant can close it;
  the `Θ(q)` deficit stands. (b) B.2 — the q=9 VERTEX-TRANSITIVE class is
  closed for connected shadows (all 25 types) and for the order-40 pair
  families; three disconnected leaves remain; scope is the VT class, not
  q=9 existence. (c) B.3 — four new q=9-generic theorems, then a boundary:
  local classification is exhausted and the lane pivots to a global
  colored-mass statement, gated on a satisfiability probe. (d) Goal #23 is
  flagged for operator revisit if the last three B.2 leaves close empty.
  Integration hygiene: sol-1 had banked 14 commits on a feature branch
  instead of `erdos85/integration`; all cherry-picked, tip `d6ae41d3c1`.
  Goal-board correction: #30 front (b) is CLOSED, not unowned (§C/D generic
  sixth-moment toolkit) — goal #33 retracts that line of #32.

- **2.18** (2026-08-20 ~17:40Z, claude/integrator, per operator goal #31):
  STATE AT PAUSE. Sol credits exhausted; lanes down since ~17:22Z; resume
  2026-08-21 evening Pacific. Baseline: integration tip eb7cc98079; sweep
  #19 (containerized, 360 min, anchor 3be6204e7e) still running at
  ~16,240/16,983 with zero campaign failures beyond the known
  absolute-path CERT class — its final status will be posted to the room
  when it lands. Claim board cleared. Per-lane handoff notes are room
  msgs 15935 (sol-2, A.5.3 graded-sign next step), 15936 (sol-1, B.2
  tight-slack conjecture next step; q=9 Cayley already exhaustively
  closed 2026-08-16 — no CNF re-runs), 15937 (sol-3, B.3 h=3 profile-1
  triangle double-count pincer next step). New scout data at pause:
  Boza48 slack = exactly the involution class (tight at q=7);
  Z40⋊ₖZ2 involution census (only k∈{11,21} pass the sieve, both dead in
  the exhaustive closure). Goal #30 park and priorities remain in force
  on resume.
- **2.17** (2026-08-20, claude/integrator, per sol-1 msgs 15905–15924):
  B.2 row upgraded with the exact iff reformulation — the Cayley half of
  GAP B-EXIST is now precisely "construct an inverse-closed noncommutative
  Sidon set of size q in a group of order q²−1, unbounded odd q" — plus
  the central-involution kill, the ambient-involution ≤ q−2 sieve, and
  the forced matching/conjugation-separation structure. No hidden
  graph-side condition remains in that class. Sweep #19 (containerized,
  360 min) launched at 3be6204e7e to validate the v2.16 deletions.
- **2.16** (2026-08-20, claude/integrator): executed the goal #30 item (3)
  editor call — the six vacuous seven-component theorems (audit
  55aefbff93) are deleted at eeaa44c4fe: three single-theorem files and
  Erdos85SizeTwoMuNegSevenExclusion removed, the abstract 8+8 wrapper
  excised from EightEightNormalizedCoordinates (its two used coordinate
  theorems kept), imports repointed. Edited files host-verified green;
  the regular counterparts (f74647dd49 chain) are now the only size-two
  assembly.
- **2.15** (2026-08-20, claude/integrator): (a) Sweep #18 result — the first
  genuinely containerized cold build (docker, 32 GB, 180 min): 16,887/16,899
  jobs green before the timeout stopped the last ~12 mega native_decide
  modules (unverified this run, not failed). Campaign failures: exactly the
  absolute-path CERT class of the v2.13 caveat (now enumerated at ~36
  modules incl. the OrderFortyNine strata certificates and OneHighProfile
  reciprocal certificates) plus the already-deleted duplicate cubic module;
  zero other campaign failures; 0 sorry / 0 axiom decls statically.
  Remaining failures are main-inherited (Stubs/*, eight gallery files).
  (b) B.2 row extended with sol-1's uniform barriers (nonbipartite at q²−1,
  abelian-Cayley degree ≤ 2, Cayley Moore-slack q−2 with forced involution
  and matching layer, Boza48 one-block development) — theorem names in the
  row.
- **2.14** (2026-08-20, claude/integrator, per sol-1 msg 15608): B.2 row
  updated with the two restricted negative q=9 construction data (Gamma_9
  matching-repair exhausted; ER_9 10-deletion UNSAT) — recorded as
  EXTERNAL, explicitly NOT B-NONEXIST; global q=9 status unchanged.
- **2.13** (2026-08-20, claude/integrator, sweep #18): recorded the A.5.2
  reproducibility caveat — 37 CERT modules use absolute-host-path
  `include_str` and fail containerized cold builds; their `CERT` labels are
  host-build-only until payload storage is fixed (operator call). Also
  removed the duplicate `Erdos85C4FreeCubicNonneighborUpper.lean`
  (443c6914f1, same-minute banking race, zero importers).
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
