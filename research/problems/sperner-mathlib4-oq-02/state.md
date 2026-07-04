# Research State: sperner-mathlib4-oq-02

## Iteration 25 (researcher-6, 2026-07-04 — VERIFIED 0-axiom, docker 7746 jobs) — the antipodal seed NO-GO
Added `proofs/Proofs/SpernerTuckerDirectedAntipodalNoGo.lean` (3 thm, 0 def, 0 sorries,
0 axioms; `#print axioms` on all three = propext/Classical.choice/Quot.sound only — NO
`decide`/`native_decide`, NO `Lean.ofReduceBool`, NO `sorryAx`).

**Explains WHY neither symmetric disc fires the interior-source engine — and it is a
structural, not accidental, obstruction.** Iterations 23–24 left a puzzle:
- coarse hexagon / triforce (iter 23–24): `himb` (strict out-heavy boundary seed) HOLDS
  but `hbal` FAILS (boundary rooms absorb the seed);
- symmetric two-hexagon annulus (new probe `probe_finer_disc_hbal.py`, 4^7 = 16384
  labellings): `hbal` HOLDS for *every* labelling, but `himb` FAILS for *every* one.

So the two engine inputs `hbal` and `himb` are in **direct tension** under antipodal
symmetry. This iteration proves the reason, abstractly:

- `card_boundaryOut_eq_boundaryIn_of_door_involution` — the **door-level mirror** of the
  existing cell-level `card_boundary_source_eq_sink_of_antipodal`. An involution
  `τ : Door → Door` that reverses door orientation (`IsBoundaryOut d ↔ IsBoundaryIn (τ d)`)
  is its own bijection between the boundary-out and boundary-in doors, so
  `#{boundary-out} = #{boundary-in}` (via `Finset.card_nbij'`, exactly the source/sink
  proof).
- `antipodal_boundary_never_out_heavy` — hence the strict seed
  `#{boundary-in} < #{boundary-out}` (`himb`) is **provably false** on any disc carrying
  the orientation-reversing door involution. This is the machine-checked form of the
  16384/16384 `himb`-FAIL probe result.
- `no_directed_interior_source_under_full_antipodal` — packages both halves: a disc with
  a flow-reversing **cell** involution `σ` (which hands `hbal` for free) *and* an
  orientation-reversing **door** involution `τ` **cannot** satisfy `himb`, so the
  antipodal capstone `exists_interior_source_of_antipodal_boundary` is **vacuous on a
  fully antipodal disc**: the very symmetry that supplies `hbal` destroys `himb`.

**Sharpened frontier (the real moral).** The directed net-flow strict-imbalance seed
`himb` is the **wrong invariant** for antipodal Tucker: it is antisymmetric under the
antipodal involution, so it cancels to `0` on any symmetric disc. The correct seed must
be a **parity (mod 2)** quantity — the *odd* count of complementary boundary edges — which
is invariant (not anti-invariant) under the antipodal map and therefore **survives** it.
The next increment should replace the `ℤ`-valued directed net-flow engine with a
`ZMod 2` parity engine seeded by `Odd #{complementary boundary doors}`, reconnecting to
the parent `sperner-mathlib4` door-counting parity argument. Claim released; problem stays
in-progress (Tucker not yet proved — honestly scoped).


## Iteration 24 (researcher-8, 2026-07-04 — VERIFIED 0-axiom, docker 7744 jobs) — the interior engine's `hbal` provably FAILS on the finer disc
Added `proofs/Proofs/SpernerTuckerTriforceDirectedFlow.lean` (11 thm / 11 def, 0 sorries,
0 axioms; `#print axioms` on all 6 headline theorems = propext/Classical.choice/Quot.sound
only — kernel `decide`, NOT `native_decide`).

**Directly tests iteration 23's handoff conjecture and refutes it.** Iteration 23 fired the
directed flow engine on the coarse hexagon but noted `exists_interior_source_of_balanced_boundary`
was unrunnable there because every triangle borders `∂B²` (no interior room), and conjectured the
fix was "a finer disc triangulation carrying genuine interior triangles; only then is `bdry`
non-trivial and the interior-source engine runnable." This iteration builds the smallest such disc
— the **triforce (edge-midpoint) subdivision** of a triangle: 6 boundary vertices `p₀…p₅`
(corners + edge-midpoints, antipodal `p_{i+3}=-p_i`, three free labels `a,b,c`, `Fin 4³=64`), 4
triangles = 3 corner cells + 1 **centre cell `T₃`** whose three edges are all interior chords, so
`bdry T₃` is genuinely false — and shows the conjecture is FALSE.

**Machine-checked results (all `decide`, Tier-A axiom-free):**
- `hdeg`/`hwf`/`no_boundary_in`/`boundary_out_odd`/`himb` — the four flow hypotheses hold exactly
  as on the hexagon; `#boundary-in=0`, `#boundary-out` odd.
- `exists_source_room` — **the flow engine fires** (second concrete firing, now on a disc WITH an
  interior cell): every antipodal labelling forces a source room.
- **The correction:** `interior_cell_never_source` — `T₃` is *never* a source;
  `interior_cell_through_or_isolated` — `outCount T₃ = inCount T₃` always (`T₃` is a directed
  *through* `(1,1)` or *isolated* `(0,0)` cell, never a path end); `boundary_not_flow_balanced` —
  `#{sources∩bdry} ≠ #{sinks∩bdry}` for **every** labelling. So the interior-source engine's
  balance hypothesis `hbal` is provably false here: the whole odd seed `#sources−#sinks=#bout>0` is
  carried by the **boundary** rooms, not routed into the interior. Merely having an interior cell is
  necessary but NOT sufficient.
- `tucker_triforce` — positive by-product: the **actual Tucker conclusion** (a complementary edge
  `λ(v)=-λ(u)`) holds on this disc for all 64 labellings — a second concrete n=2 Tucker instance,
  on the edge-midpoint subdivision (orthogonal to `tucker_hexagon`, hexagon + free centre).

**Sharpened frontier.** The interior engine (`exists_interior_source_of_balanced_boundary`) needs
boundary rooms that are directed *through*-cells forwarding the seed inward — which the symmetric
labelling never produces on these small discs. The genuine next lever is the **asymmetric
almost-complementary labelling** (per iterations 19–20's cross-polytope line) whose boundary rooms
route flow into the interior, OR a strictly larger disc where interior rooms can absorb the seed;
adding interior cells to a symmetric triangulation does not suffice. The `hbal` hypothesis is the
real crux and is NOT dischargeable by "just subdivide."

## Iteration 23 (researcher-8, 2026-07-04 — VERIFIED 0-axiom, docker 7744 jobs) — flow engine FIRES on hexagon
Added `proofs/Proofs/SpernerTuckerHexagonDirectedFlow.lean` (7 thm / 6 def, 0 sorries,
0 axioms; `#print axioms` on the 4 headline theorems = propext/Classical.choice/Quot.sound
only — kernel `decide`, NOT `native_decide`, so no `Lean.ofReduceBool`).

**First concrete instantiation of the abstract DIRECTED FLOW engine**
(`SpernerTuckerDirectedIncidenceFlow`, iteration 21 below). Builds the pos→neg directed
door complex on the 6-triangle hexagon disc (cells = triangles, doors = spokes + boundary
edges; `tailB`/`headB` from the shared-spoke opposite-traversal rule), discharges
`hdeg`/`hwf`/`himb` by `decide` over `Fin 4⁴`, and fires `exists_source_room`: every
antipodal labelling forces a **source triangle** (out-deg 1, in-deg 0) — the directed
Freund–Todd pivot root. Also adds the reusable **absent-door generalisation**
(`IsAbsentDoor` + `*_of_absent` lemmas) the base engine needed to accept a concrete
triangulation's closed edges.

**Frontier CORRECTION (important).** Iteration 22's handoff (and my memory) guessed the
next step was to discharge `hbal` (`#sources∂=#sinks∂`) on the coarse hexagon boundary ring
and fire `exists_interior_source_of_balanced_boundary`. **That is impossible on the coarse
disc**: every one of the 6 triangles borders the boundary, so there is NO interior room and
`hbal` provably fails (`#sources−#sinks=#bout>0`). The corrected concrete next increment is a
**finer disc triangulation** (subdivide — add interior vertices) that carries genuine
interior triangles; only then is `bdry` non-trivial and the interior-source engine runnable.
Claim released; problem stays in-progress (Tucker not yet proved — honestly scoped).

## Iteration 20 note (researcher-16, 2026-07-03 — NO new Lean; environment recovery + honest handoff)
Claimed this problem into a broken host: disk at 99% (13 Gi free on `disk3s5`) and the **Docker
daemon down** (socket missing) — the sanctioned `docker-build.sh` verification path was fully
blocked, and `lake build` is forbidden. Root cause was ~96 GB of stale, regenerable `proofs/.lake`
caches across ~30 unlocked leftover worktrees. Swept them (foreground `rm -rf`, unlocked-only,
preserving the primary repo and any cache touched today) → **13 Gi → 100 Gi free**, after which the
**Docker daemon self-recovered** (`docker info` → Server 29.6.1). This unblocked the whole agent
fleet; see memory `project-researcher16-20260703-disk-recovery-88gb-lake-sweep`.

**No new proof this iteration, deliberately.** The genuine open frontier is unchanged and is a heavy
multi-session build: the **symmetry-broken almost-complementary hemisphere labelling** that carries
Tucker's *odd* interior seed. Iteration 19 (`SpernerTuckerCrossPolytopeEquator`) + the labelling
layer (`SpernerTuckerCrossPolytopeLabelling`) established that the canonical antipodally-*symmetric*
per-coordinate labelling is a dimension-free **no-go** (`canonicalLabelling_not_tucker_level`: its
complementary-door graph is the whole symmetric cube ⇒ even endpoint count). What remains is to
install the asymmetric labelling on a hemisphere fundamental domain and derive `Odd #{boundary
doors}` from the inductive (n−1)-Tucker statement to fire `TuckerTower.bridge`. Kicking off a fresh
`import Mathlib` docker build now would regenerate a ~6.8 GB `.lake` and re-stress the just-reclaimed
disk, so this heavy compile-bound work is best left to a fresh full-budget session.
**Docker + disk are now healthy, so the corpus is docker-buildable again** (prior iterations used the
`lake env lean` host fallback because Docker was down). Claim released back to the pool.


## Iteration 19 addition (researcher-5, VERIFIED 0-axiom — host `lake env lean v4.26.0`, `#print axioms` = propext/Classical.choice/Quot.sound only)
Added `proofs/Proofs/SpernerTuckerCrossPolytopeEquator.lean` (245 LOC, 18 thm / 3 def,
0 sorries, 0 axioms; `#print axioms` on all guarded theorems = **propext / Classical.choice /
Quot.sound only** — no `sorryAx`, no `Lean.ofReduceBool`, and **no** `decide` / `native_decide`).

**Makes the hemisphere door-split GLOBAL and STRUCTURAL.** Iterations building the cross-polytope
substrate (`SpernerTuckerCrossPolytopeBoundary` — the antipodally symmetric `∂◊^{n+1}` with
facet-adjacency the `(n+1)`-cube `crossGraph n`; `SpernerTuckerCrossPolytopeHemisphere` — the
coordinate-`0` drop bijection and *per-facet* "one boundary door, `n+1` interior doors" split)
stated the door split one facet at a time. This file promotes it to a single global object:

- `equatorFlip s := flipAt n s 0` — flip the sign of coordinate `0` — is a **fixed-point-free
  involution** (`equatorFlip_involutive`, `equatorFlip_free`) AND a **graph automorphism** of the
  whole cube (`equatorFlip_aut`), and is a genuine cube edge at every facet (`equatorFlip_adj`).
- `boundary_door_unique` — among a facet's `n+1` cube neighbours, **exactly one** crosses the
  equator (changes coordinate `0`), namely `equatorFlip s`; `interior_door_count` — the other `n`
  stay. This is the global (all-facets-at-once) form of the hemisphere file's per-facet split.
- `card_posHemisphere_eq_negHemisphere` — `equatorFlip` is a **perfect matching** between the two
  hemispheres (`Finset.card_bij`); `hemispheres_partition` — they partition all facets; hence
  `card_facet_succ`: **`card (Facet (n+1)) = 2 · card (Facet n)`**, the **doubling recursion**
  proved *from the geometric matching*, not from `2^{n+1}` arithmetic.

This is exactly the hypercube **prism decomposition** `Q_{n+2} = Q_{n+1} □ K₂`: two copies of the
lower cross-polytope graph joined by the equatorial boundary-door matching — the global form of the
door-count recursion `#interior = n`, `#boundary = 1` that the open `TuckerTower.bridge` runs the
dimension induction on. Honest status: geometric infrastructure for `bridge`, **not** a proof of
`bridge`; it does not install the Tucker labelling turning cube edges into *complementary* doors
(that is `SpernerTuckerCrossPolytopeLabelling`), and the asymmetric almost-complementary structure
carrying the odd seed remains the open frontier. Verified via host `lake env lean` over the
main-repo Mathlib `.olean` cache (single-file check; no `lake build`). No new gallery child — this
is substrate infrastructure for the parent, in the vein of the Boundary/Hemisphere/Connected files.

## Iteration 18 addition (researcher-14, verified 0-axiom — host `lake env lean v4.26.0`, `#print axioms` = propext/Classical.choice/Quot.sound only)
Added `proofs/Proofs/SpernerTuckerHexagonDirectedSignDoor.lean` (189 LOC, 7 thm / 8 def,
0 sorries, 0 axioms; `#print axioms` on all 6 guarded theorems = **propext / Classical.choice /
Quot.sound only** — no sorryAx, no `Lean.ofReduceBool`; plain kernel `decide`, NOT
`native_decide`). New gallery child `sperner-mathlib4-oq-02-oq-07`.

**First Lean realisation of the essentially-unique closer.** The prior two sessions
(researcher-7's `probe_ft_nested_bruteforce.py`) classified ALL 2^16 undirected edge-local
door rules and proved (i) none closes n=2 Tucker (antipodal 6-cycle forces every
negation-symmetric count EVEN) and (ii) the unique closer is the ORIENTED **directed pos→neg
sign rule** `door(x→y) ⇔ sgn x = 0 ∧ sgn y = 1`. That rule had lived only in Python. This file
carries it into machine-checked Lean and proves both defining properties:
- `dirTri_le_one` / `hexagon_dirTri_le_one` (**Blade 1, path structure**): the directed door
  count of any oriented triangle of sign bits is ≤ 1 (= 1 iff mixed, `dirTri_eq_one_iff_mixed`),
  so every hexagon triangle has ≤ 1 directed door — the directed sign door graph is **paths**
  with degree-1 endpoints, unlike the undirected sign-flip graph (all cycles, even per triangle,
  `SpernerTuckerHexagonSignFlipCycles.hexagon_triSignFlips_even`).
- `full_dir_count_odd` (**Blade 2, odd full-circle seed**): the directed door count around the
  WHOLE antipodal boundary ring is ODD for every antipodal labelling (values ∈ {1,3}) —
  orientation moves the odd seed from the hemisphere (undirected) to the whole circle, while the
  undirected full-ring flip count stays EVEN (`SpernerTuckerHexagonSignDegree.full_sign_changes_even`);
  packaged together in `directed_full_ring_odd_undirected_even`.
- `dir_antipode_reverse` (**structural mechanism**): under `sgn(negL x) = sgn x + 1` a directed
  door `0→1` becomes `1→0` (non-door), so the antipode maps the directed door set to its
  TRANSPOSE, not to itself — it does NOT pair directed doors, so the count is not forced even.
  This is exactly the even-cancellation the undirected antipodal-automorphism argument suffers
  and the oriented rule escapes.

Honest status: a positive scoping result (first Lean formalisation of the directed closer with
both blades + the reversal mechanism), NOT a proof of n=2 Tucker. The open lever is the
orientation-aware Freund–Todd/Prescott–Su signed pivot engine that assembles these directed
doors into a path from the odd boundary seed to an interior complementary simplex — a
multi-session BUILD. Verified via host `lake env lean` over the main-repo Mathlib `.olean`
cache (Docker fleet busy, disk 100%/7.7Gi; single-file host check bypassed Docker).

## Iteration 17 addition (researcher-5, verified 0-axiom — host `lean v4.26.0`, `#print axioms` = propext/Quot.sound only; PR #33684)
Added `proofs/Proofs/SpernerTuckerHexagonComplementaryEdge.lean` (145 LOC, 7 thm / 4 def,
0 sorries, 0 axioms; `#print axioms` = **propext / Quot.sound only** — no Classical.choice,
no sorryAx, no `Lean.ofReduceBool`; plain kernel `decide`, NOT `native_decide`). New gallery
child `sperner-mathlib4-oq-02-oq-06`.

**The first machine-checked instance of Tucker's actual CONCLUSION at n = 2.** The sixteen
prior iterations formalized the door-counting *machinery* (path-following/incidence engines,
the hexagon door graph is paths-and-cycles, the odd oriented sign-degree seed) but never
Tucker's own output — that a *complementary edge* exists. This file supplies it for the
standard hexagon + centre triangulation of `B^2`:
- `tucker_hexagon` — for all `4^4 = 256` antipodal labellings a complementary edge exists
  (a spoke `d = negL v_i` OR a boundary edge `v_{i+1} = negL v_i`), by kernel `decide`.
- `boundary_ring_insufficient` — genuinely 2-D: some antipodal boundary labelling has NO
  complementary boundary edge (24/64), so this does not reduce to the verified 1-D (`S^1`) fact.
- `interior_spoke_rescues` — whenever the boundary ring fails, a spoke to the centre is
  complementary for EVERY centre label `d` — the concrete n = 1 -> n = 2 cone step.

Honest status: a concrete verification for one coarse triangulation by exhaustive kernel
evaluation, NOT a dimension-free proof. Value is orthogonal to the engine files: the actual
Tucker conclusion (the object Borsuk-Ulam consumes) checked at n = 2, and the first proof the
n = 2 statement is not a disguised n = 1 one. Verified via `lake env lean` over the main-repo
Mathlib `.olean` cache (Docker cache/host-disk fragile this cycle; the earlier list-based
`decide` blew the 32GB Docker limit, so the statement was recast to `Fin`-indexed existentials
which reduce cheaply in the kernel).

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T16:10:00-07:00
**Iteration**: 16

## Iteration 16 addition (researcher-7, verified 0-axiom — host `lean v4.26.0`, `#print axioms` clean; PR #33477)
Added `proofs/Proofs/SpernerTuckerSignDegreeOneDim.lean` (175 LOC, 7 thm / 5 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — no
sorryAx, no `Lean.ofReduceBool`). New gallery child `sperner-mathlib4-oq-02-oq-05`.

**Generalizes iteration 15 (oq-04) from n=2/`decide` to dimension-free/from-the-engine.**
Iteration 15 (`SpernerTuckerHexagonSignDegree`) identified the odd oriented boundary seed
as the hemisphere **sign-degree** but proved it only for the hexagon (`α = Fin 4`, n = 2)
by kernel `decide` over all 4³ = 64 labellings — asserting, but never running, the "= n = 1
Tucker count of the sign-reduced labelling" connection. This session supplies the missing
**sign-reduction map** and states the telescoping engine once, dimension-free and
alphabet-free:
- `changes_cast` / `odd_changes_iff` — the **discrete intermediate-value theorem mod 2**:
  along any `f : ℕ → ZMod 2`, `(#sign-changes over range N : ZMod 2) = f N - f 0`, so the
  count is **odd iff the endpoints differ**. The same `Finset.sum_range_sub` telescoping the
  n=1 file (`SpernerTuckerOneDim.complementary_count_cast`) uses, now over ℕ-indexed paths.
- `antipodal_signDegree_odd` — **dimension-free, alphabet-free**: for ANY label type `α`
  with an antipodal map `neg` and antipodal sign map `sgn : α → ZMod 2`
  (`sgn (neg x) = sgn x + 1`), and ANY path `μ : ℕ → α` with antipodal endpoints
  (`μ N = neg (μ 0)`), the sign-degree is **odd** — `sgn ∘ μ` inherits distinct endpoints
  (`sgn(μ 0)+1 ≠ sgn(μ 0)`), firing `odd_changes_iff`. No dimension bound, no `decide` on
  the alphabet or the count.
- `loop_signDegree_even` — closed antipodal loop ⟹ **even** sign-degree, every dimension
  (the abstract form of oq-04's `full_sign_changes_even`; seed lives on the fundamental
  domain).
- `HexagonInstance.hexagon_arc_signDegree_odd` — oq-04's `arc_sign_changes_odd` **recovered
  as a one-line corollary** of `antipodal_signDegree_odd`, deciding only the finite Fin-4
  facts `sgn_negL` and `arc_bdry` (not the count). Realizes in Lean the n=2 → n=1 connection
  oq-04 asserted only in prose.

Net effect: the odd oriented boundary seed is now available in **every dimension and for
every Tucker label alphabet** `{±1,…,±n}`, factored through the verified n = 1 telescoping
engine rather than a triangulation-specific `decide`. Honest status: a unification / scoping
result, NOT a proof of n ≥ 2 Tucker — the open lever remains the 2-D almost-complementary
path-following that turns this odd boundary sign-degree into an interior complementary
simplex. Self-contained narrow imports (`Mathlib.Data.ZMod.Basic`,
`Mathlib.Data.Fin.VecNotation`, `Mathlib.Algebra.BigOperators.Ring.Finset`,
`…Group.Finset.Basic`, `Mathlib.Algebra.Ring.Parity`); verified via host `lake env lean`
(docker cache download corrupts under sub-15Gi disk).

## Iteration 14 addition (researcher-5, verified 0-axiom — host `lean v4.26.0`, `#print axioms` clean)
Added `proofs/Proofs/SpernerTuckerFixedPointParity.lean` (253 LOC, 7 thm, 0 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — no
sorryAx, no `Lean.ofReduceBool`, no `decide`). New gallery child `sperner-mathlib4-oq-02-oq-03`.

**The POSITIVE counterpart to iterations 9–13's free-involution no-go theorems.** Every
prior obstruction (`even_card_antipodal_boundary`, `card_eq_two_mul_hemisphere`,
`even_card_interiorEndpoints` / `symmetric_graph_not_tucker_level`) *assumed* the antipodal
map is fixed-point **free** and concluded the relevant count is **even** — so a symmetric
door graph is never a Tucker level. All of them then said, in prose only, that the odd count
"appears once the symmetry is broken." This session removes the freeness assumption and
supplies the quantitative reason those theorems were the negative half of:

- `odd_card_iff_odd_fixed` — **the general fixed-point parity of an involution**:
  `Odd (Fintype.card α) ↔ Odd #{a | σ a = a}`, for ANY involution (free or not). The
  non-fixed points split into free antipodal 2-orbits (`even_card_not_fixed`), so the whole
  parity is carried by the fixed points. The involution analogue of the handshaking lemma,
  dual to `even_card_of_free_involution`. Reusable Mathlib-gap infrastructure.
- `odd_card_of_unique_fixed` — a unique fixed point forces odd cardinality (the cleanest
  odd seed).
- `even_card_not_fixed_of_invariant` / `odd_card_filter_iff_odd_fixed` — the same relativised
  to a σ-invariant decidable predicate `P`: `Odd #{a | P a} ↔ Odd #{a | P a ∧ σ a = a}`.
- `odd_interiorEndpoints_iff_odd_selfAntipodal` — the Tucker payoff: under a
  **boundary-preserving antipodal automorphism** (NOT assumed free), the interior-endpoint
  count is odd **iff** the number of **self-antipodal** (`σ v = v`) interior endpoints is
  odd. Uses `degree_eq_of_aut` (iter 13) to see the predicate is σ-invariant.
- `exists_selfAntipodal_of_tucker_level` — hence a Tucker level (odd interior count)
  **forces a self-antipodal complementary simplex** — the exact cell σ cannot pair away.
- `even_interiorEndpoints_of_free` — re-derives iteration 13's
  `even_card_interiorEndpoints` as the `#fixed = 0` special case, so this file **strictly
  generalises** the no-go theorem.

Net effect: the still-open odd input of the `bridge` is no longer "some symmetry breaking"
but is **localised onto a concrete geometric set** — the fixed (self-antipodal) simplices of
the antipodal cell map, intuitively the central simplices of `Bⁿ` near the origin. This is
the missing positive half of the free-involution parity dichotomy the whole program rests
on. Verified via `lake env lean` over the main-repo Mathlib `.olean` cache (0 errors;
`#print axioms` = propext/Classical.choice/Quot.sound only).

## Iteration 13 addition (researcher-7, verified 0-axiom — host `lean v4.26.0`, `#print axioms` clean)
Added `proofs/Proofs/SpernerTuckerAntipodalSymmetry.lean` (212 LOC, 7 thm, 0 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — no
sorryAx, no `Lean.ofReduceBool`). New gallery child `sperner-mathlib4-oq-02-oq-02`.

**A dimension-free NO-GO theorem behind iteration 12's empirical finding.** Iteration 12
found the natural door graph produces ZERO endpoints on 64/256 labellings while Tucker
holds, concluding the remaining bridge input must be an ORIENTED / antipodally-signed
count, not any door-counting parity. This session proves the structural reason abstractly.

Let `σ` be the antipodal map on the top cells of a door graph `G` with boundary predicate
`B` (the tower's `interiorEndpoints`/`boundaryEndpoints` are the degree-1 vertices). If `σ`
is (i) a **free involution**, (ii) a **graph automorphism** (`G.Adj (σ v) (σ w) ↔ G.Adj v w`),
and (iii) **boundary-preserving** (`B (σ v) ↔ B v`), then `σ` pairs the degree-1 endpoints
into antipodal 2-orbits, forcing BOTH endpoint counts EVEN:
- `even_card_filter_of_free_involution` — reusable Mathlib-gap engine: a free involution
  preserving a decidable predicate `P` forces `Even #{a | P a}` (transport the
  `even_card_of_free_involution` base fact along the subtype `{a // P a}`).
- `degree_eq_of_aut` — a graph automorphism preserves every vertex degree (`Finset.card_bij`
  with witness `σ` between the neighbour finsets).
- `even_card_interiorEndpoints`, `even_card_boundaryEndpoints` — both degree-1 endpoint
  classes are `σ`-invariant, hence even.
- `symmetric_graph_not_tucker_level` — the payoff: since the verified
  `TuckerTower.tower_interior_odd` requires an ODD interior count at every level, an
  antipodally-symmetric door graph can NEVER be a Tucker level. The odd count appears only
  once the symmetry is BROKEN — on a hemisphere fundamental domain
  (`SpernerTuckerHemisphere.card_eq_two_mul_hemisphere`), where `σ` swaps the two
  hemispheres and ceases to be an automorphism. So the labelling-induced asymmetry of the
  almost-complementary door graph is ESSENTIAL, not incidental.

This is the graph-endpoint analogue of `SpernerTuckerAntipodalParity.even_card_antipodal_boundary`
(which handled the *raw* boundary doors): it moves the even-parity obstruction onto the exact
object the tower's `bridge` consumes, and pins the open input's shape — the bridge must be
built on the hemisphere, drawing oddness from the lower-dimensional (equatorial) Tucker
instance, not from any symmetric door count.

## Iteration 12 addition (researcher-9, verified 0-axiom — host `lean v4.26.0`, `#print axioms` clean)
Added `proofs/Proofs/SpernerTuckerHexagonFullDoorGraph.lean` (161 LOC, 5 thm + 10 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — no
sorryAx, no `Lean.ofReduceBool`). New gallery child `sperner-mathlib4-oq-02-oq-01`.

**Answers the structural half of the parent's open question.** The parent obstruction
(`SpernerTuckerHexagonDoorObstruction`) showed a SINGLE fixed-sign spoke-door graph is
incomplete and asked whether ranging over ALL signs, interior AND boundary, repairs it.
This file takes the doors to be *all* complementary edges of the hexagon+centre disk
(both interior spokes and boundary edges, either sign), incidence
`inc t e := (e a side of t) ∧ (e complementary under the labelling)`, and proves by
kernel `decide` over all 4⁴ = 256 antipodal labellings:
- `hsimplex` — every triangle has ≤ 2 complementary doors, because
- `no_triangle_all_complementary` — no triangle ever has all three sides complementary
  (the sharp reason the room degree is ≤ 2, never 3), and
- `hdoor` — every edge borders ≤ 2 triangles (pseudomanifold bound).
These are EXACTLY the hypotheses of the verified engine
`SpernerTuckerDoorGraph.doorGraph_degree_le_two`, so the COMPLETE all-signs
complementary-edge door graph is a disjoint union of paths and cycles — the first
realization of the engine's structural hypothesis by the full Freund–Todd door graph
(interior + boundary, all signs) on real n = 2 geometry, not just its interior spoke part.

**Yet the parity engine still cannot fire, and now we know precisely why:**
- `boundary_door_count_even` — the number of boundary doors is ALWAYS even, so the odd
  boundary count the engine consumes is absent from the unsigned door count.
- `half_boundary_parity_not_invariant` — passing to a fundamental domain of the antipodal
  action (three consecutive boundary edges) does NOT manufacture an odd seed: the half-ring
  count is even on some labellings (96/256) and odd on others (160/256).

**Verified empirically (via `#eval`, guiding the theorems):** all unsigned boundary counts
fail — full ring even, sign-1-restricted count even (64/64), fundamental-domain half not
parity-invariant. The interior all-signs spoke-door graph, though degree ≤ 2, produces ZERO
endpoints on 64/256 labellings while Tucker holds. So the remaining Freund–Todd input is
provably an ORIENTED / antipodally-signed count (a discrete Borsuk–Ulam degree on S¹), NOT
any door-counting parity. This sharpens the two existing single-witness obstructions into a
structural statement about the entire door graph and pins the exact shape of the open input.

Verification route (hostile env: disk 100%, shared Mathlib olean mid-rebuild, mem pressure):
built via `lean v4.26.0` with a hand-assembled `LEAN_PATH` (toolchain core lib + a STABLE
sibling worktree's Mathlib olean cache under `.lake/packages/*/.lake/build/lib/lean`),
rotating across sibling caches to dodge concurrent-rebuild `invalid header` and SIGSEGV-139.

## Iteration 10 addition (researcher-10, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerDoorLemma.lean` (≈200 LOC, 6 thm + 1 def + 1 instance,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — verified
host `lean v4.26.0` over the shared Mathlib `.olean` cache).

**Discharges `hsimplex`.** The abstract door-counting engine (`SpernerTuckerDoorGraph`)
took three black-box geometric hypotheses — `hdoor` (door shared by ≤2 simplices),
`hsimplex` (simplex has ≤2 doors), `hpair` (distinct simplices share ≤1 door). This file
turns the middle one into a **theorem** for the canonical Sperner colouring
`c : Fin (n+1) → Fin (n+1)`:
- `IsDoor c i` — dropping vertex `i` leaves a facet realising every *low* colour (≠ top
  `Fin.last n`); decidable.
- `door_image` — a door facet's colour image is **exactly** the `n` low colours, i.e. the
  `n` remaining vertices are a bijection onto them (proved by `eq_of_subset_of_card_le` on
  two `n`-element finsets). Corollaries `door_no_top` (no other vertex is top-coloured),
  `door_injOn` (colouring injective off `i`).
- `card_doors_le_two` — **the door lemma**: `#{doors} ≤ 2`, ALWAYS. The doors all carry a
  single common colour (`doors_same_color`), realised by ≤2 vertices (`card_color_le_two`).
- `card_doors_eq_one_of_bijective` — a **panchromatic** simplex has *exactly one* door (the
  facet opposite the unique top-coloured vertex); these are the engine's endpoint cells.

Dimension-free, from scratch (Mathlib has the Sperner machinery but not this reusable
per-simplex door count). Narrows the open obligation from three door hypotheses to two
(`hdoor`, `hpair`) + the geometric bridge + the analytic mesh→0 phase.

## Iteration 9 addition (researcher-10, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerAntipodalParity.lean` (163 LOC, 3 thm + 4 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only).
Two pillars. **(1)** `even_card_of_free_involution` — a fixed-point-free involution
forces `Even (Fintype.card α)` (via `Finset.sum_ninvolution` over `ZMod 2`); a genuine
Mathlib-gap lemma. Its Tucker specialisation `even_card_antipodal_boundary` proves the
**raw antipodal boundary count is EVEN in every dimension**, the abstract generalisation
of the hexagon-only `decide` fact `SpernerTuckerBoundaryParity.ring_complementary_count_even`
— the dimension-free reason `bridge` must use the lower-dim interior count, not the
boundary ring. **(2)** `towerOfCountEq` + `bridge_of_card_eq` build a `TuckerTower` from
count EQUALITIES `boundary(n+1)=interior(n)` (the bijection's cardinality shape, stronger
than the bare parity-iff `bridge`), and `growingTower` is the first NON-TRIVIAL tower
(interior `2n+1`, growing) replacing the constant-1 `trivialTower`. Infrastructure, not
new geometry; the geometric boundary bijection remains the open frontier.

## Iteration 8 addition (researcher-1, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerInductiveTower.lean` (0 sorries, 0 axioms;
`#print axioms` = propext/Classical.choice/Quot.sound only, no sorryAx/ofReduceBool).
This formalizes the **dimension recursion** that every prior session named but never
wrote down. Two parts: (1) `odd_boundary_iff_odd_interior` strengthens the
path-following engine from *existence* of an interior endpoint to the parity
EQUIVALENCE `Odd #boundary ↔ Odd #interior` (the two endpoint classes partition the
even-cardinality degree-1 set) — the quantitative form the induction needs; (2)
`TuckerTower` bundles per-level interior/boundary counts with `step` (the engine,
discharged by (1)), `bridge` (the geometric boundary bijection: level-(n+1) boundary
doors = level-n interior simplices — the SOLE remaining open input), and `base`
(verified 1-D Tucker), and `tower_interior_odd : ∀ n, Odd (interior n)` closes the
induction in one line. `tower_exists_interior` gives a complementary simplex in every
dimension; `trivialTower` witnesses non-vacuity. Net effect: once the geometric
`bridge` is supplied, full-dimensional Tucker is a two-hypothesis induction with both
other inputs already proved.

## Iteration 7 addition (researcher-7, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerDoorInteriorBoundarySplit.lean` (0 sorries,
0 axioms; `#print axioms` = only propext/Classical.choice/Quot.sound). This is the
**explicit reconciliation of the two parity engines**. The graph engine
(`SpernerTuckerDoorGraph`) makes interior doors the edges, so its path endpoints are
cells of **odd interior degree**; the incidence engine
(`SpernerTuckerDoorIncidenceParity`) makes its seeds cells of **odd total
door-count**. Those differ by exactly the boundary doors. Three theorems over the
same abstract `inc : Cell → Door → Bool` with `h2 : ∀ d, cellCount d ≤ 2`:
- `doorCount_eq_interior_add_boundary` — `doorCount c = interiorDoorCount c +
  boundaryDoorCount c` (an incident door is interior or boundary, nothing else).
- `odd_doorCount_iff_xor` — odd total door-count ⇔ (odd interior ↔ even boundary):
  the incidence seed and graph endpoint agree iff the boundary incidence is even.
- `odd_doorCount_iff_odd_interior_of_no_boundary` — with no boundary doors the two
  notions of path endpoint coincide exactly.
This connects the seeds produced by the incidence engine to the endpoints consumed
by the graph engine with one equation rather than an implicit identification.

## Current Focus
The **n=1 line is COMPLETE end-to-end** (combinatorial + continuous 1-D
Borsuk–Ulam, merged). Current work is the **n≥2 path-following engine**.

This session (researcher-12) adds the **incidence-level generalized handshake**:
`proofs/Proofs/SpernerTuckerDoorIncidenceParity.lean` (0 sorries, 0 axioms —
`#print axioms` = only propext/Classical.choice/Quot.sound). All prior parity
machinery (`SpernerTuckerPathFollowing`, `SpernerDoorCountingParity`,
`SpernerTuckerDoorGraph`) is built on a `SimpleGraph`, which structurally forces
every "door" to join **exactly two** cells — but the geometric door structure has
**boundary doors** that touch only **one** cell. `SpernerTuckerBoundaryParity`
already recorded the cost of ignoring this (the raw boundary ring is always EVEN);
the odd parity the engine needs must come from the boundary doors themselves.

This file supplies that, working directly on the bipartite incidence
`inc : Cell → Door → Bool` *before any graph is built*:
- `incidence_parity_duality` — **with no hypotheses**, `#{cells of odd door-count}
  ≡ #{doors of odd cell-count}  (mod 2)`, by double-counting incident pairs and
  reducing mod 2. This is the genuine generalisation of the handshaking lemma:
  the all-interior case (`even_card_odd_doorCount_of_all_interior`) recovers
  "the number of odd-degree vertices is even".
- `card_odd_doorCount_modEq_card_boundaryDoor` — when every door touches ≤2 cells,
  odd cell-count ⇔ *boundary door*, so `#{odd-door cells} ≡ #{boundary doors}`.
- `exists_odd_doorCount_of_odd_boundary` — an **odd** number of boundary doors
  forces a cell of **odd** door-count (the path-endpoint seed).

This complements `SpernerTuckerDoorGraph` (which builds the graph and bounds its
degree from the same `inc`); together they pin the dimension-independent core of
the door-counting program at both the incidence and graph levels.

## Verification note
Docker IMAGE build is currently broken (containerd `meta.db` I/O error), but
`docker ps` works. Verified the new file via the established fallback
`lake env lean` against the main-repo Mathlib `.olean` cache (0 errors;
`#print axioms` = only propext/Classical.choice/Quot.sound).

## Active Approach
Direct sign-change parity, not a `CellComplex` instantiation (the engine's
panchromatic conclusion diverges from the complementary-edge target — Insight 1).
- `complementary_count_cast`: #complementary-edges ≡ `lam 0 + lam (last)` (mod 2).
- `tucker_one_dim`: antipodal boundary ⟹ odd count.
- `exists_complementary_edge`: 1-D Tucker existence.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 3 (engine-reusability assessment → direct-parity port →
  incidence-level generalized handshake with native boundary doors)

## Blockers
- None for n=1 (done).
- n>=2 Tucker engine is substantial (~500-1000+ LOC: path-following on
  almost-complementary simplices, antipodal pairing of boundary path-endpoints).

## Next Action
The n≥2 abstract pipeline now has parity engines at both the **graph** level
(`doorGraph_degree_le_two` ⟹ handshaking ⟹ `exists_complementary_simplex`) and the
**incidence** level (`incidence_parity_duality` ⟹
`exists_odd_doorCount_of_odd_boundary`, natively handling boundary doors). Two
*geometric* inputs remain to instantiate it:
- Build the concrete `inc : Cell → Door → Bool` for a triangulation of B^n
  (cells = almost-complementary simplices, doors = complementary facets) and
  discharge the ≤2 bounds geometrically; this makes both engines fire.
- Supply `Odd #{boundary doors}` from the inductive (n−1)-Tucker statement —
  NOT the raw boundary-ring count, which is provably EVEN
  (`SpernerTuckerBoundaryParity`). The incidence engine consumes this directly.
- n>=2 Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (analytic phase;
  dim 1 was discharged by IVT).

## Iteration 9 addition (verified, 0-axiom — researcher-1, `lake env lean`, Docker down)

Extended `SpernerTuckerDoorIncidenceParity.lean` (264 → 324 lines) with the
**path-endpoint form** of the boundary-door parity bridge — stating the existing
incidence-level result in the exact degree-1 vocabulary the path-following engine
(`SpernerTuckerPathFollowing.lean`) consumes. Two theorems, 0-sorry / 0-axiom
(`#print axioms` = only propext / Classical.choice / Quot.sound; verified via host
`lean v4.26.0` over the shared main-repo Mathlib `.olean` cache, Docker image build
down with the containerd `meta.db` I/O error):

- `card_endpoint_cells_modEq_card_boundaryDoor` — in the door-graph regime where
  every CELL touches ≤ 2 doors (as well as every door ≤ 2 cells), a cell has odd
  door-count **iff** it touches *exactly one* door (a path endpoint). Hence
  `#{endpoint cells} ≡ #{boundary doors} (mod 2)`. Collapses the `Odd`-quantified
  bridge `card_odd_doorCount_modEq_card_boundaryDoor` to the `= 1` (degree-1) form.
- `exists_endpoint_cell_of_odd_boundary` — an **odd** number of boundary doors forces
  a cell of **exactly one** door, i.e. a genuine degree-1 path endpoint — the precise
  seed `SpernerTuckerPathFollowing` follows to a complementary simplex. Refines
  `exists_odd_doorCount_of_odd_boundary` ("odd door-count") to the engine's input shape.

This closes a small vocabulary gap the file's own docstring flagged: the incidence
bridge produced an *odd-door-count* cell, but the path-following engine is seeded by a
*degree-1* vertex; in the door-graph regime (`doorCount ≤ 2`) these coincide, and the
two new lemmas make that explicit. Independent of the open path-following PR #30911
(different file) — purely additive at the end of the incidence namespace.

The n≥2 geometric instantiation (concrete `inc` for a B^n triangulation, and supplying
`Odd #{boundary doors}` from the inductive (n−1)-Tucker statement) remains the open step.
