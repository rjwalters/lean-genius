# Knowledge Base: sperner-mathlib4-oq-02

Tucker's lemma (and Borsuk–Ulam) from the parent's abstract door-counting engine.

---

## Problem Understanding

Parent `sperner-mathlib4` (`proofs/Proofs/SpernerMathlib4.lean`, 732 LOC, GREEN)
proves Sperner's lemma abstractly:

- `CellComplex V d`: `Cell` type, `vertex : Cell → Fin (d+1) → V`,
  `adj : Cell → Fin (d+1) → Option (Cell × Fin (d+1))` with symmetry /
  shared-face / distinctness axioms.
- `IsPanchromatic c K s`  := `c ∘ vertex s` surjective onto `Fin (d+1)`.
- `IsDoor c K s k`        := dropping vertex `k`, the other `d` vertices realize
  all colors `{0,…,d-1}`.
- `door_count_parity`: a coloring `f : Fin (d+1) → Fin (d+1)` has door count ≡ 1
  (mod 2) iff `f` is surjective, else 0.
- `sperner_parity`: `#panchromatic ≡ #boundary-doors (mod 2)`.
- `sperner`: odd boundary doors ⟹ a panchromatic cell exists.

The OQ asks: does this engine extend to **Tucker's lemma** — antipodally
symmetric triangulation of `Bⁿ`, labelling `λ : V → {±1,…,±n}` antipodal on the
boundary (`λ(-v) = -λ(v)`), conclusion: some edge is **complementary**
(`λ(u) = -λ(v)`)? Tucker ⟹ Borsuk–Ulam.

---

## Insights

### Insight 1 — the parent engine is hard-wired to the Sperner target
`door_count_parity`, `IsPanchromatic`, `IsDoor` are all stated over an *unsigned*
color alphabet `Fin (d+1)` with the conclusion "a `d`-cell sees all `d+1` colors".
Tucker's alphabet is *signed* with `2n` labels `{±1,…,±n}` and its conclusion is a
**1-dimensional** object (a complementary edge), not a full-dimensional
panchromatic cell. There is no black-box specialization of `CellComplex.sperner`
that yields Tucker — the *target object has the wrong arity and the wrong
algebraic structure*. (Engine-divergence probe, n=2 hexagon: 40 antipodal
labellings have a complementary edge but no "rainbow-signed" triangle — the two
conclusions are not interchangeable.)

### Insight 2 — n=1 Tucker IS a direct door-count corollary (PORTABLE)
Exhaustive check of `B¹ = [-m,m]` (3,5,7 vertices; labels `{+1,-1}`; antipodal
endpoints `λ(m) = -λ(-m)`, interior free): the **complementary-edge count is
ALWAYS ODD** (distributions `{1:4}`, `{1:8,3:8}`, `{1:12,3:40,5:12}`). This is
exactly a door-counting parity over a 2-label alphabet: complementary edges are
the "doors", antipodal boundary forces an odd boundary contribution, interior
pairing gives the rest. So **n=1 Tucker (= 1-D Borsuk–Ulam) is a near-mechanical
port of the parent engine** restricted to `d=1` with a signed 2-symbol alphabet.

### Insight 3 — n≥2 Tucker is NOT a one-step parity (needs path-following)
Exhaustive check of `B²` (hexagon + center, antipodally symmetric, 6 triangles,
labels `{±1,±2}`, 256 antipodal labellings): Tucker holds (0 labellings without a
complementary edge) BUT the complementary-edge count is **not** a parity invariant
— distribution `{1:48, 2:72, 3:48, 4:48, 5:24, 6:8, 9:8}`, only 128/256 odd.
Hence the parent's "count the target object, show it's odd" strategy does NOT lift
to `n≥2`. The standard remedy is **Freund–Todd (1981) / Prescott–Su
path-following on *almost-complementary* simplices**: paths run between
complementary simplices and the boundary; the antipodal boundary condition pairs
boundary path-endpoints, forcing an interior complementary simplex. This is a
genuinely different parity engine (parity of path endpoints, not of the target
set itself).

### Insight 4b — n=1 Tucker ⟹ Borsuk–Ulam collapses to IVT (PORTABLE, DONE)
The general Tucker ⟹ Borsuk–Ulam reduction is an analytic limit (refine the
triangulation, mesh → 0, extract a convergent subsequence by compactness). In
**dimension 1** this limit *collapses entirely to the Intermediate Value
Theorem*: a continuous function with antipodal boundary values (`f a = -f b`)
has a zero between `a` and `b` — the exact continuous mirror of "an antipodal
sign boundary forces a complementary edge". From this, the genuine continuous
**1-D Borsuk–Ulam** follows: for continuous 1-periodic `f`, the antipodal
difference `g x = f x - f (x + 1/2)` satisfies `g 0 = -g (1/2)` (periodicity),
so `g` has a zero ⟹ `f c = f (c + 1/2)` for some `c`. Shipped as
`SpernerTuckerBorsukUlamOneDim.lean` (`exists_zero_of_antipodal`,
`borsuk_ulam_circle`), 117 LOC, 0 sorries, 0 axioms (IVT only). Mathlib has **no**
Borsuk–Ulam theorem of its own, so this is a genuinely new artifact, not a
re-export. NB: the analytic collapse is special to n=1; for n≥2 the mesh→0 /
compactness argument is the real (still-open) analytic phase.

### Insight 4 — buildability split
- **n=1 milestone**: small, self-contained `CellComplex`-style parity over
  `{+1,-1}`. Estimated < 200 LOC. BUILD when Docker is up.
- **General Tucker**: the Freund–Todd path-following engine + antipodal pairing of
  boundary endpoints is substantial (≈ 500–1000+ LOC) and is the real content;
  alternatively a Tucker-via-Sperner "doubling/quotient" reduction (problem.md
  approach 2) trades the path-following for orientation bookkeeping on `ℝPⁿ`.
- **Tucker ⟹ Borsuk–Ulam** (continuous, mesh→0 + compactness) is a separate
  analytic phase, out of scope for the combinatorial engine.

### Insight 5 — door conservation localizes the boundary (PORTABLE, DONE)
With the sharp degree formula `degree v = #(shared doors of v)` in hand, the doors
of a simplex split as shared (= graph degree) ⊕ boundary (carried by no other
simplex), giving `degree v + #(boundary doors v) = #(all doors v)`
(`doorGraph_degree_add_boundaryDoors`, 0-axiom). Consequence: a degree-1 *endpoint*
with the maximal two doors has exactly one boundary door (`boundaryDoor_of_endpoint`).
This makes "is a path endpoint" a **purely local** statement about a simplex's own
boundary doors, with no reference to the global graph — the precise hook for the
still-open `Odd #{boundary endpoints}` step, which becomes a count of boundary doors
supplied by inductive (n−1)-Tucker. The abstract door-counting engine
(`SpernerTuckerDoorGraph.lean`) is now closed end-to-end up to that one geometric/
inductive boundary input.

---

## Dead Ends

- **"Adapt `door_count_parity` to complementary edges and show the boundary count
  is odd"** — fails for `n≥2`: the complementary-edge count is not odd in general
  (verified, B² distribution above). Only works for `n=1`.

---

## Verification Artifact

`verify_tucker.py` (this dir) — Docker-free, exhaustive. Confirms Tucker on
`B¹` (3/5/7 vtx) and `B²` (hexagon+center), prints the complementary-edge-count
distributions (the parity evidence), and runs the engine-divergence probe. All
assertions pass: every antipodal labelling on every enumerated triangulation has
a complementary edge.

---

## Session Log

## Session 2026-06-28 (researcher-10) — ACT: antipodal free-involution parity engine + bridge-as-bijection

**Mode**: REVISIT (RICH; n=1 line done, abstract n≥2 engine + dimension induction done).
**Outcome**: progress (ACT) — new `proofs/Proofs/SpernerTuckerAntipodalParity.lean`
(163 LOC, 3 thm + 4 def, 0 sorries, 0 axioms). Verified offline via
`LAKE_UNSAFE=1 lake env lean -o …olean` against the main-repo Mathlib `.olean` cache
(Docker host down). `#print axioms` on `even_card_of_free_involution`,
`even_card_antipodal_boundary`, and `growingTower`: **only**
propext/Classical.choice/Quot.sound — no `sorryAx`, no `Lean.ofReduceBool`.

New file (no collision: the three open PRs #31090/#31094/#30911 edit
DoorGraph/DoorIncidenceParity/PathFollowing).

### What I Did — two pillars

**Pillar 1 — the antipodal parity engine (genuine Mathlib-gap lemma).**
- `even_card_of_free_involution`: a fixed-point-free involution `σ` (σ∘σ=id, ∀a σa≠a)
  forces `Even (Fintype.card α)`. Proof: sum the constant `1 : ZMod 2` over `univ`;
  `Finset.sum_ninvolution` cancels it in antipodal pairs (`1+1=0`), so the total — the
  card mod 2 — vanishes (`ZMod.natCast_eq_zero_iff_even`). Mathlib had no direct form
  (only the much heavier `p`-group `card_modEq_card_fixedPoints`).
- `even_card_antipodal_boundary`: the boundary doors carry the free antipodal involution
  `d ↦ -d`, so the **raw** antipodal boundary count is EVEN **in every dimension**. This
  is the abstract, dimension-free generalisation of
  `SpernerTuckerBoundaryParity.ring_complementary_count_even` (proved only for the n=2
  hexagon, by a 64-case `decide`) — and the precise reason the inductive `bridge` must
  draw its odd parity from the lower-dimensional interior count, not the boundary ring.

**Pillar 2 — the geometric bridge as an explicit cardinality bijection.**
- `bridge_of_card_eq` + `towerOfCountEq`: build a `TuckerTower` from per-level count
  EQUALITIES `boundary (n+1) = interior n` (the cardinality consequence of the geometric
  boundary bijection) — strictly stronger input than the bare parity-iff `bridge`, and
  exactly what an explicit bijection supplies.
- `growingTower`: the first **non-trivial** `TuckerTower` (interior `n = 2n+1`, growing),
  replacing the constant-`1` `trivialTower` (`bridge := Iff.rfl`), demonstrating the
  dimension recursion does substantive work on non-constant data.

### Honest status
Parity infrastructure, NOT new Tucker geometry. Pillar 1 is a genuine reusable
Mathlib-gap lemma that lifts a previously `decide`-only fact to all dimensions; Pillar 2
sharpens the open obligation (bijection, not parity coincidence). The geometric
construction of the boundary bijection (`boundary (n+1) = interior n` from the antipodal
hemisphere folding) remains the open frontier, as every prior session flagged.

### Files Modified
- proofs/Proofs/SpernerTuckerAntipodalParity.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps
- Apply `even_card_of_free_involution` to the antipodal boundary sphere `Sⁿ` with a
  hemisphere fundamental domain to derive the bridge count equality
  `boundary (n+1) = interior n` geometrically, then feed `towerOfCountEq`.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-27 (researcher-2) — ACT: door-conservation identity (degree + boundary doors = total doors)

**Mode**: REVISIT (RICH). **Outcome**: progress — `SpernerTuckerDoorGraph.lean`
(+2 theorems, ~60 L, 0 sorry, `#print axioms` = `[propext, Classical.choice,
Quot.sound]` only, NO `ofReduceBool`/`sorryAx`). Verified via single-file
`lake env lean` against the main-repo Mathlib olean cache (Docker host still down).

### What I Did
The prior session sharpened the degree bound to an *equality* `degree v =
#(shared doors of v)` (`doorGraph_degree_eq_shared`). This session uses that to
prove the **door-conservation law** and read off the local boundary fingerprint:

- `doorGraph_degree_add_boundaryDoors` — under `hdoor` (≤2 simplices/door) and
  `hpair` (distinct simplices share ≤1 door),
  `degree v + #{d | inc v d ∧ ∀ w ≠ v, ¬ inc w d} = #{d | inc v d}`.
  Proof: rewrite `degree` as `#shared` (the sharp formula); the shared doors
  (`∃ w ≠ v, inc w d`) and the boundary doors (its negation, `push_neg`) partition
  the doors of `v` via `Finset.filter_card_add_filter_neg_card_eq_card`.
- `boundaryDoor_of_endpoint` — a degree-1 endpoint carrying the maximal two doors
  has **exactly one** boundary door (`1 + b = 2`, `omega`).

### Why this matters
Conservation converts the *global* graph degree of a simplex into a *purely local*
count of its boundary doors — the abstract analogue of "interior facets are shared,
boundary facets are not". The endpoint corollary is the clean local fingerprint of
a boundary complementary simplex: one shared facet (its unique graph edge) + one
boundary facet (the facet the inductive `(n−1)`-Tucker count enumerates). This is
the conservation law that the still-open `Odd #{boundary endpoints}` step plugs into:
boundary endpoints ↔ simplices with an odd number of boundary doors.

### Files Modified
- proofs/Proofs/SpernerTuckerDoorGraph.lean (+`doorGraph_degree_add_boundaryDoors`,
  +`boundaryDoor_of_endpoint`)
- research/problems/sperner-mathlib4-oq-02/knowledge.md

### Next Steps (frontier unchanged; boundary interface now local)
- Supply `Odd #{boundary endpoints}` for a concrete antipodal triangulation by
  counting **boundary doors** (now a local per-simplex quantity) via inductive
  (n−1)-Tucker — feeds `exists_complementary_simplex`.
- Build the concrete `inc : V → D → Prop` and discharge `hdoor`/`hsimplex`/`hpair`
  geometrically; a boundary endpoint is a two-door simplex with one boundary door.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam: analytic phase.

## Session 2026-06-27 (researcher-2) — ACT: sharp degree formula (degree = #shared doors)

**Mode**: REVISIT (RICH). **Outcome**: progress — `SpernerTuckerDoorGraph.lean`
(+1 theorem `doorGraph_degree_eq_shared`, ~75 L, 0 sorry, 0 axiom —
`#print axioms` = `[propext, Classical.choice, Quot.sound]` only, NO
`ofReduceBool`/`sorryAx`). Verified via single-file `lake env lean`
(toolchain `leanprover/lean4:v4.26.0`, exit 0, ~6 s; Docker host still down).

### What I Did
Last session (researcher-6) derived `doorGraph_degree_le_two` — the path-following
engine's `degree ≤ 2` hypothesis — from two `≤2` door-incidence bounds. This
session **sharpens that bound to an equality**, which is the interface the
geometric `inc` construction actually needs:

- `doorGraph_degree_eq_shared` — under (i) `hdoor` (each door joins ≤2 simplices)
  and (ii) **`hpair`** (two *distinct* simplices share at most one door — the
  door-graph analogue of `adj_unique_facet`), the door-graph degree of `v` equals
  the number of `v`'s **shared** doors:
  `(doorGraph inc).degree v = #{d | inc v d ∧ ∃ w ≠ v, inc w d}`.
  Proof: `Finset.card_bij` with the witness map *neighbour `w` ↦ the door it
  shares with `v`* (the `g`/`Exists.choose` witness reused from
  `doorGraph_degree_le_two`). It lands in the shared doors; injective by `hdoor`
  (a door joining `v` to two distinct neighbours would touch three simplices);
  surjective by `hpair` (a shared door's other endpoint `w` is a neighbour, and
  `hpair` forces `g w` to be exactly that door). Empty-`D` handled separately
  (both sides 0).

### Why this matters
`degree_le_two` only gave the path/cycle structure. The *equality* converts the
order-theoretic predicate "`v` is a path endpoint" (`degree v = 1`) into the
purely **local** door statement "`v` has exactly one shared door". That is the
clean target for the still-open geometric step: building `inc` and identifying the
interior complementary simplices (= endpoints with one shared door, no boundary
door) without reasoning about the global graph. `hpair` is a new, natural geometric
obligation the construction must also supply (besides the two `≤2` counts).

### Files Modified
- proofs/Proofs/SpernerTuckerDoorGraph.lean (+`doorGraph_degree_eq_shared`)
- src/data/research/problems/sperner-mathlib4-oq-02.json (knowledge)
- research/problems/sperner-mathlib4-oq-02/knowledge.md

### Next Steps (unchanged frontier; interface now sharper)
- Build the concrete `inc : V → D → Prop` for a triangulation and discharge
  `hdoor`, `hsimplex`, and now `hpair` geometrically; a path endpoint is exactly a
  simplex with **one** shared door (`doorGraph_degree_eq_shared`).
- Supply `Odd #{boundary endpoints}` from inductive (n−1)-Tucker.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam: analytic phase.

## Session 2026-06-27 (researcher-6) — ACT: door-counting ⟹ degree ≤ 2 bridge

**Mode**: REVISIT (RICH)
**Outcome**: progress — `proofs/Proofs/SpernerTuckerDoorGraph.lean` (new, 227 LOC,
4 thm + 1 def, 0 sorry, 0 axiom — `#print axioms` = propext/Classical.choice/
Quot.sound only, NO ofReduceBool). Verified via `lake env lean` against the
main-repo Mathlib olean cache (Docker image build still broken).

### What I Did
The abstract path-following engine (`SpernerTuckerPathFollowing.lean`) and its
interior-parity refinement take `∀ v, G.degree v ≤ 2` as a **black-box
hypothesis**. The OQ's whole framing is "Tucker *from abstract door-counting*",
so that bound should not be assumed — it should come from the *door incidence
structure*. This session derives it, fully abstractly:

- `doorGraph (inc : V → D → Prop)` — the almost-complementary-simplex graph:
  `v ~ w ⟺ v ≠ w ∧ ∃ d, inc v d ∧ inc w d` (share a door).
- `doorGraph_degree_le_two` — **the door-counting degree bound**: if each door is
  incident to ≤2 simplices (`∀ d, #{v | inc v d} ≤ 2`) and each simplex has ≤2
  doors (`∀ v, #{d | inc v d} ≤ 2`), then `degree v ≤ 2`. Proof: the neighbours
  of `v` inject into the ≤2 doors of `v` via a shared-door witness; injectivity
  holds because a single door joining `v` to two distinct neighbours would be
  incident to three distinct simplices, contradicting the ≤2 door bound.
- `doorGraph_even_endpoints` — handshaking ⟹ even # path endpoints.
- `tucker_door_count` — **quantitative Tucker from door-counting**: odd boundary
  endpoints ⟹ odd interior (complementary) simplices; the analogue of the parent
  `sperner_parity`.
- `exists_complementary_simplex` — existence corollary.

### Key Findings
- The engine's `degree ≤ 2` hypothesis is a *theorem* of the door-incidence
  structure, not an assumption (Insight added). This realizes the OQ title
  literally: door-counting (≤2 doors/simplex, ≤2 simplices/door) ⟹ the
  paths-and-cycles structure that drives the parity argument.
- The remaining n≥2 gap is now sharply localized: supply `Odd #{boundary
  endpoints}` (inductive (n−1)-Tucker — NOT the raw ring count, which is EVEN)
  and the *geometric* construction of `inc` for a concrete triangulation. Both
  feed directly into `exists_complementary_simplex`.

### Files Modified
- proofs/Proofs/SpernerTuckerDoorGraph.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps
- Build the concrete `inc : V → D → Prop` for a triangulation (V = almost-
  complementary simplices, D = complementary facets) and discharge the two ≤2
  bounds geometrically.
- Supply `Odd #{boundary endpoints}` from inductive (n−1)-Tucker.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): analytic phase.

## Session 2026-06-14 (Session 2) — ORIENT: engine reusability assessment

**Mode**: FRESH
**Outcome**: progress (ORIENT) — Docker DOWN, no Lean written

### What I Did
- Read the full parent engine `SpernerMathlib4.lean` (abstract `CellComplex`
  door-counting; `sperner_parity`, `sperner`).
- Built `verify_tucker.py`: exhaustive Tucker check on `B¹`/`B²` + parity probe +
  engine-divergence probe. All assertions pass.

### Key Findings
- Parent engine is specialized to the unsigned `Fin (d+1)` panchromatic target;
  no black-box reduction yields Tucker (Insight 1).
- n=1 Tucker = direct door-count parity (complementary edges always ODD) →
  portable first milestone (Insight 2).
- n≥2 Tucker complementary-edge count is NOT a parity invariant → needs
  Freund–Todd path-following, a different engine (Insight 3).

### Files Modified
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}
- research/problems/sperner-mathlib4-oq-02/verify_tucker.py (new)

### Next Steps
- Docker up → port n=1 Tucker as a `CellComplex`-style parity lemma over `{±1}`.
- Scope Freund–Todd path-following engine for n≥2 (BUILD vs Sperner-doubling).

## Session 2026-06-27 (Session 3) — ACT: n=1 Tucker milestone shipped (verified)

**Mode**: BUILD (Docker UP — the prior session's blocker is cleared)
**Outcome**: progress (ACT) — new verified file, 0 sorries, 0 axioms

### What I Did
- Ported the n=1 Tucker milestone (Insight 2) to Lean as
  `proofs/Proofs/SpernerTuckerOneDim.lean` (169 LOC). Built clean via
  `docker-build.sh Proofs.SpernerTuckerOneDim` (exit 0).
- Chose the **direct sign-change parity** proof over instantiating the abstract
  `CellComplex`: the engine's panchromatic conclusion genuinely diverges from the
  complementary-edge target (Insight 1), so a black-box instantiation is clunky and
  no cleaner than the direct discrete-FTC argument.

### Theorems (all verified, 0-axiom, kernel `decide` only)
- `complementary_count_cast`: telescoping ZMod-2 identity — the number of
  complementary edges, cast to `ZMod 2`, equals `lam 0 + lam (Fin.last N)`
  (discrete fundamental theorem of calculus: #sign-changes = net sign change).
- `tucker_one_dim`: antipodal boundary (`lam 0 ≠ lam (Fin.last N)`) ⟹ the
  complementary-edge count is **odd**.
- `exists_complementary_edge`: **1-D Tucker** — antipodal boundary ⟹ a
  complementary edge exists. This is the combinatorial core of 1-D Borsuk–Ulam.

### Encoding notes
- Signs `{+1,-1}` encoded as `ZMod 2` (`+1↦0`, `-1↦1`). Path of `N+1` vertices
  `Fin (N+1)`; edge `i : Fin N` joins `i.castSucc` and `i.succ`.
- Antipodal boundary `λ(-v) = -λ(v)` at the two endpoints ⇔ `lam 0 ≠ lam (last)`.
- Key Mathlib lever: `Finset.sum_range_sub` (telescoping over `range N`) after
  extending `lam` to `g : ℕ → ZMod 2`; in `ZMod 2`, `-x = x` (proved by `decide`)
  turns the additive indicator into a telescoping difference.

### Files Modified
- proofs/Proofs/SpernerTuckerOneDim.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (knowledge + leanFiles)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps (unchanged for n≥2)
- n≥2 Tucker needs the Freund–Todd / Prescott–Su path-following engine (the
  complementary-edge count is NOT a parity invariant for n≥2 — Insight 3). Or the
  Tucker-via-Sperner doubling/quotient reduction on RPⁿ.
- Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (separate analytic phase).

## Session 2026-06-27 (Session 4) — ACT: continuous 1-D Borsuk–Ulam capstone (verified)

**Mode**: BUILD (Docker IMAGE build broken — containerd `meta.db` I/O error; verified
via `lake env lean` fallback against main-repo Mathlib `.olean` cache)
**Outcome**: progress (ACT) — new verified file, 0 sorries, 0 axioms

### What I Did
- Completed the **n=1 line end-to-end** by adding the continuous capstone
  `proofs/Proofs/SpernerTuckerBorsukUlamOneDim.lean` (117 LOC). It carries out the
  **Tucker ⟹ Borsuk–Ulam** reduction in dimension 1, where the usual mesh→0 /
  compactness limit collapses to the **Intermediate Value Theorem** (Insight 4b).

### Theorems (all verified, 0-axiom: propext/Classical.choice/Quot.sound only)
- `exists_zero_of_antipodal`: continuous `f` with antipodal boundary `f a = -f b`
  has a zero in `uIcc a b` (continuous analogue of `exists_complementary_edge`).
  Proof: `intermediate_value_uIcc` at the value `0`, which lies in `uIcc x (-x)`.
- `borsuk_ulam_circle`: **1-D Borsuk–Ulam** — continuous 1-periodic `f : ℝ → ℝ`
  has `f c = f (c + 1/2)` for some `c`. Proof: antipodal difference
  `g x = f x - f (x + 1/2)` has `g 0 = -g (1/2)` by periodicity, then the above.

### Gotchas
- After `rw [hanti]` the IVT interval is `uIcc (-f b) (f b)`; needed
  `Set.uIcc_comm` to match the helper `zero_mem_uIcc_neg : 0 ∈ uIcc x (-x)`.
- Mathlib has NO Borsuk–Ulam theorem (only a passing mention in
  `Topology/Homotopy/LocallyContractible.lean`) — this is a genuinely new artifact.

### Files Modified
- proofs/Proofs/SpernerTuckerBorsukUlamOneDim.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + currentState)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps (n≥2 unchanged)
- n≥2 Tucker: Freund–Todd / Prescott–Su path-following engine (Insight 3), or
  Tucker-via-Sperner doubling on RPⁿ. The n≥2 Tucker ⟹ Borsuk–Ulam mesh→0 /
  compactness analytic phase remains the genuine open analytic step.

## Session 2026-06-27 (Session 5) — ACT: boundary-parity correction (verified)

**Mode**: REVISIT (n=1 line + abstract n≥2 engine already done; this advances n≥2)
**Outcome**: progress (ACT) — new verified file, 0 sorries, 0 axioms (decide/kernel)

**Collision note**: a concurrent agent independently landed the n=2 Tucker
hexagon `decide` instance as `proofs/Proofs/SpernerTuckerHexagon.lean`
(PR #30917, `hexagon_tucker` + `count_parity_not_invariant`). To avoid
duplicating that artifact, this session contributes the **complementary**
boundary-parity result in a separate file rather than a competing same-name PR.

### What I Did
- Built `proofs/Proofs/SpernerTuckerBoundaryParity.lean` (84 LOC). Verified via
  `lake env lean` against the main-repo Mathlib `.olean` cache (Docker has no Lean
  image). `#print axioms`: only propext / Classical.choice / Quot.sound —
  **no `Lean.ofReduceBool`** (plain `decide`, not `native_decide`), no `sorryAx`.
  Genuinely 0-axiom.

### Theorems (all verified, kernel `decide`)
- `ring_complementary_count_even`: **negative parity result** — the
  complementary-edge count on the antipodal hexagon *boundary ring* is **always
  even** (distribution `{0,2,6}` over 64 antipodal ring labellings).
- `ring_complementary_count_not_odd`: contrapositive reading — the circle-parity
  shortcut is provably unavailable.
- `lneg_involutive`: label negation is an involution.

### Key correction (saves the next session a wrong turn)
The abstract engine `SpernerTuckerPathFollowing.exists_interior_degree_one`
requires `Odd #{boundary ends}`. The tempting shortcut — feed it the boundary
**circle's** complementary-edge count — **cannot work**: that count is always
EVEN (now proved in Lean). (The spoke count is mixed-parity
`{0:32,1:96,2:96,3:32}`, no shortcut either — see Python probe.) The engine's odd
boundary parity must come from the refined *almost-complementary* simplex
structure (equivalently the inductive (n−1)-Tucker on the boundary sphere), not
from raw circle/spoke parity. Consistent with Insight 3 (no single-set parity
invariant for n≥2), and complements PR #30917's `count_parity_not_invariant`
(full-triangulation count is mixed) with the sharper *universal* ring statement.

### Files Modified
- proofs/Proofs/SpernerTuckerBoundaryParity.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/knowledge.md

### Next Steps (n≥2 instantiation, crux is boundary parity)
- Geometric instantiation of the path-following engine: almost-complementary
  graph, degree ≤ 2, and `Odd #{boundary ends}` via inductive (n−1)-Tucker
  (NOT raw ring parity).
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-27 (researcher-3) — ACT: exact door-counting identity (parity → equation)

**Mode**: REVISIT (RICH; n=1 line + abstract n≥2 engines already verified). 
**Outcome**: progress (ACT) — strengthened `SpernerTuckerDoorIncidenceParity.lean`,
0 sorries, 0 axioms (propext/Classical.choice/Quot.sound; plain `decide`/`omega`, no
`native_decide`/`ofReduceBool`). Offline `LAKE_UNSAFE=1 ./bin/lake env lean` EXIT 0.

### What I Did
The incidence engine proved only the **mod-2** bridge
`#{odd-door cells} ≡ #{boundary doors}`. Upgraded it to the **exact integer identity**
underneath:
- `IsInteriorDoor d := cellCount d = 2` (+ Decidable instance).
- `sum_doorCount_eq_boundary_add_two_interior` : when every door touches one or two
  cells (`1 ≤ cellCount d ≤ 2`),
  `∑_c doorCount c = #{boundary doors} + 2·#{interior doors}` — each boundary door
  counted once (its single cell), each interior door twice (both cells). Reducing
  mod 2 kills the `2·…` term and recovers `card_odd_doorCount_modEq_card_boundaryDoor`.
- `card_interior_eq` : solving for interior doors,
  `2·#{interior} = ∑ doorCount − #{boundary}`.

### Key Findings / why it's the right strengthening
- The pre-existing results were all *parity* (`% 2` / `Odd` / `Even`) shadows of one
  exact count. The identity is the door-complex analogue of the handshaking *equation*
  `∑ deg = 2·#edges` generalised to allow degree-1 (boundary) doors: boundary doors are
  precisely the "odd" defect that the pure handshaking lemma cannot see.
- Makes the interior-door count a derived quantity, useful for the n≥2 Euler-type
  bookkeeping (boundary doors come from inductive (n−1)-Tucker; interior doors are then
  pinned by this equation).

### GOTCHAs
- `Finset.sum_ite` after rewriting the summand as `if IsBoundaryDoor … then 1 else 2`
  yields the boundary card via the *eta-expanded* predicate `fun d => IsBoundaryDoor inc d`
  whereas the goal's RHS uses `IsBoundaryDoor inc`; `ring` (not `omega`) closes the final
  `A + B*2 = A + 2*B` because it unifies the eta-differing card atoms up to defeq.
- The `¬ IsBoundaryDoor` filter equals the `IsInteriorDoor` filter only under
  `1 ≤ cellCount ≤ 2` (`Finset.filter_congr` + `omega`).

### Honest status
- Infrastructure / sharpening, NOT new Tucker mathematics: the n≥2 geometric
  instantiation (building the almost-complementary door complex and getting
  `Odd #{boundary doors}` from inductive (n−1)-Tucker) remains the genuine open lever,
  as flagged by every prior session. Value: turns the engine's parity output into an exact
  count and exposes the interior-door quantity.

### Files Modified
- proofs/Proofs/SpernerTuckerDoorIncidenceParity.lean (+2 theorems 8→10, +1 def 3→4, 217→280 lines; 0 axioms, 0 sorries)
- src/data/research/problems/sperner-mathlib4-oq-02.json (registered the file in leanFiles + currentState)

### Next Steps (unchanged genuine lever)
- n≥2 geometric door complex + `Odd #{boundary doors}` via inductive (n−1)-Tucker, then
  feed `exists_odd_doorCount_of_odd_boundary` → `SpernerTuckerPathFollowing`.

## Session 2026-06-27 (researcher-1) — ACT: the dimension recursion as an abstract induction

**Mode**: REVISIT (RICH; every single-level parity piece already verified).
**Outcome**: progress (ACT) — new `proofs/Proofs/SpernerTuckerInductiveTower.lean`
(231 LOC, 9 thm + 3 def + 1 structure, 0 sorry, 0 axiom). Verified offline via
`LAKE_UNSAFE=1 ./bin/lake env lean` against the main-repo Mathlib `.olean` cache
(Docker image still down). `#print axioms`: `odd_boundary_iff_odd_interior` and the
tower theorems depend only on propext/Classical.choice/Quot.sound — **no `sorryAx`,
no `Lean.ofReduceBool`**.

### What I Did
Every prior session named the same frontier in prose — "supply `Odd #{boundary
doors}` from inductive (n−1)-Tucker" — but the **induction on dimension itself** was
never formalized; the engine files are all single-level. This session writes that
recursion down and proves it closes.

- **`odd_boundary_iff_odd_interior` (engine, count form).** The path-following file's
  `exists_interior_degree_one` only extracted *one* interior endpoint. Here: in a
  max-degree-≤2 door graph, `Odd #{boundary endpoints} ↔ Odd #{interior endpoints}`,
  because the two classes **partition** the degree-1 vertices, whose total is even
  (`even_card_degree_one`). This is the quantitative statement the induction needs —
  an *odd interior count* that can propagate upward, not just a witness.
- **`TuckerTower` + `tower_interior_odd`.** A structure bundling per-level
  `boundary, interior : ℕ → ℕ` with three fields: `step` (the engine, discharged by
  the lemma above), `bridge` (`Odd (boundary (n+1)) ↔ Odd (interior n)` — the
  geometric boundary bijection, the SOLE open input), and `base` (`Odd (interior 0)`,
  the already-verified 1-D Tucker). Then `tower_interior_odd : ∀ n, Odd (interior n)`
  by a one-line induction (`Odd interior(n+1) ↔ Odd boundary(n+1) ↔ Odd interior(n)`
  via step/bridge/IH), and `tower_exists_interior : ∀ n, 0 < interior n` gives a
  complementary simplex in EVERY dimension.
- **`trivialTower`** — an inhabited tower (all counts 1) witnessing non-vacuity and
  showing the recursion computes.

### Why this matters
This pins down precisely what is left: **once the geometric `bridge` is supplied,
full-dimensional Tucker is a two-hypothesis induction** with both other inputs
already verified. It converts the recurring prose "next step" into a machine-checked
skeleton and tells the next session exactly one obligation to discharge geometrically
(`bridge`), rather than re-deriving the parity bookkeeping.

### Honest status
Infrastructure / organizing skeleton, NOT new Tucker mathematics. `step` is proved,
`base` is proved (n=1), and `bridge` — the geometric identification of level-`n`
boundary doors with level-`(n−1)` interior simplices — remains the genuine open
lever, exactly as every prior session flagged. Value: the dimension induction is now
explicit and verified, so the remaining work is a single, sharply-stated geometric
input.

### Files Modified
- proofs/Proofs/SpernerTuckerInductiveTower.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + currentState)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps (frontier now a single geometric obligation)
- Construct the concrete door complex for a triangulation of `Bⁿ` and supply
  `TuckerTower.bridge`: a parity-preserving bijection between level-`n` boundary
  doors and level-`(n−1)` interior complementary simplices. With `step` and `base`
  already verified, this alone yields full-dimensional Tucker via `tower_interior_odd`.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-28 (researcher-2) — realize the abstract tower from concrete door graphs

**Mode**: REVISIT (RICH). Frontier unchanged = the geometric `bridge` (level-`n`
boundary doors ↔ level-`(n−1)` interior simplices), a hard open construction.
**Outcome**: progress — extended `SpernerTuckerInductiveTower.lean` (+2 decls, still
0 sorry / 0 axiom; host `lake env lean` clean, all axioms foundational-only).

Added a **realization layer** showing the abstract `TuckerTower.step` field is never
an obligation once levels are realized by actual door graphs:
- `TuckerTower.ofGraphs`: builds a `TuckerTower` from a family `G : ∀n, SimpleGraph (V n)`
  (max degree ≤2) + boundary preds `B n`, discharging `step` via the engine
  `odd_boundary_iff_odd_interior`. Only `bridge` + `base` remain caller inputs.
- `exists_interior_of_graph_tower` (headline): given such a graph family with the
  geometric `bridge` and 1-D `base`, ∀n ∃ degree-1 interior vertex — Tucker's
  existence conclusion in EVERY dimension, in concrete graph terms, `step` eliminated.

GOTCHA: `(have T := ofGraphs …; T.interior n)` does NOT reduce — a local hyp of
structure type is opaque, so `Odd (T.interior n)` won't match `Odd #(interiorEndpoints …)`.
INLINE the `ofGraphs` application: `(TuckerTower.ofGraphs … ).tower_interior_odd n`
reduces the projection definitionally (ofGraphs is semireducible). 

This narrows the open surface from {step, bridge, base} to {bridge} (base verified at
n=1). Frontier for next session is STILL the single geometric `bridge` construction —
unchanged; this is organizing infrastructure, not new Tucker mathematics.
