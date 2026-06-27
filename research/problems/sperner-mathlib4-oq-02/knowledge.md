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
