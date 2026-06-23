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
