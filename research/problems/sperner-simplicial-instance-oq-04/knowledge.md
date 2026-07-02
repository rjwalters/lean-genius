# sperner-simplicial-instance-oq-04

**Open question.** Build a Brouwer-fixed-point theorem on top of the 1-d Sperner
lemma (`interval_sperner`): combine it with a barycentric-mesh refinement and a
continuous-coloring → Sperner-coloring reduction to derive Brouwer for `[0,1]^n`.
The interval case yields the discrete intermediate-value theorem and a Lean proof
of `|f(x₀)| → 0` for any continuous `f : [0,1] → [-1,1]` with `f(0) ≤ 0 ≤ f(1)`.

## Decomposition

| Part | Content | Status | Size |
|------|---------|--------|------|
| (a) | Discrete sign-change for real `f` (continuous-coloring → Sperner-coloring reduction) | **DONE (S1)** | ~90 lines |
| (b) | Continuous 1-d IVT via mesh refinement + Bolzano–Weierstrass | **DONE (S2), VERIFIED 0-axiom** | ~86 lines |
| (c) | `n`-d Brouwer via barycentric subdivision + `sperner-ndim` | BLOCKED | >1000 lines |

The **discrete IVT itself** (`c(0) ≠ c(m) ⟹ ∃` panchromatic cell) was already
proven in the sibling `SpernerSimplicialInstanceOQ05Scarf1d.lean`
(`discrete_ivt_panchromatic_cell`). oq-04 only adds the real-function reduction
layer on top of it; there is no new combinatorics in part (a).

## Session 2026-07-02 (Session 2) — Continuous 1-d IVT via the discrete bridge (part b)

**Mode**: REVISIT · **Outcome**: progress (ACT) · **Status**: VERIFIED, 0-axiom

### What I Did
- Added `continuous_ivt_of_bridge` to `proofs/Proofs/SpernerSimplicialInstanceOQ04.lean`
  (part (b) of the decomposition): for continuous `f : ℝ → ℝ` with `f 0 ≤ 0 ≤ f 1`,
  there is `x ∈ [0,1]` with `f x = 0`. **Derived through the discrete Sperner
  bracket**, not Mathlib's `intermediate_value_Icc`:
  1. `exists_sign_change_bracket` gives, for each mesh `m = n+1`, a bracket
     `[aₙ, bₙ] ⊆ [0,1]` with `bₙ - aₙ = 1/(n+1)` and `f(aₙ)·f(bₙ) ≤ 0`
     (packaged with `choose`).
  2. `IsCompact.tendsto_subseq` on `Set.Icc 0 1` extracts `a_{φ k} → x*`.
  3. `bₙ - aₙ → 0` (via `tendsto_one_div_add_atTop_nhds_zero_nat ∘ φ.tendsto_atTop`)
     ⟹ `b_{φ k} → x*` (`Tendsto.congr` on the sum).
  4. `Continuous.tendsto` passes both limits through; `le_of_tendsto` on the
     eventually-nonpositive product forces `f(x*)² ≤ 0`, hence `f x* = 0`
     (`mul_self_eq_zero`).
- Degenerate `f 1 = 0` handled separately (root at `x = 1`), so the statement is
  the clean `f 0 ≤ 0 ≤ f 1` hypothesis.

### Verification
- Compiled with `lean` (toolchain v4.26.0) against project Mathlib oleans
  (docker/lake unusable this session: `.loom` + `/private/tmp` worktrees were
  being reaped concurrently, and the deployer-branch `packages/mathlib` is not a
  git repo so docker forces a destructive re-clone).
- `#print axioms continuous_ivt_of_bridge` → `[propext, Classical.choice,
  Quot.sound]` only. No `sorry`, no `axiom`, no `Lean.ofReduceBool`. **Genuinely
  verified / 0-axiom.**

### Key Findings
- The whole 1-d Sperner→root chain (discrete IVT → continuous IVT) is now
  machine-checked. The Sperner content lives entirely in part (a); part (b) is
  the standard `m → ∞` compactness/continuity limit, but it is threaded *through*
  the discrete bracket rather than shortcutting to `intermediate_value_Icc`.
- `Continuous.tendsto x` (not `ContinuousAt`) composes cleanly with the
  subsequence limit; `le_of_tendsto` + `filter_upwards` is the tidy way to pass a
  pointwise `≤ 0` to the limit.

### Files Modified
- `proofs/Proofs/SpernerSimplicialInstanceOQ04.lean` (+86 lines: `continuous_ivt_of_bridge`)
- `research/problems/sperner-simplicial-instance-oq-04/knowledge.md`
- `src/data/research/problems/sperner-simplicial-instance-oq-04.json`

### Next Steps
1. Part (c) `n`-d Brouwer remains BLOCKED (>1000 lines: barycentric subdivision +
   `sperner-ndim` d-simplex triangulation + mesh shrinking on `[0,1]^n`).
2. Optional: a gallery entry for oq-04 (parent + oq-05 already have entries); the
   discrete+continuous 1-d IVT is now a coherent verified deliverable.

## Session 2026-06-15 (Session 1) — Continuous-coloring reduction (interval case)

**Mode**: FRESH · **Outcome**: progress (ACT, build-pending)

### What I Did
- Built `proofs/Proofs/SpernerSimplicialInstanceOQ04.lean` (no `sorry`, no `axiom`):
  - `meshPt m j = j / m`, `signColoring f m j = if f (j/m) ≤ 0 then 0 else 1`
    — the explicit continuous-coloring → Sperner-coloring reduction.
  - `signColoring_zero` / `signColoring_self`: endpoints are `0` / `1` from
    `f 0 ≤ 0` and `0 < f 1`.
  - `exists_sign_change_cell`: for every mesh `m > 0` there is a cell `i : Fin m`
    whose mesh endpoints `i/m`, `(i+1)/m` straddle a sign change of `f`. Proven by
    feeding `signColoring` to `OQ05Scarf1d.discrete_ivt_panchromatic_cell`.
  - `exists_sign_change_bracket`: product form `f(a)·f(b) ≤ 0`.
- Numerical certificate `verify_sperner_oq04_bridge.py` (3 test functions, incl.
  transcendental root `x − cos x` and an irrational cubic root): the sign-change
  cell exists and brackets a true root for every mesh `m ∈ {1,…,65536}`, with
  `|f(midpoint)| → 0` at rate `≤ L·(1/m)`.

### Key Findings
- The discrete statement is continuity-free; continuity is only needed for the
  `m → ∞` limit to an exact root.
- Mathlib already has Brouwer and all the limit ingredients
  (`tendsto_subseq_of_bounded`, `Continuous.continuousAt`), but no Sperner→Brouwer
  bridge — the value here is the explicit derivation chain, not new Mathlib infra.

### Files Modified
- `proofs/Proofs/SpernerSimplicialInstanceOQ04.lean` (new, UNREGISTERED in Proofs.lean)
- `research/problems/sperner-simplicial-instance-oq-04/verify_sperner_oq04_bridge.py` (new)
- `src/data/research/problems/sperner-simplicial-instance-oq-04.json` (knowledge)

### Next Steps
1. Prove continuous 1-d IVT from `exists_sign_change_bracket` (part b): convergent
   subsequence of bracket left-ends on `[0,1]` + continuity ⟹ `f(x*) = 0`.
2. Keep part (c) (`n`-d Brouwer) BLOCKED until (b) lands.
3. Verify the build once the docker backend recovers; then register in `Proofs.lean`.

### Blackout note
Docker build backend hung (header printed, no progress in 90 s); Aristotle not
used (discrete part is elementary). File deliberately left out of `Proofs.lean`
so a non-compiling file cannot break the auto-merged `main` build.
