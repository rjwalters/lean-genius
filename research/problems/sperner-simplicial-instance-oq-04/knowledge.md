# sperner-simplicial-instance-oq-04

**Open question.** Build a Brouwer-fixed-point theorem on top of the 1-d Sperner
lemma (`interval_sperner`): combine it with a barycentric-mesh refinement and a
continuous-coloring → Sperner-coloring reduction to derive Brouwer for `[0,1]^n`.
The interval case yields the discrete intermediate-value theorem and a Lean proof
of `|f(x₀)| → 0` for any continuous `f : [0,1] → [-1,1]` with `f(0) ≤ 0 ≤ f(1)`.

## Decomposition

| Part | Content | Status | Size |
|------|---------|--------|------|
| (a) | Discrete sign-change for real `f` (continuous-coloring → Sperner-coloring reduction) | **DONE (this session)** | ~90 lines |
| (b) | Continuous 1-d IVT via mesh refinement + Bolzano–Weierstrass | OPEN, tractable | ~150 lines |
| (c) | `n`-d Brouwer via barycentric subdivision + `sperner-ndim` | BLOCKED | >1000 lines |

The **discrete IVT itself** (`c(0) ≠ c(m) ⟹ ∃` panchromatic cell) was already
proven in the sibling `SpernerSimplicialInstanceOQ05Scarf1d.lean`
(`discrete_ivt_panchromatic_cell`). oq-04 only adds the real-function reduction
layer on top of it; there is no new combinatorics in part (a).

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

## Session 2026-07-04 (researcher-5) - Gallery landing of the interval case

**Mode**: REVISIT (FRESH claim of an `available` pool problem, RICH knowledge tier)
**Outcome**: completed (interval-case deliverable)

### What I Did
- Verified the interval-case proof `proofs/Proofs/SpernerSimplicialInstanceOQ04.lean`
  compiles: `docker-build.sh Proofs.SpernerSimplicialInstanceOQ04` → `✔ Built ... (7.3s)`,
  0 sorries / 0 axioms / no native_decide. (The prior S1 "blackout" note is resolved;
  S2/researcher-7 had already added the continuous limit `ivt_of_shrinking_brackets` +
  `exists_root_of_continuous`, so the file is the *complete* 1-d chain.)
- Discovered the file was **orphaned**: no `src/data/proofs/` gallery entry, and the old
  "UNREGISTERED in Proofs.lean" concern is moot — `Proofs.lean` is now empty of imports and
  modules are auto-discovered by the Lake `globs` directive, so the file already builds in CI.
- Created the gallery entry `src/data/proofs/sperner-simplicial-instance-oq-04/`:
  - `meta.json` (verified/original badge, 0 axioms, 4 thm + 5 lemma + 2 def, 206 lines,
    full overview / proofStrategy / keyInsights / crossReferences / sections).
  - `annotations.json` (5 annotations across the header, reduction, discrete IVT, analytic
    limit, and continuous IVT).
  - Both pass `pnpm annotations:validate` (entry-clean) and `gallery:check-size:strict`.
- Advanced phase ACT → COMPLETED; pool status → completed.

### Key Findings
- The verified result was already on `main` (PR #33652) but invisible in the web gallery for
  want of a `src/data/proofs/` entry — the meaningful progress this session is surfacing it.
- Honest scope confirmed: this closes the **interval (1-d)** case named in OQ-04; the
  n-dimensional Brouwer via barycentric subdivision stays BLOCKED (>1000 lines absent from
  Mathlib) and is now recorded as an `openQuestion` in the entry rather than attempted.

### Files Modified
- `src/data/proofs/sperner-simplicial-instance-oq-04/meta.json` (new)
- `src/data/proofs/sperner-simplicial-instance-oq-04/annotations.json` (new)
- `src/data/research/problems/sperner-simplicial-instance-oq-04.json` (knowledge, phase)

### Next Steps
1. 1-d fixed-point corollary: `exists_root_of_continuous` on `f = g − id` ⟹ Brouwer-in-1-d
   for continuous `g : [0,1] → [0,1]` (few lines).
2. Quantitative bisection variant of `ivt_of_shrinking_brackets` (explicit modulus).
3. n-d Brouwer: keep BLOCKED.
