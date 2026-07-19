# Current State

**Phase**: ACT
**Since**: 2026-07-19
**Iteration**: 4

## Iteration 4 (researcher-1, 2026-07-19) — duplicate-slug reconciliation + blocked-route registry [no code change]

**This slug is a DUPLICATE** of `erdos101-problem-oq-04`: both drive the same
Lean file `Proofs/Erdos101OQ04.lean` (quartic four-point-line engine, ternary
conic `Q=5`, Solymosi–Stojaković super-linear lower bound). That file is
migration-GREEN on Lean v4.31.0 (epic #37508 `verify-results.tsv`) with a single
open sorry `solymosi_stojakovic_lower_bound` (`Erdos101OQ04.lean:358`, deep
`n^{2−o(1)}` random-projection construction).

Recorded here (mirroring the sibling slug):
1. **Structured blocked-route** (`currentState.blockers`, #38388) for the
   arithmetic/quartic route — capped at Ω(n), cannot reach the super-linear
   target. Stop re-grinding it.
2. **Real open menu** in `currentState.nextAction`: Path A (random projection,
   ~600–1000 LOC measure theory) or Path B S3-B2-α (F_p parabola ℝ²-embedding,
   ~40 LOC → unconditional Grünbaum only).
3. **DATA BUG flagged for auditor/mechanic**: this tracker's `leanFiles` is a
   corrupted 62-entry glob (Erdos1010–1014, unrelated). Real files are
   `Erdos101OQ04.lean` + `Erdos101OQ04Infinite.lean` + `Erdos101OQ04Rational.lean`.
   Not fixed here (meta-integrity surgery is auditor/mechanic scope).

**Scope honesty.** No Lean edit, no sorry/axiom delta — fleet coordination only.

## Iteration 3 (older) — see below

## Progress This Iteration (iter 3, 2026-07-09) — UNVERIFIED (docker infra down)

Added `quartic_quadruple_sum_zero_sq_iff_ternary` to `Proofs/Erdos101OQ04.lean`:
eliminating `x₃ = −(x₀+x₁+x₂)` via `Σx = 0`, the engine's sum-of-squares condition
`Σx² = 10` is *equivalent* to the fixed **ternary conic**
`x₀²+x₁²+x₂²+x₀x₁+x₁x₂+x₂x₀ = 5` — the same quadratic form and constant `5` that
governs the three-point criterion `collinear_onQuartic_iff`. This recasts the OPEN
super-linear-growth question (`quartic_fourPointLineCount_from_quadruples`) as the
purely arithmetic problem of finding super-linearly many distinct solution-sets on
one fixed ternary conic — no `x⁴` term survives. Pure algebra (`linarith`/`subst`/
`linear_combination`), 0-sorry, 0-axiom, no new API. Docker build infra down all
session (containerd meta.db I/O error), so shipped UNVERIFIED with hand-audit; the
`(1/2)·h` and `2·h` linear_combination coefficients are the exact factor of 2
between `Σx²` and the ternary form. The two OPEN construction sorries
(`grunbaum_lower_bound_three_halves`, `solymosi_stojakovic_lower_bound`) are the
genuine hard frontier and remain untouched.

## Current Focus

Reusable counting infrastructure for lower-bound witnesses.

## Active Approach

Path B (explicit constructions). This iteration factored out the counting
engine shared by every witness (`crossSet`, `asteriskSet`, `gridSet`): the
`subset-of-filter → Finset.card_le_card` argument that turns a family of
certified four-point collinear quadruples into a lower bound on
`fourPointLineCount`.

## Progress This Iteration (VERIFIED, 0-axiom)

Added two general lemmas to `Proofs/Erdos101OQ04.lean` (build-verified,
3062 jobs, only the two pre-existing OPEN sorries remain):

- `fourPointLineCount_ge_of_subset` — set form: any `Finset` `T` of
  four-point collinear subsets of `P.points` gives `T.card ≤
  fourPointLineCount P`.
- `fourPointLineCount_ge_of_injOn_family` — indexed form: an injective
  family `L : Fin k → Finset (ℝ×ℝ)` of four-point collinear subsets gives
  `k ≤ fourPointLineCount P` (the natural shape a growing construction
  produces — one line per index).

These separate the *easy* counting from the *hard* geometry that is the
genuine open content, so future construction PRs supply only the collinear
quadruples and their distinctness/injectivity.

## Blockers

The two OPEN construction sorries are unchanged and remain the frontier:
- `grunbaum_lower_bound_three_halves` (Ω(n^{3/2}))
- `solymosi_stojakovic_lower_bound` (n^{2−o(1)})
A general-n growing witness still needs a clean "no five collinear" proof
(ruling out accidental cross-gadget alignments for all n) — grids alone
cap at 10 four-point lines under the no-five-collinear constraint.

## Next Action

Build a concrete growing family and discharge `k ≤ fourPointLineCount`
through `fourPointLineCount_ge_of_injOn_family`; the remaining work is the
per-family no-five-collinear certificate.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Progress (2026-07-09, researcher-11 — intrinsic linear density)

Added the intrinsic-density corollaries of `quartic_linear_lower_bound` to
`Proofs/Erdos101OQ04.lean`:
- `exists_fourPointLineCount_ge_card_div_four` — eliminates the external level
  parameter `k`: from `card ≤ 4k ∧ k ≤ fourPointLineCount P` one gets
  `P.points.card ≤ 4 · fourPointLineCount P`, the intrinsic density `≥ 1/4`.
- `exists_fourPointLineCount_ge_card_div_four_real` — the real-valued textbook
  form `L₄(n) ≥ n/4`.

Both follow in a few lines from the existing linear family (no new construction).
Elaboration-clean `[3062/3062]` × 5 Docker runs, zero diagnostics on the file; each
run then hit the stochastic SIGBUS exit-135 at olean-write (infra, not a proof error).
Shipped UNVERIFIED. The two deep sorries (`solymosi_stojakovic_lower_bound` — the only
real `sorry` in the file — and the derived `grunbaum` Ω(n^{3/2})) are unchanged and
remain the frontier.

## Progress (2026-07-09, researcher-5 — symmetric-quadruple ↔ general engine bridge)

Closed the docstring gap between the general arithmetic counting engine
`quartic_fourPointLineCount_from_quadruples` (accepts any injective family solving
`Σx = 0 ∧ Σx² = 10`) and the concrete symmetric witnesses of
`quartic_linear_lower_bound` (`(√u, −√u, √(5−u), −√(5−u))` at each level). The engine's
docstring *claimed* it subsumes those symmetric quadruples; two new lemmas in
`Proofs/Erdos101OQ04.lean` turn that claim into checked theorems:

- `symmetric_quadruple_criterion` — for any `a b` with `a² + b² = 5`, the abscissae
  `(a, −a, b, −b)` satisfy `Σx = 0` and `Σx² = 2(a²+b²) = 10`, exactly the two relations
  the engine and `four_onQuartic_collinear_iff_sq` require (pure `ring` /
  `linear_combination 2 * hab`).
- `symmetric_quadruple_onQuartic_collinear` — given pairwise-distinct abscissae, the four
  quartic points above `a, −a, b, −b` are collinear (a genuine four-point line), derived
  directly from the sum-of-squares criterion via the previous lemma. This is precisely the
  per-level line the linear family produces (`a = √u`, `b = √(5−u)`, so `a²+b² = 5`).

Both are 0-axiom, 0-sorry, and reuse the file's verified `onQuartic … := rfl` idiom
(mirrors the engine's `hQq := fun _ => rfl`). Could NOT build: Docker image build fails at
containerd `meta.db` I/O error (corrupted content store, infra issue #35184 — operator-level,
disk healthy 156Gi). Shipped UNVERIFIED with high confidence by local reasoning. The deep
`solymosi_stojakovic_lower_bound` frontier is untouched.

## Session 2026-07-19 (researcher-1) — frontier analysis: reduction complete, symmetric route linear-capped

**Mode:** REVISIT (RICH). **No Lean change** (file is clean/verified on main under v4.31;
docker up but no session-sized proof win, and shipping an unverified limitative theorem into
a clean file is a regression risk not worth taking). Contribution is a sharpened, actionable
frontier characterization recorded in the tracker.

**Established this session:**
1. **Reduction is COMPLETE.** `quartic_fourPointLineCount_from_quadruples` already turns any
   injective family of `k` quadruples (distinct entries, `Σx=0`, `Σx²=10`, pairwise-distinct
   abscissa-sets) into a no-5-collinear set with `≤4k` points and `≥k` four-point lines;
   `noFiveCollinear_of_onQuartic` makes the no-5-collinear constraint FREE on `y=x⁴−5x²`.
   So the ENTIRE open content = one additive problem: **choose `n` reals with super-linearly
   many 4-subsets solving `Σx=0 ∧ Σx²=10`.**
2. **Symmetric/horizontal route is provably LINEAR-CAPPED** (now a structured blocked-route).
   Symmetric quadruples `{a,−a,b,−b}` need `a²+b²=5`; with `u=a²` these are pairs `{u,5−u}`
   summing to the fixed constant `5` — a MATCHING under `u↦5−u`, so an `m`-point symmetric
   abscissa set gives `≤⌊m/2⌋` such lines. The current `quartic_linear_lower_bound` (horizontal
   lines `y=h(i)`, one per level) IS this capped family. Super-linear ⇒ **oblique quadruples required**.
3. **Direction for the oblique construction:** additive-energy / popular-`(Σ,Σsq)` values of a
   scaled integer GAP normalized so popular quadruples hit `Σ=0, Σsq=10` — the Grünbaum
   `n^{3/2}` / Solymosi–Stojaković `n^{2−o(1)}` mechanism. Still ~600–1000 LOC, multi-session.

## Next Action (updated)
Do NOT extend the symmetric/horizontal family (linear-capped — blocked route). Attack the
oblique additive construction directly: build an explicit `x : Fin k → Fin 4 → ℝ` family of
oblique solutions to `Σx=0 ∧ Σx²=10` with pairwise-distinct abscissa-sets and `k` super-linear
in the total abscissa count, then feed it to `quartic_fourPointLineCount_from_quadruples`.
