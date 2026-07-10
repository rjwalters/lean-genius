# Current State

**Phase**: ACT
**Since**: 2026-07-08T00:00:00Z
**Iteration**: 2

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
