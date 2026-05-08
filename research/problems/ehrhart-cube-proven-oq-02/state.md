# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: ACT — Mathlib API drift fix (S6); 1 sorry remains
**Path**: incremental sorry closure
**Since**: 2026-05-07
**Last Updated**: 2026-05-08
**Iteration**: 6

## Current Focus
One sorry remains in `proofs/Proofs/EhrhartCrossPolytope.lean`:
- `crossBall_card` succ-d case — slicing decomposition that uses
  `fiber_card_eq_crossBall_card` (this session) once fibers are
  identified with the filter-set form.

## Active Approach (helpers + slicing)

The slicing argument uses the centered-weight characterization. Five
foundation lemmas are now in place:

- `cweight_le_iff (n a M : ℕ)` — `(if a ≤ n then n - a else a - n) ≤ M
  ↔ n - M ≤ a ∧ a ≤ n + M`. (Session 3)
- `cweight_translate (n M a : ℕ) (hM : M ≤ n) (h_lo : n - M ≤ a)
  (h_hi : a ≤ n + M)` — bridge identity; cweight at center `n` of `a`
  equals cweight at center `M` of `a - (n - M)`. (Session 3)
- `cweight_sum_individual {d n M} (y) (hsum) (j)` — sum bound implies
  individual bound. (Session 4)
- `cweight_sum_range {d n M} (hM) (y) (hsum) (j)` — sum bound + `M ≤ n`
  forces `(y j).val ∈ [n - M, n + M]`. (Session 4)
- `fiber_card_eq_crossBall_card (d n M : ℕ) (hM : M ≤ n)` — the cardinality
  identity: `{y : Fin d → Fin (2n+1) | Σ cweight(y, n) ≤ M}` is in bijection
  with `crossBall d M`, via `yᵢ ↦ ⟨(yᵢ).val - (n - M), _⟩`. (Session 4,
  via `Finset.card_bij'`, ~80 lines.)

## Path to closing the remaining sorry

1. **Slicing** (the rest of `crossBall_card` succ-d, ≈80–120 lines):
   `(crossBall (d+1) n).card = ∑ j : Fin (2n+1), (fiber j).card`
   via `Finset.card_eq_sum_card_fiberwise` projecting on the last coord.
   For each `j`, the fiber is in bijection with the filter-set used by
   `fiber_card_eq_crossBall_card` for `M_j = if j.val ≤ n then j.val
   else 2n - j.val` (= `n - cweight(j, n)`). Apply
   `fiber_card_eq_crossBall_card d n M_j (by omega)` to get
   `(fiber j).card = (crossBall d M_j).card`.
   - The fiber-to-filter-set bijection itself is via `Fin.snoc` /
     `Fin.init`: drop the last coordinate, and the remaining d
     coordinates satisfy the cweight-sum-bound at center `n` with
     budget `M_j`.

2. **j↔(2n−j) pairing**: `∑ j ∈ Finset.range (2n+1),
   crossEhrhart d (n - cweight(j, n)) = crossEhrhart d n + 2 · ∑ m ∈ range n,
   crossEhrhart d m` by splitting `range (2n+1) = range n ∪ {n} ∪
   range n` (shifted by `n+1`) and reversing the high half via the
   bijection `m ↦ n - 1 - m` (or via `Finset.sum_nbij'`).

3. **Apply IH**: requires `induction d generalizing n` so the IH gives
   `(crossBall d m).card = crossEhrhart d m` for **every** m. Then
   `crossEhrhart_succ_d` closes the proof.

## Attempt Count
- Total attempts: 6
- Approaches tried:
  - Session 1 (researcher-8, OBSERVE): mapped Mathlib tools for
    `crossEhrhart_is_poly` (descPochhammer-based)
  - Session 2 (researcher-8, ACT): closed `crossEhrhart_is_poly` (PR #16734)
  - Session 3 (researcher-11, ACT): added `cweight_le_iff` and
    `cweight_translate` foundation helpers
  - Session 4 (researcher-9, ACT): added `cweight_sum_individual`,
    `cweight_sum_range`, and `fiber_card_eq_crossBall_card` (via
    `Finset.card_bij'`)
  - Session 5 (researcher-12, ORIENT): wrote slicing decomposition spec
    (`session-5-slicing-spec.md`); deferred Lean prototype
  - Session 6 (researcher-1, ACT): **Mathlib API drift fix**. After
    deleting the broken `proofs/.lake` self-symlink and running the
    Docker build, found that origin/main no longer compiles due to
    Mathlib API drift since PR #16734 / #17008 merged unverified.
    Three fixes restored buildability:
    (a) `Polynomial.descPochhammer` → `descPochhammer` (5 refs);
        `Polynomial.descPochhammer_succ_right` → `descPochhammer_succ_right` (2 refs).
        `descPochhammer` lives at the root namespace (after `open Polynomial`),
        not inside `namespace Polynomial`.
    (b) Removed redundant `ring` after `field_simp [hk_ne]` in
        `crossEhrhart_is_poly` (field_simp now closes the goal directly).
    (c) Added explicit `Fin (2 * M + 1)` and `Fin (2 * n + 1)` type
        annotations to the Forward/Backward bijection lambdas inside
        `Finset.card_bij'` for `fiber_card_eq_crossBall_card`. Without
        the annotations, Lean's elaborator failed to fix the lambda's
        codomain, leaving the Fin-bound proof obligation unmaterialized
        ("No goals to be solved" at the inner `by` block) and leaving
        a stray metavariable inside the post-`simp only [crossBall, ...]`
        sum body ("show tactic failed: pattern not definitionally equal"
        with `↑?m.56` on the target side).
    Also bumped `is_lt` → `isLt` (cosmetic; both work).
    Build verified: `./proofs/scripts/docker-build.sh Proofs.EhrhartCrossPolytope`
    in worktree `researcher-1`, exit 0, 1 sorry / 0 axioms / 538 lines.

## Blockers
- **Local Lean build**: The recursive self-symlink at
  `/Users/rwalters/GitHub/lean-genius/proofs/.lake` (and the inherited
  symlink in fresh worktrees) blocks Docker builds. Workaround:
  `rm proofs/.lake` in the worktree and let the container clone Mathlib
  fresh — adds ~10 min for clone + ~5 min for cache get on first use,
  then incremental builds are ~2 min.

## Next Action
**For Session 7**: Resume the slicing decomposition prototype from
`session-5-slicing-spec.md` §4-6 on top of the now-buildable
origin/main. The S6 prototype committed to local branch
`research/ehrhart-cube-proven-oq-02-fiber-bij-1778229307`
(`4e9853d0510`) adds `crossBall_succ_d_fiber_card` (~80 lines),
`crossBall_succ_d_slice` (~10 lines), `sum_crossBall_pair` (~55 lines)
and the `crossBall_card` wire-in (~6 lines). When pulled into a fresh
build it will surface its own Mathlib-drift issues
(`Finset.card_eq_sum_card_fiberwise` MapsTo vs `∀ x ∈ s, f x ∈ t`,
`Fin.snoc_last` arg order, possible `change`/`omega` interactions on
opaque sums) which will likely need fixes similar to Session 6.

## References
- `proofs/Proofs/EhrhartCrossPolytope.lean:336-354` — cweight bridge
  helpers (Session 3)
- `proofs/Proofs/EhrhartCrossPolytope.lean:356-374` — sum-bound helpers
  (Session 4)
- `proofs/Proofs/EhrhartCrossPolytope.lean:376-468` — fiber bijection
  (Session 4)
- `proofs/Proofs/EhrhartCrossPolytope.lean:485-490` — main theorem
  with sorry
- `proofs/Proofs/EhrhartCrossPolytope.lean:205-215` — `crossEhrhart_succ_d`
- Mathlib: `Finset.card_bij'`, `Finset.card_eq_sum_card_fiberwise`,
  `Fin.snoc`, `Finset.sum_nbij'`
