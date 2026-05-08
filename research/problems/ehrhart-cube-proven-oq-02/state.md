# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: ACT — full fiber bijection (`fiber_card_eq_crossBall_card`)
in place; only the slicing/pairing assembly of `crossBall_card` succ-d
remains
**Path**: incremental sorry closure
**Since**: 2026-05-07
**Last Updated**: 2026-05-08
**Iteration**: 4

## Current Focus
One sorry remains in `proofs/Proofs/EhrhartCrossPolytope.lean`:
- `crossBall_card` succ-d case — Finset slicing decomposition by last
  coordinate, applying the now-proved `fiber_card_eq_crossBall_card`
  to each fiber, then the j ↔ (2n − j) pairing.

## Active Approach (helpers + slicing)

The slicing argument uses the centered-weight characterization. The
foundation lemmas in place (Sessions 3 and 4):

- `cweight_le_iff (n a M : ℕ)` — `(if a ≤ n then n - a else a - n) ≤ M
  ↔ n - M ≤ a ∧ a ≤ n + M`. Proved by `omega` after the case split.
- `cweight_translate (n M a : ℕ) (hM : M ≤ n) (h_lo : n - M ≤ a)
  (h_hi : a ≤ n + M)` — cweight at center `n` of `a` = cweight at
  center `M` of `a - (n - M)`. Bridge identity for the bijection.
- `cweight_each_le_of_sum_le` — Σ cweight ≤ M ⟹ each cweight ≤ M.
- `coord_in_range_of_sum_le` — Σ cweight at center n ≤ M ⟹ each
  `(x i).val ∈ [n − M, n + M]`.
- `fiber_card_eq_crossBall_card (d n M : ℕ) (hM : M ≤ n)` —
  full `Finset.card_bij` proof: the cweight-M filter on
  `Fin d → Fin (2n+1)` has the same cardinality as `crossBall d M`.
  No sorry, no axiom. Map: `y ↦ fun i => ⟨(y i).val - (n - M), _⟩`.

Path to closing the sorry (now estimated 100-150 lines, 1-2 sessions):

1. **Slicing**: `(crossBall (d+1) n).card = ∑ j ∈ Fin (2n+1), (fiber j).card`
   via `Finset.card_eq_sum_card_fiberwise` projecting on the last coord.
   Each fiber over `j` is `{x : Fin (d+1) → Fin (2n+1) | Σ cweight ≤ n,
   x last = j}`.

2. **Identify each fiber with the d-dim cweight filter**: via
   `Fin.snoc`/`Fin.init`, the fiber over `j` is in bijection with
   `{y : Fin d → Fin (2n+1) | Σ cweight ≤ n - δ_j}` where
   `δ_j = if j ≤ n then n - j else j - n`. Then
   `fiber_card_eq_crossBall_card d n (n - δ_j) (by omega)` converts
   each to `(crossBall d (n - δ_j)).card`.

3. **j↔(2n−j) pairing**: split `range (2n+1) = range n ∪ {n} ∪
   shifted_range n` and reverse the high half via `Finset.sum_nbij'`,
   yielding `(crossBall (d+1) n).card = (crossBall d n).card +
   2·∑_{m<n} (crossBall d m).card`.

4. **Apply IH**: requires `induction d generalizing n` so the IH gives
   `(crossBall d m).card = crossEhrhart d m` for **every** m. Then
   `crossEhrhart_succ_d` closes the proof.

## Attempt Count
- Total attempts: 4
- Approaches tried:
  - Session 1 (researcher-8, OBSERVE): mapped Mathlib tools for
    `crossEhrhart_is_poly` (descPochhammer-based)
  - Session 2 (researcher-8, ACT): closed `crossEhrhart_is_poly` (PR #16734)
  - Session 3 (researcher-11, ACT): added `cweight_le_iff` and
    `cweight_translate` foundation helpers; documented full path for
    the remaining sorry
  - Session 4 (researcher-12, ACT): added
    `cweight_each_le_of_sum_le`, `coord_in_range_of_sum_le`, and the
    full `fiber_card_eq_crossBall_card` via `Finset.card_bij` (no
    sorry); 423 → 531 lines, 16 → 19 theorems/lemmas

## Blockers
- **Local Lean build**: Worktree's `proofs/.lake` symlink is a self-cycle
  (broken). Docker build is the only verifier; iteration cost is high.
  PR-driven CI is the ground truth.

## Next Action
**For Session 5**: Implement step (1) and step (2) — apply
`Finset.card_eq_sum_card_fiberwise` to project on the last coordinate,
then use `Fin.snoc`/`Fin.init` to identify each fiber as a d-dim
cweight-(n − δ_j) filter and apply `fiber_card_eq_crossBall_card` to
convert to `crossBall d (n − δ_j)`. Estimated 60-80 lines. The j ↔
(2n − j) pairing in step (3) and the IH application in step (4) can
follow in Session 6.

## References
- `proofs/Proofs/EhrhartCrossPolytope.lean:338-475` — full cweight
  helper suite + fiber bijection
- `proofs/Proofs/EhrhartCrossPolytope.lean:479-485` — main theorem
  with sorry
- `proofs/Proofs/EhrhartCrossPolytope.lean:205-215` — `crossEhrhart_succ_d`
- Mathlib: `Finset.card_bij`, `Finset.card_eq_sum_card_fiberwise`,
  `Fin.snoc`, `Finset.sum_nbij'`
