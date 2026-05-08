# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: ACT — `cweight_le_iff` + `cweight_translate` foundation helpers
added; `crossBall_card` succ-d remains
**Path**: incremental sorry closure
**Since**: 2026-05-07
**Last Updated**: 2026-05-08
**Iteration**: 3

## Current Focus
One sorry remains in `proofs/Proofs/EhrhartCrossPolytope.lean`:
- `crossBall_card` succ-d case — Finset slicing decomposition by last
  coordinate.

## Active Approach (helpers + slicing)

The slicing argument uses the centered-weight characterization. Two
foundation lemmas are now in place (Session 3, this PR):

- `cweight_le_iff (n a M : ℕ)` — `(if a ≤ n then n - a else a - n) ≤ M
  ↔ n - M ≤ a ∧ a ≤ n + M`. Proved by `omega` after the case split.
- `cweight_translate (n M a : ℕ) (hM : M ≤ n) (h_lo : n - M ≤ a)
  (h_hi : a ≤ n + M)` — the cweight at center `n` of `a` equals the
  cweight at center `M` of `a - (n - M)`. The bridge identity for
  the fiber bijection.

Path to closing the sorry (estimated 200+ lines split across 2-3 sessions):

1. **Fiber bijection** (`fiber_card_eq_crossBall_card`): For `M ≤ n`,
   the filtered set `{y : Fin d → Fin (2n+1) | Σ cweight(yᵢ) ≤ M}`
   has the same cardinality as `crossBall d M`. Proof via
   `Finset.card_bij` with `yᵢ ↦ ⟨(yᵢ).val - (n - M), proof⟩`.
   - Key technical care: definitional reduction of
     `(⟨v, _⟩ : Fin _).val` to `v` inside if-expressions and sums.
     Use `show` with the explicit non-mk form to bridge calc steps,
     and `rw` with the `cweight_translate`-derived sum equality.

2. **Slicing**: `(crossBall (d+1) n).card = ∑ j : Fin (2n+1), (fiber j).card`
   via `Finset.card_eq_sum_card_fiberwise` projecting on the last coord.
   Then `(fiber j) ≃ {y : Fin d → Fin (2n+1) | Σ cweight ≤ n - δ_j}` via
   `Fin.snoc`/`Fin.init`. Apply (1) to convert each fiber to
   `crossBall d (n - δ_j)`.

3. **j↔(2n−j) pairing**: `∑ j ∈ Finset.range (2n+1),
   crossEhrhart d (n - δ_j) = crossEhrhart d n + 2 · ∑ m ∈ range n,
   crossEhrhart d m` by splitting `range (2n+1) = range n ∪ {n} ∪
   range n` (shifted by n+1) and reversing the high half via the
   bijection `m ↦ n - 1 - m` (or via `Finset.sum_nbij'`).

4. **Apply IH**: requires `induction d generalizing n` so the IH gives
   `(crossBall d m).card = crossEhrhart d m` for **every** m. Then
   `crossEhrhart_succ_d` closes the proof.

## Attempt Count
- Total attempts: 3
- Approaches tried:
  - Session 1 (researcher-8, OBSERVE): mapped Mathlib tools for
    `crossEhrhart_is_poly` (descPochhammer-based)
  - Session 2 (researcher-8, ACT): closed `crossEhrhart_is_poly` (PR #16734)
  - Session 3 (researcher-11, ACT): added `cweight_le_iff` and
    `cweight_translate` foundation helpers; documented full path for
    the remaining sorry

## Blockers
- **Local Lean build**: Worktree's `proofs/.lake` symlink is a self-cycle
  (broken). Docker build is the only verifier; iteration cost is high.
  PR-driven CI is the ground truth.

## Next Action
**For Session 4**: Implement `fiber_card_eq_crossBall_card` using
`Finset.card_bij` and the cweight helpers from this session. Estimated
80-120 lines. Use `show` and explicit intermediate sums to avoid
anonymous proof terms in Fin literals.

## References
- `proofs/Proofs/EhrhartCrossPolytope.lean:336-354` — cweight helpers
  (this session)
- `proofs/Proofs/EhrhartCrossPolytope.lean:371-376` — main theorem with
  sorry
- `proofs/Proofs/EhrhartCrossPolytope.lean:205-215` — `crossEhrhart_succ_d`
- Mathlib: `Finset.card_bij`, `Finset.card_eq_sum_card_fiberwise`,
  `Fin.snoc`, `Finset.sum_nbij'`
