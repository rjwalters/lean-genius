# State — chebyshev-bounds-oq-04-oq-01

## Current phase

**Phase**: ACT (Iter 2 prime-value lemmas merged via PR #17690)
**Iteration**: 3 (Iter 3 in planning — Möbius–log identity for Λ₂)
**Since**: 2026-05-13T22:50:00Z (JSON resync; this state.md doc-only sync)

## Lean snapshot (post-Iter 2)

| File | LOC | Thm | Defs | Sorries | Axioms | Status |
|---|---:|---:|---:|---:|---:|---|
| `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` | 230 | 12 | 3 noncomputable | 0 | 0 | build-verified at Iter 2 merge |

Parent: `proofs/Proofs/ChebyshevBounds.lean` (carries the
`chebyshevPsi_asymptotic` axiom — the open target). OQ-04-OQ-01 is the
**elementary Selberg–Erdős 1949 PNT** approach to discharging that
axiom (no complex analysis).

## Iteration log

### Iter 2 — 2026-05-12 (PR #17690 merged)

**Result**: Closes the Iter 1 documented next-iteration deliverables
#1 and #2:

- `vonMangoldtConv_prime`: `(Λ ∗ Λ)(p) = 0` for prime `p`. Proof via
  `Nat.divisors_prime` + `Finset.sum_pair` + `vonMangoldt_apply_one`.
- `selbergLambda2_prime`: `Λ₂(p) = (log p)²` for prime `p`. Proof via
  `vonMangoldt_apply_prime`.

LOC delta: 206 → 230 (+24). Theorem count: 10 → 12. Sorries unchanged
(0). Axioms unchanged (0). PR #17690 also refreshed the gallery
`meta.json` description + `originalContributions` to mention Iter 2.

**Race note (post-merge cleanup deferred)**: PR #17689 ("Iter 2 —
prime values", different branch, OPEN+CONFLICTING since
2026-05-12T22:13Z) was a parallel attempt superseded by #17690 but
never closed. Decision to comment-close it deferred to maintainer.

### Iter 1 — 2026-05-09 (researcher-12, PR #17658 merged)

**Result**: OBSERVE-phase scaffold of the Selberg–Erdős strategy.

**Built** (`proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean`, 209 LOC):

- 3 noncomputable defs:
  - `vonMangoldtConv : ℕ → ℝ` — `Λ ∗ Λ` as a literal divisor sum
    (chosen over Mathlib's `ArithmeticFunction.mul` for cleaner
    algebraic rewrites downstream).
  - `selbergLambda2 : ℕ → ℝ` — `Λ(n) · log n + (Λ ∗ Λ)(n)`.
  - `selbergSum2 : ℕ → ℝ` — `Σ_{n ≤ N} Λ₂(n)`.
- 10 routine theorems: zero-value, one-value, non-negativity,
  successor-recursion, monotonicity (one per def).
- 0 sorries, 0 axioms.

Gallery entry `chebyshev-bounds-oq-04-oq-01` created (status
`formalized`, badge `wip`). File roadmap + Future Work sections
document the downstream Selberg symmetry formula + Erdős finishing
argument; the parent's `chebyshevPsi_asymptotic` axiom remains the
open target.

## Blockers

None. The Iter 3 task (Möbius–log identity) has clear Mathlib API
(`ArithmeticFunction.moebius_mul_coe_zeta`, `vonMangoldt_eq_log_mul_moebius`),
no exotic typeclass machinery needed.

## Next Action

**Iter 3 — Möbius–log identity**: prove

```
Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d)        (for n ≥ 1)
```

This is the central algebraic identity converting Selberg's elementary
PNT strategy into a Möbius manipulation problem. With this in hand,
Iter 4-6 then become:

- **Iter 4**: Selberg's symmetry formula
  `Σ_{n ≤ N} Λ₂(n) = 2N log N + O(N)` via summation by parts.
- **Iter 5**: Möbius hyperbola bound for the error term.
- **Iter 6**: Erdős finishing argument bridging
  `S₂(N) → ψ(N) ∼ N`, discharging `chebyshevPsi_asymptotic`.

Estimated 60-100 LOC for Iter 3. Mathlib readiness: high
(`ArithmeticFunction` namespace is well-developed in v4.26.0).

## Attempt Counts

- Total attempts: 2 (Iter 1, Iter 2)
- Current approach attempts: 2 (Selberg–Erdős elementary)
- Approaches tried: 1

## Race awareness (this STATE-SYNC)

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open` returns 1 OPEN PR (#17689, CONFLICTING since 2026-05-12T22:13Z, superseded by merged #17690). This STATE-SYNC touches only `state.md` + `lastUpdate` JSON; no Lean / gallery / candidate-pool changes. No file overlap with #17689.

## STATE-SYNC notes

This entry is a doc-only tracker resync (no Lean, no gallery JSON
beyond `lastUpdate`). The slug's `currentState` in
`src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json` already
held accurate Iter 1 + Iter 2 progress as of 2026-05-13T22:50Z; this
sync brings `state.md` (which was the seeker-init "Phase: NEW since
2026-05-08" stub) up to parity. Pattern: `feedback_researcher_state_sync_active_thread_prep_backlog.md`.
