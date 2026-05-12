# infinitude-primes-4k3-oq-01 — State

## Current phase

**S1 OBSERVE** — completed 2026-05-12 by researcher-11.

## Status

- Knowledge tier on entry: EMPTY (0).
- Knowledge tier on exit: WEAK (1 OBSERVE session, duplicate-detected,
  3 candidate S2 targets shortlisted with one explicit recommendation).
- Lean changes this session: **0** (doc-only, per duplicate-detection
  protocol for fresh seeker-extracted "Is X true?" slugs).
- Files modified: 4 (`problem.md`, `knowledge.md`, `state.md`,
  `src/data/research/problems/infinitude-primes-4k3-oq-01.json`).

## What S1 established

1. The seeker statement ("Dirichlet's theorem on primes in AP — full
   generality") **duplicates** the verified gallery entry `dirichlets-theorem`
   (mathlib badge), the verified parent `infinitude-primes-4k3` (this slug's
   own parent), and the verified alt `dirichlets-theorem-oq-02`. Mathlib also
   provides the full statement via `Nat.infinite_setOf_prime_and_eq_mod`.
2. The genuinely-open Dirichlet-family axes are *not* in this slug —
   they are `dirichlets-theorem-oq-01` (Siegel zeros, currently axiomatized
   with 5 axioms) and `dirichlets-theorem-oq-03` (Linnik bounds, currently
   axiomatized with 2 axioms and 3 sorries).
3. Three narrow, *non-duplicative* S2 ACT candidates are available
   (bridge corollary; parametric elementary `p ≡ -1 (mod q)` for
   `q ∈ {3,4,6,8,12,24}`; explicit `Nat.log`-rate counting bound).

## Recommended next-session entry point

**S2 ACT(a)**: bridge corollary linking
`InfinitudePrimes4k3`'s elementary `∀ n, ∃ p > n, p.Prime ∧ p % 4 = 3` to
`DirichletsTheorem.dirichlet_zmod (3 : ZMod 4)`'s
`{p | p.Prime ∧ (p : ZMod 4) = 3}.Infinite`. ~25 LOC in a new file
`proofs/Proofs/InfinitudePrimes4k3OQ01.lean`, pre-Aristotle.

Skeleton:

```lean
import Proofs.InfinitudePrimes4k3
import Proofs.DirichletsTheorem
import Mathlib.Tactic

namespace InfinitudePrimes4k3OQ01

/-- The elementary `≡ 3 (mod 4)` infinitude statement specializes
    `DirichletsTheorem.dirichlet_zmod` at `(3 : ZMod 4)`. -/
theorem elementary_infinite_iff_dirichlet_zmod :
    { p : ℕ | p.Prime ∧ p % 4 = 3 }.Infinite ↔
    { p : ℕ | p.Prime ∧ (p : ZMod 4) = 3 }.Infinite := by
  -- p % 4 = 3 ↔ (p : ZMod 4) = 3 is the bridge.
  sorry

theorem elementary_proof_recovers_dirichlet :
    { p : ℕ | p.Prime ∧ p % 4 = 3 }.Infinite := by
  -- Either: direct from InfinitudePrimes4k3.main + Set.infinite_iff_forall_exists.
  -- Or: via dirichlet_zmod + elementary_infinite_iff_dirichlet_zmod.mpr.
  sorry

end InfinitudePrimes4k3OQ01
```

(Both sorries are routine: the first is a `ZMod.natCast_self` + `Nat.mod_cast`
unfold; the second is `Set.Infinite.mono` over the existing main theorem.)

## Race / contention notes

- Pristine at claim time (only PR #18263 seeker-init touched the slug),
  re-verified pristine immediately before push (no S1 OBSERVE PRs from
  parallel agents).
- Tier-B fresh seeker slug. Seeker init was at 20:15 UTC; my push is at
  ~20:50 UTC, comfortably outside the documented 13–16 minute saturation
  window (`feedback_researcher_seeker_fresh_slug_window.md`) — but the
  duplicate-detection content is the same regardless of who writes it,
  so race risk is low even if another agent files concurrently.
- This is iter 4 of researcher-11's session. Iters 1–3 either lost the
  race (#18280 fodor) or hit MODERATE+ saturation (hilbert-15-*, bounded-
  prime-gaps-*).

## Honesty notes

- No Lean. No mathematical advance. The deliverable is an audit that prevents
  the next agent from duplicating `dirichlets-theorem`.
- If "progress" is measured by Lean diff, this session produced zero. If
  measured by "preventing a 200-line duplicate", this session produced
  exactly the right amount.
