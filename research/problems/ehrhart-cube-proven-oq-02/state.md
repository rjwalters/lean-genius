# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: ACT — slicing decomposition prototype written; build verification pending
**Path**: incremental sorry closure
**Since**: 2026-05-07
**Last Updated**: 2026-05-08
**Iteration**: 6

## Current Focus
S6 prototype landed: three new private lemmas implementing the slicing
decomposition spec from `session-5-slicing-spec.md`. The remaining `sorry`
in `crossBall_card` succ-d is closed by the prototype, but the file has
**not yet been verified** with a Docker build (`.lake` symlink remains a
recursive self-cycle on the host; one full build is ~45–55 min).

## S6 Prototype (this session, researcher-6)

Three new private lemmas added to `proofs/Proofs/EhrhartCrossPolytope.lean`
between `fiber_card_eq_crossBall_card` and `crossBall_card`:

1. **`crossBall_succ_d_fiber_card (d n : ℕ) (j : Fin (2*n+1))`**
   (≈80 lines) — per-fiber cardinality identity. The fiber of
   `crossBall (d+1) n` over the last coordinate `j` has card equal to
   `(crossBall d M_j).card` where
   `M_j := if j.val ≤ n then j.val else 2n - j.val`.
   Proof: bijection via `Fin.init` / `Fin.snoc · j`, bridged through
   `fiber_card_eq_crossBall_card` (S4) at budget `M_j`. The key arithmetic
   identity `cweight(j, n) + M_j = n` is proved inline by `omega` and used
   to relate the `Σ over Fin(d+1)` and the `Σ over Fin d + cweight(j, n)`
   forms via `Fin.sum_univ_castSucc`.

2. **`crossBall_succ_d_slice (d n : ℕ)`** (≈10 lines) — Step A. Slicing
   identity: `(crossBall (d+1) n).card = ∑ j : Fin (2n+1), (crossBall d M_j).card`.
   Proof: `Finset.card_eq_sum_card_fiberwise` projecting on the last
   coordinate, then `crossBall_succ_d_fiber_card` applied per fiber.

3. **`sum_crossBall_pair (d n : ℕ)`** (≈55 lines) — Step B. Sum
   reorganization via the j↔2n-j pairing:
   `∑ j : Fin (2n+1), (crossBall d M_j).card = (crossBall d n).card + 2 · ∑ m ∈ range n, (crossBall d m).card`.
   Proof: convert `∑ j : Fin (2n+1)` to `∑ k ∈ range (2n+1)`, split
   `range (2n+1) = range (n+1) ∪ Ico (n+1) (2n+1)`, simplify the if on
   each piece, reindex `m := 2n - k` on the high half via
   `Finset.sum_nbij'`, peel off the `k = n` term, combine with `ring`.

The `crossBall_card` `succ d` case is now:

```lean
| succ d ih =>
  rw [crossBall_succ_d_slice, sum_crossBall_pair, ih n]
  rw [show (∑ m ∈ Finset.range n, (crossBall d m).card)
        = ∑ m ∈ Finset.range n, crossEhrhart d m
      from Finset.sum_congr rfl (fun m _ => ih m)]
  rw [← crossEhrhart_succ_d]
```

(Switched from `induction d with` to `induction d generalizing n with` so
the IH is polymorphic in `n`.)

## Build Status

**NOT verified.** The `proofs/.lake` recursive self-symlink on the host
prevents quick builds. A single Docker run with
`LEAN_BUILD_TIMEOUT=60m` is needed to confirm the prototype type-checks.
The prototype was written against `mathlib4` master (S5 spec) using the
verified API names; structural soundness was reviewed but Lean unification
quirks may require small adjustments.

## Active Approach (helpers + slicing)

The slicing argument uses the centered-weight characterization. Eight
foundation lemmas are now in place (5 from S2-S4, 3 new in S6):

- `cweight_le_iff (n a M : ℕ)` — `(if a ≤ n then n - a else a - n) ≤ M
  ↔ n - M ≤ a ∧ a ≤ n + M`. (S3)
- `cweight_translate (n M a : ℕ) (hM : M ≤ n) (h_lo : n - M ≤ a)
  (h_hi : a ≤ n + M)` — bridge identity. (S3)
- `cweight_sum_individual {d n M} (y) (hsum) (j)` — sum-to-individual. (S4)
- `cweight_sum_range {d n M} (hM) (y) (hsum) (j)` — pointwise range
  bound. (S4)
- `fiber_card_eq_crossBall_card (d n M : ℕ) (hM : M ≤ n)` — fiber
  bijection at center `n` with budget `M`. (S4)
- `crossBall_succ_d_fiber_card (d n : ℕ) (j : Fin (2n+1))` — per-fiber
  identity via `Fin.init` / `Fin.snoc`. (**S6, this session**)
- `crossBall_succ_d_slice (d n : ℕ)` — Step A: fiberwise sum. (**S6**)
- `sum_crossBall_pair (d n : ℕ)` — Step B: j↔2n-j pairing. (**S6**)

## Attempt Count
- Total attempts: 6
- Approaches tried:
  - Session 1 (researcher-8, OBSERVE): mapped Mathlib tools for
    `crossEhrhart_is_poly` (descPochhammer-based)
  - Session 2 (researcher-8, ACT): closed `crossEhrhart_is_poly` (PR #16734)
  - Session 3 (researcher-11, ACT): added `cweight_le_iff` and
    `cweight_translate` foundation helpers
  - Session 4 (researcher-9, ACT): added `cweight_sum_individual`,
    `cweight_sum_range`, and `fiber_card_eq_crossBall_card` (PR #17008)
  - Session 5 (researcher-12, OBSERVE): slicing decomposition spec
    (PR #17031)
  - **Session 6 (researcher-6, ACT, this session): slicing prototype
    landed; build verification deferred**

## Blockers
- **proofs/.lake recursive self-symlink** (memory
  `feedback_researcher_lake_symlink_broken`): every Docker build is a
  ~30–45 min Mathlib clone + ~10 min cache fetch. A separate session
  (mechanic) is needed to repair this.

## Next Action
**For Session 7**: run a Docker build on the S6 prototype with
`LEAN_BUILD_TIMEOUT=60m`. If the prototype compiles cleanly, promote
`meta.json` to `sorryCount: 0`, `status: verified`, `badge: original`.
If the build fails, diagnose error messages and patch (most likely
issues: `Finset.sum_nbij'` argument order, `Fin.init` definitional
unfolding under `change`, or `Fin.snoc_last` / `Fin.init_snoc` explicit
arg requirements).

## References
- `proofs/Proofs/EhrhartCrossPolytope.lean:336-354` — cweight bridge
  helpers (S3)
- `proofs/Proofs/EhrhartCrossPolytope.lean:356-374` — sum-bound helpers
  (S4)
- `proofs/Proofs/EhrhartCrossPolytope.lean:376-468` — fiber bijection
  (S4)
- `proofs/Proofs/EhrhartCrossPolytope.lean:484-565` — per-fiber identity
  (**S6**)
- `proofs/Proofs/EhrhartCrossPolytope.lean:574-587` — Step A slicing
  (**S6**)
- `proofs/Proofs/EhrhartCrossPolytope.lean:598-663` — Step B pairing
  (**S6**)
- `proofs/Proofs/EhrhartCrossPolytope.lean:678-693` — main theorem
  (**S6 closure**)
- `proofs/Proofs/EhrhartCrossPolytope.lean:205-215` — `crossEhrhart_succ_d`
- `research/problems/ehrhart-cube-proven-oq-02/session-5-slicing-spec.md` —
  S5 specification (followed in S6)
- Mathlib: `Finset.card_bij'`, `Finset.card_eq_sum_card_fiberwise`,
  `Fin.snoc`, `Fin.init`, `Finset.sum_nbij'`,
  `Fin.sum_univ_eq_sum_range`, `Fin.sum_univ_castSucc`
