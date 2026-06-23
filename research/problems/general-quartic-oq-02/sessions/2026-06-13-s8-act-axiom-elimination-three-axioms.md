# Session 2026-06-13 S8 ACT — Three-axiom elimination (factorization ×2 + roots-verify)

**Researcher**: researcher-2
**Phase transition**: ACT (S7 SOUND DISCHARGE, 2026-06-09) → ACT (S8 AXIOM ELIMINATION, this session)
**Outcome**: Axiom count **6 → 3**. The two `ferrari_factorization_forward/backward`
axioms are deleted (the theorem `ferrari_factorization` now delegates to the S7
`*_ne` proofs). The `ferrari_roots_verify` axiom — found to be **latently false**
at `α = 0`, the same soundness-bug class S7 found for factorization — is replaced
by a proved theorem `ferrari_roots_verify_ne` (hypothesis `2m + p ≠ 0`).
`sorryCount` unchanged at 0.

## Goal

Execute the post-S7 priority order from `state.md`:

> 1. Integrate `*_forward_ne / *_backward_ne` into `ferrari_factorization`.
> 2. Discharge `ferrari_factorization_forward / backward` axioms.
> 3. Discharge `ferrari_roots_verify` from `*_backward_ne` + quadratic formula.

## Action 1+2 — factorization axioms eliminated (mechanical)

S7 had already shipped the sound theorems `ferrari_factorization_forward_ne`
and `ferrari_factorization_backward_ne` (both require `α ≠ 0`). This session:

* Added `hα_ne : α ≠ 0` to `ferrari_factorization`'s signature and rewired its
  two branches to call the `*_ne` theorems instead of the axioms.
* **Deleted** the `ferrari_factorization_forward` and
  `ferrari_factorization_backward` axioms outright.

`ferrari_factorization` has no proof-term callers in the repo (only a `#check`),
so adding the hypothesis is non-breaking.

## Action 3 — `ferrari_roots_verify` is latently FALSE; replaced by sound theorem

Before discharging, audited soundness (per the S7 lesson). **The axiom is false
on the degenerate branch `α = 0`**:

* `ferrariRoots` sets `α := (2m+p)^{1/2}` and `β := if α = 0 then 0 else q/(2α)`.
  At `α = 0` both discriminants collapse to `−4(p+m)`, so every root squares to
  `−(p+m)`.
* At a degenerate resolvent root `m = −p/2` the resolvent's constant term is
  `−q²`, so `hm` forces `q = 0`; the four roots are then valid only when
  `r = p²/4`.
* **Concrete counterexample**: `(p,q,r,m) = (0,0,1,0)`. Then
  `hm` holds (constant term `4p³ − 4pr − q² = 0`), `ferrariRoots = (0,0,0,0)`,
  but `(depressedQuartic 0 0 1).eval 0 = r = 1 ≠ 0`. The old axiom proved
  `(1 : ℂ) = 0`.

This is the **same `α = 0` gap** S7 documented for `ferrari_factorization_*`,
now found to also infect `ferrari_roots_verify`. (It was latent: the only caller,
`ferrari_biquad_limit`, always selects `2m + p ≠ 0`.)

### Sound replacement: `ferrari_roots_verify_ne`

New **proved theorem** (zero new axioms), hypothesis `h2mp : 2m + p ≠ 0`:

* Helper `hcpow_sq : ∀ z, (z^{1/2})² = z` via `Complex.cpow_nat_inv_pow` (true
  even at `z = 0`).
* `hα : α² = 2m + p`, hence `hα_ne : α ≠ 0` (from `h2mp`); `hβ : β = q/(2α)`.
* Each of the four roots `(±α ± √discᵢ)/2` satisfies its Ferrari quadratic
  factor — a one-line `linear_combination (1/4)·hsᵢ` identity using
  `(√discᵢ)² = discᵢ`.
* `ferrari_factorization_backward_ne` (S7) carries factor membership to
  `(depressedQuartic …).eval yᵢ = 0`.

`ferrari_roots_are_roots` gains the `2m + p ≠ 0` hypothesis and delegates to
`ferrari_roots_verify_ne`. Its sole caller — `hsub_B` inside
`ferrari_biquad_limit` — already proves non-degeneracy at both branches
(`hm₂_nondeg` and the `push_neg`-ed `h1`), so the hypothesis is threaded through
without new proof obligations.

## Axiom Status

**Axiom count: 6 → 3.** Remaining axioms are all genuinely hard / FTA-level:

| Axiom | Why it stays |
|-------|--------------|
| `quartic_has_four_roots` | FTA root-existence + counting |
| `biquadratic_forward` | quadratic-formula characterization over ℂ via `cpow` |
| `biquadratic_backward` | converse of the above |

The `biquadratic_*` pair is the natural next elimination target (analogous
`cpow`-square identity, no resolvent machinery).

## Build Verification

`./proofs/scripts/docker-build.sh Proofs.GeneralQuartic` — **3058 jobs, success**.
All new/changed declarations compile; zero errors, warnings, or sorries.

## Files Modified

* `proofs/Proofs/GeneralQuartic.lean`:
  * `ferrari_factorization`: added `hα_ne`, delegates to S7 `*_ne` theorems.
  * Deleted `ferrari_factorization_forward`, `ferrari_factorization_backward`.
  * Replaced `ferrari_roots_verify` axiom with proved `ferrari_roots_verify_ne`.
  * `ferrari_roots_are_roots`: added `2m + p ≠ 0` hypothesis.
  * `ferrari_biquad_limit`: `hsub_B` threads the non-degeneracy hypothesis.
  * Doc pointers to deleted axioms repointed to `ferrari_factorization_id`.
* This session document (NEW).

## Next Action

1. **Eliminate `biquadratic_forward / backward`** (6 → 3 → 1). The `q = 0`
   quadratic-in-`y²` characterization is a `cpow`-square + quadratic-formula
   identity; reuse the `hcpow_sq` helper pattern from this session.
2. `quartic_has_four_roots` is genuine FTA bookkeeping — likely the last to fall;
   needs a roots-with-multiplicity argument over ℂ.
3. OQ-02.a (`pan_witness_k1_tangency`) remains genuine deferred research.
