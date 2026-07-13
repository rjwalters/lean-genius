# basel-problem-oq-13-oq-01-oq-01 — Uniform Dirichlet eta values η(2k)=(1−2^{1−2k})·ζ(2k)

**Status**: COMPLETED (VERIFIED, 0-axiom) — PR #32307
**Lean file**: `proofs/Proofs/BaselProblemOQ13OQ01OQ01.lean` (7 theorems, 177 lines)

## Problem

Sibling `basel-problem-oq-13-oq-01` formalized the single value η(4)=7π⁴/720 by
hand-splitting the alternating fourth-power sum by parity and reusing fixed
numerical ingredients. Its first open question: package the eta–zeta relation
η(s) = (1 − 2^{1−s})ζ(s) **once**, then specialize to the even integers using
Mathlib's closed form for ζ(2k).

## Result

`hasSum_eta_of_hasSum_zeta` — the exponent-independent bridge: for any natural
`m` and any `Z`, `HasSum (1/n^m) Z ⟹ HasSum ((-1)^{n+1}/n^m) ((1 − 2/2^m)·Z)`.
Then:
- `hasSum_eta_two_mul_nat`: η(2k) = (1 − 2/2^{2k})·ζ(2k), ζ(2k) via `hasSum_zeta_nat` (Bernoulli).
- `eta_factor_eq`: 1 − 2/2^{2k} = 1 − 2^{1−2k}.
- `hasSum_eta_two` = π²/12, `hasSum_eta_four` = 7π⁴/720 (reproves sibling), + tsum forms.

## Session 2026-07-01 (Session 1, FRESH) — COMPLETED

### What I did
- Wrote the general eta–zeta bridge from the parity decomposition alone (no analytic
  dependence on the exponent), specialized to even integers via Mathlib `hasSum_zeta_nat`,
  and recovered η(2), η(4).
- Verified 0-axiom (`#print axioms` → propext/Classical.choice/Quot.sound only).
- Gallery entry + PR #32307.

### Key findings / techniques
- **Parity split is finite-combinatorial**: ∑_even 1/n^s = 2^{-s}ζ(s), so
  η = ζ − 2·(even) = (1 − 2^{1−s})ζ. No exponent property beyond convergence.
- **Odd tail via `HasSum.unique`**: the odd sub-sum B has no closed form, but
  reassembling even+odd=full and comparing with the hypothesis pins
  (1/2^m)Z + B = Z symbolically; finish with one `linear_combination`.
- **Explicit summands defeat HOU**: state each even/odd subseries `HasSum` with
  its summand written out so `HasSum.even_add_odd` unifies the ambient `f` by
  definitional reduction of `f(2k)`/`f(2k+1)`. Even so the main lemma needed
  `set_option maxHeartbeats 1000000` (a `whnf` defeq cost, not divergence).
- **Sign by parity**: (-1)^(2k+1)=-1, (-1)^(2k+2)=+1 via `pow_succ`/`pow_mul` + `norm_num`.
- **`eta_factor_eq`**: reconcile negative integer exponent with natural power via
  `zpow_sub₀` + `zpow_natCast` + `norm_cast`.

### Gotchas
- Factorial `!` notation needs `open scoped Nat`.
- `convert h using 2` mis-descends when goal head is `HDiv` but hypothesis value
  is `HMul` (π²/12 vs (1−2/4)*(π²/6)); use `rwa [show ... = ... by ring] at h` instead.
- **Worktree reaping**: `/private/tmp` worktrees had their git-admin dir reaped
  mid-session (concurrent prune/loom-clean); a second `/private/tmp` worktree was
  removed entirely right after `git worktree add`. Fix: do checkout+copy+commit+push
  atomically in **`$HOME`** (survives loom-clean, which targets /private/tmp + .loom).

### Next steps (follow-ups)
- rpow lift to real/complex s>1 for Mathlib `riemannZeta`.
- Analogous λ(s)=(1−2^{-s})ζ(s) so λ,η,ζ at 2k share one parity lemma.
- Dirichlet beta values β(2k+1) via the odd-character split.
