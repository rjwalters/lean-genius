# Research State: erdos-277-oq-02

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-16
**Iteration**: 3

## Current Focus
Prime-power non-vacuity for the corrected `ErdosQuestion277`: no prime power
`p^k` (`k ≥ 1`) admits a proper covering by distinct divisor moduli each `> 1`.
The headline theorem `no_proper_covering_prime_power`
(`proofs/Proofs/Erdos277PrimePowerAristotle.lean`) is **fully proved** by
elementary induction on `k` (0 real `sorry`, 0 `axiom`); the three supporting
lemmas are proved too. All dependencies cross-checked by hand against the parent
`Erdos277Problem.lean`.

**DONE (this session):** the companion file is now **registered on `main`** —
both `import Proofs.Erdos277PrimePowerAristotle` and `import Proofs.Erdos277Problem`
are present in `proofs/Proofs.lean` (lines 1273–1274), merged via PR #24893. The
prior "Next Action" (register the companion once infra is fixed) is therefore
**already complete**; do not re-register. No further session-sized math work
remains for this sub-problem. The only assumption is the intentional deep axiom
`haight_theorem` in `Erdos277Problem.lean` (the open question stays
`axiomatized`).

## Active Approach
Elementary induction on `k` (no density theory, avoiding the non-Mathlib
`∑ 1/mᵢ ≥ 1` covering theorem):
- base `k = 1` = `no_proper_covering_prime`;
- step: if the top modulus `p^(k+1)` is absent, the system already covers `p^k`
  (contradiction by IH); if present at unique `c₀`, erase it — the rest has all
  moduli dividing `p^k`, so its covered set is `p^k`-periodic
  (`covers_add_of_dvd`); any `x` it misses forces `p^(k+1) ∣ p^k` (impossible),
  so the erased system covers ℤ and is a proper covering of `p^k` (IH again).

## Attempt Count
- Total attempts: 3 (S1 authored proof; S2 verified deps + attempted build;
  S3 confirmed companion registered on main, synced state to COMPLETED)
- Current approach attempts: 3
- Approaches tried: 1 (elementary induction)

## Blockers
None remaining for this sub-problem. (Historical infra note: earlier sessions hit
a self-referential `proofs/.lake` symlink + missing Azure olean for
`Mathlib.Algebra.BigOperators.Group.Finset`, which blocked machine verification;
that did not prevent the eventual registration via PR #24893.)

## Next Action
None — sub-problem complete. The companion is registered and merged; the parent
`Erdos277Problem.lean` carries the intentional deep axiom `haight_theorem` (do
**not** touch it; the open question itself stays `axiomatized`). Future work on
Erdős 277 would be a separate, harder effort to discharge `haight_theorem`, which
is not session-sized and likely not Aristotle-able.
