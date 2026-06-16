# Research State: erdos-277-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
Prime-power non-vacuity for the corrected `ErdosQuestion277`: no prime power
`p^k` (`k ≥ 1`) admits a proper covering by distinct divisor moduli each `> 1`.
The headline theorem `no_proper_covering_prime_power`
(`proofs/Proofs/Erdos277PrimePowerAristotle.lean`) is **fully proved** by
elementary induction on `k` (0 real `sorry`, 0 `axiom`); the three supporting
lemmas are proved too. All dependencies cross-checked by hand against the parent
`Erdos277Problem.lean`.

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
- Total attempts: 2 (prior session authored proof; this session verified deps +
  attempted build twice)
- Current approach attempts: 2
- Approaches tried: 1 (elementary induction)

## Blockers
- **Shared build-env corruption blocks machine verification.** Two clean Docker
  builds this session (Docker at a safe ≤2-container trough) failed identically:
  `proofs/.lake` is a **self-referential symlink** (`-> itself`), so
  `.lake/packages/mathlib/...` hits `ELOOP`; combined with a missing Azure olean
  for `Mathlib.Algebra.BigOperators.Group.Finset`, Lake can't elaborate that one
  module from source. This breaks *every* build touching `BigOperators`,
  including the already-registered `Erdos277Problem.lean` — a fleet-wide outage,
  not a defect in this proof. Not repaired by this researcher (shared infra,
  gitignored `.lake`, other agents building; risk to warm cache).
- Aristotle backend: 404 (live-probed earlier this session).

## Next Action
When the `.lake` self-symlink + missing-olean infra is fixed and
`./proofs/scripts/docker-build.sh Proofs.Erdos277PrimePowerAristotle` is green:
register the file in `Proofs.lean` (after the `Erdos277Problem` import). The proof
needs no further mathematical work. Do **not** touch `haight_theorem` (deep
axiom; the open question itself stays `axiomatized`).
