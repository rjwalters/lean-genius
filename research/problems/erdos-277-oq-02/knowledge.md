# erdos-277-oq-02 — Knowledge

## Problem

Erdős #277 (Haight 1979). Formalized in `proofs/Proofs/Erdos277Problem.lean`.
`ErdosQuestion277`: for every `c > 0` there is `n` with `σ(n) > cn` but **no
proper covering** of `n` — i.e. no covering system of ℤ whose moduli are
**distinct divisors of `n`, each `> 1`** (`HasProperCoveringWithDivisorModuli`).

The main result `erdos_277 := haight_theorem` is an **axiom** (Haight's 1979
construction; a genuinely deep result, kept axiomatized — do not try to prove it
from Mathlib).

## State of the formalization

- `haight_theorem` — deep axiom, stays. (This is the correct `axiomatized`
  status per the project's Axiom Integrity Policy.)
- Non-vacuity (witnesses `n` with no proper covering) is the productive vein:
  - `no_proper_covering_one` — `n = 1` has no proper covering (only divisor is 1).
  - `no_proper_covering_prime` — every prime `p` has none (single residue class
    mod `p` misses `a + 1`).
  - **NEW (this session):** target `no_proper_covering_prime_power` — every
    prime power `p^k`, `k ≥ 1`, has none. Strictly generalizes the prime case;
    shows non-vacuity on the infinite set of all prime powers.

## Prime-power non-vacuity: elementary induction proof (no density theory)

Divisors of `p^k` that are `> 1` are exactly `p, p², …, p^k`, so a proper
covering of `p^k` uses **distinct** moduli `p^{j}`, `1 ≤ j ≤ k`. Induct on `k`.

- **Base `k = 1`:** `no_proper_covering_prime`.
- **Step.** Let `S` be a proper covering of `p^k`.
  - If the top modulus `p^k` is **not** used, every modulus divides `p^{k-1}`,
    so `S` is a proper covering of `p^{k-1}` → contradiction by IH.
  - If `p^k` **is** used, it's used by a unique `c₀` (distinctness). Set
    `S' = S.erase c₀`. Every modulus of `S'` divides `p^{k-1}`, so the set
    covered by `S'` is **periodic with period `p^{k-1}`** (`covers_add_of_dvd`).
    If some `x` is uncovered by `S'`, then `S` covers `x` only via `c₀`, so
    `x ≡ c₀.residue (mod p^k)`; but `x + p^{k-1}` is *also* uncovered by `S'`
    (periodicity), hence also `≡ c₀.residue (mod p^k)` — forcing
    `p^k ∣ p^{k-1}`, impossible. So `S'` already covers ℤ. If `S' = ∅` then
    `S = {c₀}`, a single congruence with modulus `p^k ≥ 2`, which misses
    `c₀.residue + 1` (`single_congruence_not_covering`); otherwise `S'` is a
    proper covering of `p^{k-1}` → contradiction by IH.

This avoids the reciprocal-sum density theorem (`∑ 1/mᵢ ≥ 1` for covering
systems), which is **not** in Mathlib.

## Supporting lemmas (proved this session, build-pending)

In `proofs/Proofs/Erdos277PrimePowerAristotle.lean` (UNREGISTERED companion):

- `single_congruence_not_covering` — single congruence, modulus `≥ 2`, misses
  `residue + 1`. (Mirrors verified code in `no_proper_covering_prime`.)
- `covers_add_of_dvd` — if `c.modulus ∣ d` and `c` covers `x`, it covers `x + d`.
  The periodicity engine for the induction. (Pure `Int.add_mul_emod_self_left`.)
- `proper_modulus_is_prime_pow` — a divisor of `p^k` that is `> 1` equals `p^j`
  with `1 ≤ j ≤ k`. (Via `Nat.dvd_prime_pow`.)

Both Mathlib lemma names (`Int.add_mul_emod_self_left`, `Nat.dvd_prime_pow`)
confirmed via Loogle.

## Status update (researcher-5, 2026-06-15)

`no_proper_covering_prime_power` is **fully proved** — the headline theorem now
carries the complete elementary induction (`Nat.le_induction` on `k`, with the
`Finset.erase` periodicity argument), **0 real `sorry`, 0 `axiom`**. The lone
`sorry` token previously reported by `grep` was only in the file's header
docstring (it claimed the theorem was a build-pending Aristotle target); that
stale comment has been corrected. All proof dependencies were cross-checked by
hand against `Erdos277Problem.lean` and match: `Congruence {residue, modulus,
modulus_pos}`, `Congruence.covers x := x % m = residue % m` (= `Int.ModEq m x
residue`), the 4-conjunct `HasProperCoveringWithDivisorModuli`, and the base case
`no_proper_covering_prime`.

**Build verification is BLOCKED by shared-infra corruption** (NOT a proof error).
Two clean Docker builds this session (`docker-build.sh
Proofs.Erdos277PrimePowerAristotle`, Docker at a safe ≤2-container trough) both
failed *identically* at module 7742/7745:

```
✖ Mathlib.Algebra.BigOperators.Group.Finset
  error: no such file or directory (error code: 2)
  file: .../proofs/.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset.lean
✖ Proofs.Erdos277Problem        — bad import 'Mathlib.Algebra.BigOperators.Group.Finset'
✖ Proofs.Erdos277PrimePowerAristotle — bad import 'Proofs.Erdos277Problem'
```

Root cause: `proofs/.lake` is a **self-referential symlink**
(`proofs/.lake -> proofs/.lake`), so any path under `.lake/packages/mathlib/`
hits `ELOOP` ("too many levels of symbolic links"). The Azure olean cache for the
current Mathlib revision is also missing the olean for
`Mathlib.Algebra.BigOperators.Group.Finset`, so Lake falls back to building it
from source — and the source path is unreachable through the looping symlink.
This breaks **every** build that touches `BigOperators` (including the already-on-
main, already-registered `Erdos277Problem.lean`), so it is a fleet-wide build
outage, not specific to this file. `.lake` is gitignored local state; repairing
it (rebuild `.lake` / fix the symlink) is shared infra and was left for the
deployer/infra owner rather than risking the warm cache while other agents build.

## Next session

1. Once the `.lake` self-symlink + missing-olean infra is repaired and
   `docker-build.sh Proofs.Erdos277PrimePowerAristotle` goes **green**, register
   it in `Proofs.lean` (after the `Erdos277Problem` import). The proof itself
   needs no further work.
2. Optionally fold the three helpers + main theorem into `Erdos277Problem.lean`
   and bump `theoremCount`.
3. Do **not** touch `haight_theorem` (deep axiom, correct `axiomatized` status).
