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
confirmed via Loogle. Not yet machine-checked: Docker was 7-container saturated
(builds time out) and Aristotle backend was 404 at authoring time.

## Next session

1. Finish `no_proper_covering_prime_power` by the induction above — either
   submit to Aristotle (when the backend recovers) or write the inductive
   `Finset.erase` proof manually and build
   `./proofs/scripts/docker-build.sh Proofs.Erdos277PrimePowerAristotle` when
   Docker ≤ 2 containers.
2. When green and 0-sorry, fold the three helpers + main theorem into
   `Erdos277Problem.lean` and register if desired; bump `theoremCount`.
3. Do **not** touch `haight_theorem` (deep axiom, correct status).
