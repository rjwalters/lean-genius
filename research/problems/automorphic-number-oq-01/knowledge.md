# Knowledge Base: automorphic-number-oq-01

Automorphic numbers mod `10^k`: `ZMod (10^k)` has exactly four idempotents.

## Problem Understanding

A `k`-digit number `n` is automorphic when `n^2 ≡ n (mod 10^k)` (e.g. `5, 6, 25, 76,
376, 625, ...`). Reducing mod `10^k`, automorphic residues are exactly the **idempotents**
`e` of the ring `ZMod (10^k)` (`e * e = e`). Claim: for every `k ≥ 1` there are exactly
four: `0`, `1`, and two non-trivial complementary automorphic residues.

## Proof Structure (in `proofs/Proofs/AutomorphicNumberOQ01.lean`)

- `idem_eq_zero_or_one` — for prime `p`, `k ≥ 1`, every idempotent of `ZMod (p^k)` is
  `0` or `1`. Lift `e` to `n < p^k`; `e^2 = e` gives `p^k ∣ n(n-1)`; since
  `gcd(n, n-1) = 1` the prime power lands on one factor, forcing `n ∈ {0,1}`.
- `idem_card_prime_pow` — hence `ZMod (p^k)` has exactly two idempotents (`{0,1}`).
- `idemCongr` / `idemProd` — idempotents transport across a ring iso and split
  componentwise across a product ring.
- `automorphic_idempotent_count` — `10^k = 2^k · 5^k` (coprime) ⟹ via CRT
  `ZMod (10^k) ≃+* ZMod (2^k) × ZMod (5^k)` ⟹ count `= 2 · 2 = 4`.

0 sorries, 0 `axiom` declarations, no `native_decide`. Genuinely `verified`-eligible
once built (not axiomatized).

## Insights

- The count is multiplicative: `ZMod n` has `2^ω(n)` idempotents; `10 = 2·5` gives `4`.
- This is the finite shadow of the two non-trivial idempotents of the 10-adic integers
  `ℤ₁₀ ≅ ℤ₂ × ℤ₅` (the "infinite automorphic numbers" `…90625`, `…09376`).
- Local-ring triviality (`ZMod (p^k)` has only `0,1` idempotent) is the per-prime factor.

## Session 2026-06-16 — rescue + ship (build-pending)

**Mode**: FRESH. **Outcome**: progress (complete proof rescued from unshipped local
work; shipped as build-pending orphan).

A prior session had written the full 176-line proof (0 sorries / 0 axioms) plus a
`src/data` gallery `meta.json`, but never committed or PR'd it — it sat as untracked
files. This session:

- Verified the mathematics is correct and the structure sound.
- Hardened two name-fragile spots against Mathlib v4.26.0 (offline-checked, pin
  `2df2f0150c`): replaced the deprecated `ZMod.natCast_zmod_eq_zero_iff_dvd` with
  `ZMod.natCast_eq_zero_iff`, and replaced a bare `Nat.Coprime.pow` (whose exponents
  are explicit in v4.26, so the dot-call would not elaborate) with a
  `Nat.coprime_pow_left_iff`/`coprime_pow_right_iff` rewrite + `decide`.
- Shipped the `.lean` as an **unregistered orphan** (not in `Proofs.lean`) and held the
  gallery `meta.json` in `gallery-draft/` rather than `src/data/`, because the Docker
  build pool was down (`docker run` rc=124) — avoids a false-green `verified` entry.

### Why not built
Dual-blackout day: `docker run --rm alpine echo ok` returns rc=124 (daemon wedged, not
just loaded — `docker ps` count of 0 is a known liar under this condition). Aristotle
not needed (no open sorries).

### Next Steps
- When Docker is healthy: register + `docker-build.sh Proofs.AutomorphicNumberOQ01`,
  then promote `gallery-draft/meta.json` to `src/data/proofs/automorphic-number-oq-01/`.
- Follow-up OQ candidates: (a) general base `b` — `ZMod (b^k)` has `2^ω(b)` idempotents;
  (b) explicit Hensel lift of the two non-trivial idempotents from mod `10` to mod `10^k`.
