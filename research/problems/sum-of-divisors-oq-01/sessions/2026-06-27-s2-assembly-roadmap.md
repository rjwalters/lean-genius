# S2 — Status reconciliation + global-assembly roadmap

**Date:** 2026-06-27
**Agent:** researcher-1
**Phase:** ORIENT complete → ACT-ready (handoff)
**Build status:** read-only session (host blocker; no new Lean shipped).

## Why this session is notes-only

The recorded `state.md` was stale ("Phase: NEW, Iteration 1, no Lean file"),
but in fact a substantial, **verified** Lean file already exists:
`proofs/Proofs/SumOfDivisorsOQ01.lean` (133 lines, **0 sorry / 0 axiom**),
together with a gallery entry `src/data/proofs/sum-of-divisors-oq-01/`
(title "Euler's Odd-Perfect Form: The Local Prime-Power Theory of the Special
Prime"). This session reconciles the state and lays out the one remaining gap.

The Docker build host is down this cycle (Data volume 100% full + containerd
blob-store I/O corruption; local olean cache partial — `Aesop.olean` absent),
so I did **not** ship the global-assembly Lean — it is heavy `Nat.factorization`
/ `ArithmeticFunction.IsMultiplicative` API work that genuinely needs iterative
build feedback to land. Forcing an unverifiable ~150-line assembly PR would be
low-confidence; instead this is an accurate handoff.

## What is DONE and verified (local prime-power engine)

In `SumOfDivisorsOQ01.lean`:
- `sigma_prime_pow_odd_iff` (L1) — odd prime `p`: `Odd (σ(p^a)) ↔ Even a`.
- `odd_perfect_sigma_eq_two_mul` — `Nat.Perfect N → σ(N) = 2N`.
- `geom_sum_odd_eq_factor` — pairing identity `∑_{j<2t+2} p^j = (1+p)·∑_{k<t+1} p^{2k}`.
- `even_geom_sum_parity` — `(∑_{k<m} p^{2k}) % 2 = m % 2` for odd `p`.
- `sigma_prime_pow_mod_four` (L2) — odd prime `p`, odd `a`:
  `σ(p^a) % 4 = 2 ↔ p % 4 = 1 ∧ a % 4 = 1`.

These are exactly the parity / mod-4 facts most prone to off-by-one error, all
closed by `omega` after the right rewrites, deliberately `padicValNat`-free.

## The remaining gap: GLOBAL ASSEMBLY (the only open work in scope)

Target theorem (conditional; existence of OPNs stays open):
> Odd `N` with `σ(N) = 2N` ⟹ `∃ p a m, N = p^a * m^2 ∧ p.Prime ∧ p % 4 = 1 ∧
> a % 4 = 1 ∧ ¬ p ∣ m`.

Reduced (cleaner) target the engine is built for:
> Odd `N > 1` with `(σ(N)).factorization 2 = 1` ⟹ Euler form.

### Concrete Mathlib API roadmap (for a session WITH a working build)

1. **σ is multiplicative.** `ArithmeticFunction.isMultiplicative_sigma`
   (`(σ k).IsMultiplicative`). Use `IsMultiplicative.multiplicative_factorization`
   or `IsMultiplicative.map_prod_of_prime` to write
   `σ(N) = ∏ p ∈ N.primeFactors, σ(p ^ (N.factorization p))`.
2. **2-adic valuation is additive over the product.**
   `Nat.factorization_prod` / `Nat.Prime.factorization_pow` plus
   `Nat.factorization_mul` (needs each factor ≠ 0 — `σ(p^a) ≠ 0`). Gives
   `(σ N).factorization 2 = ∑ p ∈ N.primeFactors, (σ (p^(N.factorization p))).factorization 2`.
3. **Each summand ≥ 1 ⟺ `σ(p^a)` even ⟺ (L1) `a` odd.** Translate L1's
   `Odd (σ(p^a))` to `(σ(p^a)).factorization 2 = 0` via `Nat.factorization_eq_zero_iff`
   / `Nat.odd_iff_not_even` + `Nat.two_dvd_ne_zero`.
4. **Sum over naturals = 1 ⟹ exactly one nonzero term, equal to 1.** A
   `Finset.sum_eq_one_iff`-style argument (each term ∈ ℕ): exactly one
   `p = p₀` has odd exponent and contributes valuation `1`; for that term
   `(σ(p₀^a)).factorization 2 = 1`, i.e. `σ(p₀^a) % 4 = 2` (relate
   `factorization 2 = 1` to `% 4 = 2` for the value, via `Nat.factorization`
   of an even-but-not-4-divisible number) ⟹ **L2** gives `p₀ % 4 = a % 4 = 1`.
5. **Assemble `N = p₀^a · m²`.** `m := ∏_{p ≠ p₀} p^(factorization p / 2)`;
   all those exponents are even (step 3), so `m²` collects them. Use
   `Nat.factorization_prod_pow_eq_self` (`N.factorization.prod (·^·) = N` for
   `N ≠ 0`) to reconstruct `N`, split off `p₀`. `¬ p₀ ∣ m` because `p₀ ∉` the
   index set.

The fiddly bridges are 3 and 4 (the `factorization 2 = 1 ↔ % 4 = 2` value
translation and the "sum of naturals = 1 ⟹ unique nonzero" extraction); budget
those for build iteration.

## Recommendation

- Keep this entry `axiomatized`-free but **incomplete** at the gallery level
  until the global assembly lands (the local engine alone does not state the
  headline theorem). The gallery `meta.json` currently has `status: None` —
  the enricher/auditor should set it to reflect "local engine verified; global
  assembly pending" rather than implying the full Euler theorem is proved.
- Next researcher with a working Docker host: implement the 5-step assembly
  above in a new `SumOfDivisorsOQ01.lean` section or a sibling file.

## Out of scope (unchanged)

Existence/non-existence of odd perfect numbers (open); Ochem–Rao-style
quantitative bounds.
