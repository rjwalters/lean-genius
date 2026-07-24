# S6+S7 ACT — CRT multiplicativity + induction assembly (main theorem closed)

**Date**: 2026-07-24
**Researcher**: researcher-2
**Phase**: ACT (final)
**Branch**: `research/gauss-wilson-oq03-s6-s7-crt-induction`
**Build**: `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ03`
— exit 0, 2973 jobs, file built in 2.4 s. **0 sorries, 0 axioms.**

## What closed

The file's sole remaining `sorry` — the main theorem

```lean
theorem card_sqrts_one_eq_numSqrtsOne (n : ℕ) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card = numSqrtsOne n
```

is now fully proved. This completes OQ-03: the exact count
`#{x ∈ ZMod n : x² = 1} = 2^(ω_odd(n) + ε₂(n))` for every `n ≥ 1`,
the quantitative upgrade of the parent's `card_sq_eq_one_ge_three`.

This session had been **BLOCKED since 2026-06-13** (Docker verification
blackout, flagged in PR #23106). Docker is back; the block dissolved.

## S6 (Section 10) — CRT multiplicativity

Exactly as designed in the S6 PREP (#18423) with the corrections from the
2026-05-13 API audit:

* `card_filter_sq_eq_one_of_mulEquiv` — generic transport of the count
  across `e : G ≃* H`. Implemented via the **image argument** (mirroring
  the file's own S3 bridge: image of the filter under the injective `e`
  equals the target filter + `Finset.card_image_of_injective`), NOT the
  PREP's `subtypeEquiv` route — the audit-flagged `Prod.pow_def` simp
  chain made no progress under v4.31 in the `subtypeEquiv` form.
* `card_filter_sq_eq_one_prod` — 2-torsion of `G × H` splits
  componentwise; `Finset.card_product` + `Prod.pow_mk` + `Prod.mk_eq_one`
  (both exist at v4.31 in `Mathlib/Algebra/Notation/Prod.lean`).
* `card_filter_sq_eq_one_units_mul_coprime` — the `Nat.totient_mul`
  rewrite chain: `Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv`
  `|>.trans MulEquiv.prodUnits`, then the two generic lemmas.

## S7 (Sections 11–12) — bookkeeping + induction

Bookkeeping (all hypothesis-free where the S7 PREP expected positivity —
`Nat.Coprime.primeFactors_mul` needs no nonzero hypotheses):

* `epsTwo_of_odd`, `epsTwo_mul_of_odd_right` (key: odd `n` is coprime to
  `2^j`, so `2^j ∣ m*n ↔ 2^j ∣ m`; `split_ifs <;> omega` discharges —
  omega consumes the dvd-iff hypotheses directly), `epsTwo_mul_of_coprime`.
* `omegaOdd_mul_of_coprime` via `Nat.Coprime.primeFactors_mul` +
  `Finset.disjoint_filter_filter ∘ Nat.Coprime.disjoint_primeFactors`.
* `numSqrtsOne_mul_of_coprime`, `numSqrtsOne_prime_pow_odd`,
  `omegaOdd_two_pow`, `epsTwo_two_pow_ge_three`, `numSqrtsOne_two`,
  `numSqrtsOne_four`.

Induction `card_filter_sq_eq_one_units_eq_numSqrtsOne` via
`Nat.recOnPosPrimePosCoprime` (case names `prime_pow/zero/one/coprime`;
`Prime p` there **is** `Nat.Prime` — file is inside `namespace Nat`, so
no `Nat.prime_iff` bridging needed, contrary to the S7 PREP's risk table):

* `zero` — vacuous from the `NeZero` binder (`h.out`).
* `one` — `(ZMod 1)ˣ` is subsingleton: `Units.ext (Subsingleton.elim _ _)`
  makes the filter the whole group, `ZMod.card_units_eq_totient` +
  `Nat.totient_one` gives 1. (**`decide` fails here** — see gotchas.)
* `prime_pow`, `p = 2` — split `k = 1 ∨ k = 2 ∨ 3 ≤ k` by omega-rcases;
  `k ≤ 2` cases via `show`-retyping to the *literal* moduli `ZMod 2` /
  `ZMod 4` (definitionally equal to `ZMod (2^1)` / `ZMod (2^2)`), then the
  existing S5b.1/S5b.2 `decide` theorems; `k ≥ 3` via S5b.3 +
  `epsTwo_two_pow_ge_three`.
* `prime_pow`, `p` odd — S5 + `numSqrtsOne_prime_pow_odd`.
* `coprime` — S6 + `numSqrtsOne_mul_of_coprime`; `NeZero a/b` from
  `1 < a/b` via `haveI ⟨by omega⟩`.

Main theorem: S3 ring↔unit bridge + the unit-side assembly. The sorried
statement was **removed from Section 3** (a forward-pointer comment
remains) and the theorem now lives in Section 12, after its dependencies.
Same name, same statement, same namespace — downstream references
unaffected.

## Gotchas recorded (v4.31)

1. **`decide` rejects goals whose types mention local instances**: inside
   the induction, `Fintype (ZMod (2^k))ˣ` is synthesized from the
   *local* `[NeZero (2^k)]` binder, so `decide` fails with "Expected type
   must not contain free variables" even after `k := 1` specialisation.
   Fix: `show` with the literal modulus (`ZMod 2`), whose global `NeZero`
   instance makes the proposition closed — definitional equality lets
   `show` retype silently.
2. The S6 PREP's `subtypeEquiv + simp [Prod.pow_def]` bridge does not
   close under v4.31 (`simp made no progress` on the transported
   predicate); the image-based argument is robust and matches the file's
   existing S3 style.
3. `omega` accepts divisibility-**iff** hypotheses (`8 ∣ m*n ↔ 8 ∣ m`)
   with opaque products as atoms, letting `split_ifs <;> omega` close all
   `epsTwo` case splits without manual mod-arithmetic.
4. `Nat.Coprime` coerces definitionally to `Nat.gcd m n = 1`
   (`have h1 : Nat.gcd m n = 1 := h`), avoiding any lemma-name lookup for
   the gcd form.

## Deliverable

* `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`: 584 → 854 lines,
  +13 theorems (Sections 10–12), 1 sorry **closed**, 0 axioms,
  0 `native_decide` in named theorems (the 13 `example`s keep theirs;
  benign).
* Docker build verified (exit 0).
* Problem **COMPLETED** — no open targets remain in this file.
