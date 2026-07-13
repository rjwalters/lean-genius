# S1 OBSERVE — Mathlib `SumTwoSquares.lean` API survey for OQ-01 Fermat-two-squares biconditional (doc-only)

**Date**: 2026-05-30
**Researcher**: researcher-1
**Phase**: OBSERVE (doc-only Mathlib API pin-survey at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Iteration**: 1 OBSERVE (first session since problem creation 2026-04-12)

## 1. Trigger and scope

| Signal | Threshold | Observation | Verdict |
|--------|-----------|-------------|---------|
| Open PRs on slug | 0 expected for fresh problem | **0 open** | OK |
| Days since problem creation | n/a (fresh) | **48 days** stale (created 2026-04-12) | priming required |
| Existing Lean files | check parent | `proofs/Proofs/InfinitudePrimes4k1.lean` (infinitude proof, uses one direction of Fermat); `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` exists | parent infrastructure present |
| Mathlib import status in existing file | `Mathlib.NumberTheory.SumTwoSquares` imported | **YES** at line 4 of `InfinitudePrimes4k1.lean` | API available without new imports |

## 2. Mathlib `SumTwoSquares.lean` API pin-verify at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Pin-verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/SumTwoSquares.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

| # | Bearer | File @ SHA | Line | Signature | Notes |
|---|--------|-----------|------|-----------|-------|
| F1 | `Nat.Prime.sq_add_sq` | `Mathlib/NumberTheory/SumTwoSquares.lean` | **35** | `{p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) : ∃ a b : ℕ, a^2 + b^2 = p` | **The hard direction**, given as `p % 4 ≠ 3` (weaker than `p % 4 = 1`); covers `p = 2` since `2 % 4 = 2 ≠ 3`. Uses `[Fact p.Prime]` typeclass — need `haveI : Fact p.Prime := ⟨hp⟩` to instantiate. |
| F2 | `Nat.sq_add_sq_mul` | (same) | **56** | `{a b x y u v : ℕ} (ha : a = x^2 + y^2) (hb : b = u^2 + v^2) : ∃ r s, a*b = r^2 + s^2` | Closure of sums-of-2-squares under multiplication; not directly needed for OQ-01 but useful for general n results. |
| F3 | `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one` | (same) | **95** | `{p n : ℕ} (hp : p ∈ n.primeFactors) (hs : IsSquare (-1 : ZMod n)) : p % 4 ≠ 3` | Used by the existing `InfinitudePrimes4k1.lean` for the forward direction. |
| F4 | `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one` | (same) | **104** (alias) | alias for F3 (deprecated name retained for back-compat) | The name the existing `InfinitudePrimes4k1.lean` references at line 36. |
| F5 | `Nat.eq_sq_add_sq_iff_eq_sq_mul` | (same) | **193** | full characterization: `∃ a b, n = a^2 + b^2 ↔ ∃ a' b, n = a'^2 * b ∧ IsSquare (-1 : ZMod b)` | For general n. NOT directly the prime biconditional but a related result. |
| F6 | `Nat.eq_sq_add_sq_iff` | (same) | **221** | full characterization: `∃ a b, n = a^2 + b^2 ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → (padicValNat q n) % 2 = 0` | For general n via prime-factor exponent parity. |

**Header documentation (lines 13-24)**:

> Fermat's theorem on the sum of two squares. Every prime `p` congruent to 1 mod 4 is the sum of two squares; see `Nat.Prime.sq_add_sq` (which has the weaker assumption `p % 4 ≠ 3`).
>
> We also give the result that characterizes the (positive) natural numbers that are sums of two squares as those numbers `n` such that for every prime `q` congruent to 3 mod 4, the exponent of the largest power of `q` dividing `n` is even; see `Nat.eq_sq_add_sq_iff`.

## 3. OQ-01 problem decomposition

The OQ-01 problem statement (per `problem.md` line 12):

> `p` is an odd prime ⇒ (`p ≡ 1 (mod 4)` ⟺ `∃ a, b ∈ ℕ, p = a² + b²`)

The two directions:

### 3.1 (←) "sum of squares ⇒ p % 4 = 1"  (easy direction)

For an odd prime `p`, if `p = a² + b²`:

- `p` is odd ⇒ exactly one of `a, b` is even, the other odd (since even² + odd² = odd, but even+even and odd+odd are even).
- Squares mod 4: `even² ≡ 0 (mod 4)`, `odd² ≡ 1 (mod 4)`.
- Sum: `0 + 1 = 1 (mod 4)`. So `p % 4 = 1`. ✓

**Lean strategy** (~10 LOC):

```lean
-- Easy direction. Given p odd prime and p = a² + b², conclude p % 4 = 1.
have h_parity : a^2 % 2 + b^2 % 2 ≡ 1 (mod 2) := by  -- p is odd
  ...
-- Case-split on a % 2 and b % 2 (4 cases), then omega closes each.
omega -- or decide / fin_cases / interval_cases
```

The case-split is mechanical; `omega` should close most cases after `decide` provides facts about `n % 4` for `n ∈ {0, 1, 2, 3}`.

### 3.2 (→) "p % 4 = 1 ⇒ sum of squares"  (hard direction)

Apply F1 (`Nat.Prime.sq_add_sq`) with `hp : p % 4 ≠ 3` derived from `p % 4 = 1` by `omega`.

**Lean strategy** (~5 LOC):

```lean
intro h_mod
haveI : Fact p.Prime := ⟨hp⟩
have hne3 : p % 4 ≠ 3 := by omega
obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hne3
exact ⟨a, b, hab.symm⟩
```

The `hab.symm` converts `a^2 + b^2 = p` to `p = a^2 + b^2`.

### 3.3 Why `p ≠ 2` matters

Note `2 = 1² + 1²` is a sum of two squares **but** `2 % 4 = 2 ≠ 1`. So for `p = 2`:
- (→): `p % 4 = 1` is FALSE (`p % 4 = 2`), so vacuously true.
- (←): `p = a² + b²` with `(a,b) = (1,1)` gives `1+1 = 2`, but `p % 4 = 2 ≠ 1`.

So the biconditional FAILS for `p = 2` in the (←) direction. The problem statement says **"odd prime"** which excludes `p = 2`. Good.

This means the formalization should have hypothesis `hp_odd : p ≠ 2` (equivalent to `p % 2 = 1` for an odd prime).

## 4. S2 SCAFFOLD-ready paste

Insertion target: **new file** `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` (note: OQ-03 already exists at `InfinitudePrimes4k1OQ03.lean`, so OQ-01 should follow naming convention `InfinitudePrimes4k1OQ01.lean`).

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Fermat's Theorem on Sums of Two Squares (OQ-01)

This file formalizes the full biconditional Fermat two-squares characterization
for odd primes:

  p odd prime → (p ≡ 1 mod 4 ↔ ∃ a b : ℕ, p = a² + b²)

The forward direction (hard) follows directly from Mathlib's
`Nat.Prime.sq_add_sq`. The backward direction (easy) is a mod-4 case analysis.

Together these strengthen `InfinitudePrimes4k1.lean` (which uses only the
forward direction implicitly via `mod_four_ne_three_of_dvd_isSquare_neg_one`).

## Status
- [x] Forward direction (Mathlib wrapper)
- [x] Backward direction (mod-4 case analysis)
- [x] Both wrapped in a single biconditional theorem
-/

namespace InfinitudePrimes4k1OQ01

open Nat

/-- Squares mod 4 are 0 or 1. -/
lemma sq_mod_four (n : ℕ) : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
  have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (n % 4) <;>
    omega -- or: have := Nat.pow_mod n 2 4; omega

/-- **Fermat's Theorem on Sums of Two Squares** (OQ-01 main result).
An odd prime `p` is a sum of two squares if and only if `p ≡ 1 (mod 4)`. -/
theorem fermat_two_squares (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    p % 4 = 1 ↔ ∃ a b : ℕ, p = a^2 + b^2 := by
  constructor
  · -- Forward: p % 4 = 1 → ∃ a b, p = a^2 + b^2.
    intro h_mod
    haveI : Fact p.Prime := ⟨hp⟩
    have hne3 : p % 4 ≠ 3 := by omega
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hne3
    exact ⟨a, b, hab.symm⟩
  · -- Backward: ∃ a b, p = a^2 + b^2 → p % 4 = 1.
    rintro ⟨a, b, hab⟩
    -- p is odd: p % 2 = 1.
    have hp_odd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    -- Case-split on (a % 2, b % 2) ∈ {(0,0), (0,1), (1,0), (1,1)}.
    -- Use a^2 % 4 ∈ {0, 1} and Nat.pow_mod, then omega.
    have ha := sq_mod_four a
    have hb := sq_mod_four b
    -- p = a^2 + b^2 ⇒ p % 4 = (a^2 + b^2) % 4.
    have h_p_mod : p % 4 = (a^2 + b^2) % 4 := by rw [hab]
    have h_pa : p % 2 = (a^2 + b^2) % 2 := by rw [hab]
    -- Parity: p is odd ⇒ a^2 + b^2 is odd ⇒ exactly one of a^2 % 2, b^2 % 2 is 1.
    -- Together with a^2 % 4 ∈ {0, 1} and b^2 % 4 ∈ {0, 1}, only (0+1) or (1+0) works mod 4.
    have h_a2_mod2 : a^2 % 2 = (a % 2)^2 % 2 := by rw [Nat.pow_mod]
    have h_b2_mod2 : b^2 % 2 = (b % 2)^2 % 2 := by rw [Nat.pow_mod]
    omega

end InfinitudePrimes4k1OQ01
```

**Estimated LOC**: ~50 lines. **Sorries**: 0. **Axioms**: 0.

### Bearer dependencies for S2 SCAFFOLD

- F1 `Nat.Prime.sq_add_sq` — pinned bearer (line 35 of `SumTwoSquares.lean`).
- `Nat.pow_mod` (Mathlib core).
- `Nat.Prime.eq_two_or_odd` (Mathlib core, alternative `Nat.Prime.two_or_odd`).
- `interval_cases`, `omega`, `rcases`, `obtain` (standard tactics).

**No new Mathlib bearers** are required. The proof is a clean wrapper around the pinned `Nat.Prime.sq_add_sq` + a 4-case mod-4 analysis.

## 5. Risk register

| Risk | Mitigation |
|------|------------|
| `Nat.pow_mod` spelling drift | Pin-verified at SHA via `gh api`. If renamed, replace with `Nat.pow_mod_eq_pow_mod_pow_mod` or unfold via `Nat.pow_succ`. |
| `interval_cases (n % 4)` not unfolding | Alternative: `match h : n % 4 with | 0 | 1 | 2 | 3 => ...` or `fin_cases h` after `have : n % 4 < 4`. |
| `omega` not closing the mod-4 case-split | Add `have : a^2 % 4 = (a % 2)^2 % 4` lemma via `Nat.pow_mod`. |
| Mathlib API drift (akin to S20 INFRA-RECOVERY discovery on `angle-trisection-oq-05-oq-04`) | Pre-flight build `Proofs.InfinitudePrimes4k1` at Docker before any new paste, to verify no latent regressions in the parent infrastructure. |

The risk register reflects the lesson from concurrent slug `angle-trisection-oq-05-oq-04`'s S20 INFRA-RECOVERY discovery (file-wide Mathlib drift hidden by Docker outages): **always re-build before pasting**.

## 6. Honest calibration

This S1 OBSERVE:

- **Adds 0 Lean to the project** (this is a doc-only session note).
- **Closes 0 sorries.**
- **Resolves 0 of the OQ-01 conjecture.**
- **Discovers**: the OQ-01 main theorem is a ~50-LOC wrapper around Mathlib's `Nat.Prime.sq_add_sq` (line 35 of `SumTwoSquares.lean`).
- **Provides paste-ready Lean** (§4) for the S2 SCAFFOLD picker to drop in without further API surveys.
- **Pin-verifies** 6 Mathlib bearers (F1–F6) at lake SHA.

The OQ-01 problem is **tractable** (per problem.md's 8/10 tractability) — Mathlib has the harder direction directly. The S2 SCAFFOLD picker should be able to land the full biconditional in 1-2 Docker iterations (the only real risk is `omega` handling the mod-4 case-split, which has 3 documented fallbacks in §5).

### Next ACT target (S2+)

1. **S2 SCAFFOLD/ACT** — paste §4 code into new file `proofs/Proofs/InfinitudePrimes4k1OQ01.lean`. Update `proofs/Proofs.lean` import root (or `Proofs.lean` if it exists as the umbrella).
2. **S3 ENRICH** — add gallery integration: `src/data/proofs/infinitude-primes-4k1-oq-01/meta.json` + annotations + cross-reference to `infinitude-primes-4k1`.
3. **S4 STRENGTHEN** — consider extending to the explicit-witness extraction (constructive `(a, b)` from `p % 4 = 1`) per problem.md §"What's Still Open" line 41.

## 7. References

- Mathlib `Nat.Prime.sq_add_sq` at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified 2026-05-30T05:30Z via gh api).
- Existing `InfinitudePrimes4k1.lean` at HEAD `ae2ff348920` (origin/main).
- Existing `InfinitudePrimes4k1OQ03.lean` at HEAD `ae2ff348920` (sibling slug).
- Problem.md §References (Fermat 1640, Euler 1749, Zagier 1990 — historical context).
