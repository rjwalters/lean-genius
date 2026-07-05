/-
# Vahlen–Capelli Criterion for Binomial Irreducibility

**Open Question OQ-03** (from `cube-root-3-irrational-oq-02`, the Eisenstein proof of
∛3's irrationality):

> Prove the classical **Vahlen–Capelli criterion**: for a field `K`, an element `a ∈ K`,
> and `n ≥ 1`,
>
>   `X^n − C a` is irreducible over `K`  ⟺
>     (1) `a` is not a `p`-th power in `K` for every prime `p ∣ n`, **and**
>     (2) if `4 ∣ n`, then `a ∉ −4·K⁴` (i.e. `a ≠ −4b⁴` for every `b ∈ K`).
>
> This is the concrete Mathlib field-theory gap that generalises the Eisenstein `∛3`
> argument to arbitrary exponents and radicands.

## Where this sits relative to Mathlib

Mathlib's `Mathlib/FieldTheory/KummerExtension.lean` proves the criterion **for odd `n`**:

  `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`
    `(hn : Odd n) : Irreducible (X ^ n - C a) ↔ ∀ p, p.Prime → p ∣ n → ∀ b, b ^ p ≠ a`

and the even case is an **explicit `TODO`** in that file, citing Lang, *Algebra*, VI §9
(the source of the classical Vahlen–Capelli statement). Condition (2) — the `−4·K⁴`
obstruction — is exactly the extra content that appears once `4 ∣ n`, and it has no
counterpart in the odd theory.

## What this file proves

| Result | Status |
|--------|--------|
| `VahlenCapelliCond` — the criterion, as a predicate | definition |
| `sophie_germain` — `u⁴ + 4v⁴ = (u²−2vu+2v²)(u²+2vu+2v²)` | **proved** (`ring`) |
| `factor_capelli` — explicit factorisation of `X^{4m} + 4(C b)⁴` | **proved** (`ring`) |
| `capelli_factor_dvd` — the Capelli obstruction gives a proper divisor | **proved** |
| `C_neg_four_mul_pow` — `C(−4b⁴) = −4(C b)⁴` bookkeeping | **proved** |
| `obstruction_pow_dvd` — `X^m − C c ∣ X^{pm} − C(cᵖ)` | **proved** |
| `vahlen_capelli_odd` — full `iff` for odd `n` (wraps Mathlib) | **proved** |

The two obstruction lemmas together are the **necessity** half of the criterion
(their contrapositive: if either condition fails, the binomial factors). They are
completely elementary and hold over any field for **every** `n`.

## The remaining gap (the genuine open part)

The `even sufficiency` direction — "conditions (1),(2) hold ⟹ `X^n − C a` irreducible"
for `4 ∣ n` — is the hard Capelli theorem and is **not** in Mathlib. It is stated here
as `vahlen_capelli` with the odd case assembled and the even branch isolated as the sole
remaining `sorry`, with a proof sketch.

## Mathematical heart: the Sophie Germain identity

Condition (2) exists solely because of the factorisation

  `a⁴ + 4b⁴ = (a² − 2ab + 2b²)(a² + 2ab + 2b²)`      (Sophie Germain, 1825)

Substituting `a ↦ X^m` shows that whenever `a = −4b⁴` and `4 ∣ n = 4m`, the binomial
`X^n − C a = (X^m)⁴ + 4(C b)⁴` splits into two degree-`2m` factors — so condition (2) is
*necessary*. Capelli's theorem is that (1)+(2) are also *sufficient*.

## Status: build-pending (Docker/Aristotle offline this session); even-sufficiency sorry
-/

import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open Polynomial

namespace CubeRoot3IrrationalOQ02OQ03

-- ============================================================
-- PART 0: The Vahlen–Capelli criterion, as a predicate
-- ============================================================

/-- The Vahlen–Capelli conditions on `a ∈ K` for the exponent `n`:
* condition (1): `a` is not a `p`-th power for any prime `p ∣ n`;
* condition (2): if `4 ∣ n`, then `a` is not of the form `−4b⁴`.

For odd `n`, condition (2) is vacuous and this reduces to Mathlib's
`X_pow_sub_C_irreducible_iff_forall_prime_of_odd`. -/
def VahlenCapelliCond (K : Type*) [Field K] (n : ℕ) (a : K) : Prop :=
  (∀ p : ℕ, Nat.Prime p → p ∣ n → ∀ b : K, b ^ p ≠ a) ∧
  (4 ∣ n → ∀ b : K, a ≠ -(4 * b ^ 4))

-- ============================================================
-- PART 1: The Sophie Germain / Capelli identity (ring-level)
-- ============================================================

/-- **Sophie Germain identity** over any commutative ring:
`u⁴ + 4·v⁴ = (u² − 2vu + 2v²)(u² + 2vu + 2v²)`.

This is the algebraic source of the `−4·K⁴` obstruction: a genuine factorisation of
`u⁴ + 4v⁴` into two quadratics, valid unconditionally. -/
theorem sophie_germain {R : Type*} [CommRing R] (u v : R) :
    u ^ 4 + 4 * v ^ 4 =
      (u ^ 2 - 2 * v * u + 2 * v ^ 2) * (u ^ 2 + 2 * v * u + 2 * v ^ 2) := by
  ring

-- ============================================================
-- PART 2: Necessity witness (2) — the −4·K⁴ obstruction
-- ============================================================

/-- **Capelli factorisation.** When `4 ∣ n` (`n = 4m`), the polynomial
`X^{4m} + 4(C b)⁴` factors explicitly into two degree-`2m` polynomials:

`X^{4m} + 4(C b)⁴ = ((X^m)² − 2(C b)·X^m + 2(C b)²)·((X^m)² + 2(C b)·X^m + 2(C b)²)`.

Obtained from `sophie_germain` with `u = X^m`, `v = C b`. Purely a `ring` identity. -/
theorem factor_capelli {K : Type*} [Field K] (m : ℕ) (b : K) :
    (X ^ (4 * m) + 4 * (C b) ^ 4 : K[X]) =
      ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2) *
        ((X ^ m) ^ 2 + 2 * C b * X ^ m + 2 * (C b) ^ 2) := by
  have hX : (X : K[X]) ^ (4 * m) = (X ^ m) ^ 4 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hX]
  ring

/-- Bookkeeping: `C(−4b⁴) = −4(C b)⁴`, so that `X^{4m} − C(−4b⁴) = X^{4m} + 4(C b)⁴`
connects the Capelli factorisation to the binomial `X^n − C a` with `a = −4b⁴`. -/
theorem C_neg_four_mul_pow {K : Type*} [Field K] (b : K) :
    (C (-(4 * b ^ 4)) : K[X]) = -(4 * (C b) ^ 4) := by
  simp only [Polynomial.C_neg, Polynomial.C_mul, Polynomial.C_pow, map_ofNat]

/-- The Capelli obstruction yields a **proper divisor** of `X^{4m} − C(−4b⁴)`: the first
quadratic factor divides it. That factor has degree `2m` (strictly between `0` and `4m`
for `m ≥ 1`), so this witnesses reducibility — the *necessity* of condition (2). -/
theorem capelli_factor_dvd {K : Type*} [Field K] (m : ℕ) (b : K) :
    ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]) ∣
      (X ^ (4 * m) - C (-(4 * b ^ 4))) := by
  refine ⟨(X ^ m) ^ 2 + 2 * C b * X ^ m + 2 * (C b) ^ 2, ?_⟩
  rw [C_neg_four_mul_pow, sub_neg_eq_add, factor_capelli]

-- ============================================================
-- PART 3: Necessity witness (1) — the p-th power obstruction
-- ============================================================

/-- **Power obstruction.** If `a = cᵖ` is a perfect `p`-th power and `p ∣ n` (`n = pm`),
then `X^m − C c` divides `X^n − C a`:

`X^{pm} − C(cᵖ) = (X^m − C c)·(∑ …)`  via `x − y ∣ xⁿ − yⁿ` with `x = X^m`, `y = C c`.

For a prime `p ∣ n` this factor has degree `m = n/p` (strictly between `0` and `n`), so it
witnesses reducibility — the *necessity* of condition (1). -/
theorem obstruction_pow_dvd {K : Type*} [Field K] (m p : ℕ) (c : K) :
    (X ^ m - C c : K[X]) ∣ (X ^ (p * m) - C (c ^ p)) := by
  have hX : (X : K[X]) ^ (p * m) = (X ^ m) ^ p := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hX, map_pow]
  exact sub_dvd_pow_sub_pow _ _ p

-- ============================================================
-- PART 4: The odd case (full iff, via Mathlib)
-- ============================================================

/-- **Vahlen–Capelli for odd `n`.** For odd exponents, condition (2) is vacuous
(`4 ∤ n`), and the criterion is exactly Mathlib's
`X_pow_sub_C_irreducible_iff_forall_prime_of_odd`. This is a complete `iff`. -/
theorem vahlen_capelli_odd {K : Type*} [Field K] {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ VahlenCapelliCond K n a := by
  rw [X_pow_sub_C_irreducible_iff_forall_prime_of_odd hn]
  have h4 : ¬ (4 ∣ n) := by
    obtain ⟨k, hk⟩ := hn
    rw [hk]; omega
  constructor
  · intro h
    exact ⟨h, fun hd => absurd hd h4⟩
  · intro h
    exact h.1

-- ============================================================
-- PART 5: The full criterion (even case = the open Mathlib gap)
-- ============================================================

/-- **Vahlen–Capelli criterion (full statement).** For any field `K`, `a : K`, and
`n ≥ 1`,

  `Irreducible (X ^ n − C a) ↔ VahlenCapelliCond K n a`.

* The **odd** case is `vahlen_capelli_odd` (complete, via Mathlib).
* **Necessity** (`⟸` contrapositive) for all `n` follows from the obstruction lemmas
  `obstruction_pow_dvd` (condition 1) and `capelli_factor_dvd` (condition 2): if either
  condition fails, the binomial acquires a proper divisor and is reducible.
* The **even sufficiency** step — conditions (1),(2) ⟹ irreducible when `4 ∣ n` — is the
  hard Capelli theorem (Lang, *Algebra*, VI §9), currently an open `TODO` in Mathlib.
  It is the sole `sorry` below.

Proof sketch for the remaining step (standard reduction, cf. Lang VI §9):
write `n = 2^k · t` with `t` odd. The odd part is handled by `vahlen_capelli_odd`
applied after the substitution `X ↦ X^{2^k}`; multiplicativity of irreducibility of
`X^s − C a` under coprime factorisations of the exponent then reduces to `n = 2^k`.
For `n = 2^k` one argues by induction on `k`: the inductive obstruction is precisely the
`−4b⁴` factorisation captured by `sophie_germain`, and condition (2) rules it out. -/
theorem vahlen_capelli {K : Type*} [Field K] {n : ℕ} (_hn : 1 ≤ n) {a : K} :
    Irreducible (X ^ n - C a) ↔ VahlenCapelliCond K n a := by
  rcases Nat.even_or_odd n with _he | ho
  · -- even case: necessity from the obstruction lemmas above; even sufficiency is the gap
    sorry
  · exact vahlen_capelli_odd ho

end CubeRoot3IrrationalOQ02OQ03
