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
| `not_irreducible_of_proper_dvd` — proper divisor ⟹ reducible (over a field) | **proved** |
| `vahlen_capelli_necessity` — necessity for **all** `n` (both parities) | **proved** |
| `vahlen_capelli` (even `n = 2` base case) — sufficiency via prime Kummer | **proved** |

The two obstruction lemmas assemble into `vahlen_capelli_necessity`: their contrapositive
shows that if either condition fails, the binomial acquires a proper divisor (degree
strictly between `0` and `n`) and factors. This is completely elementary and holds over any
field for **every** `n`.

## The remaining gap (the genuine open part)

The `even sufficiency` direction — "conditions (1),(2) hold ⟹ `X^n − C a` irreducible"
for even `n` — is the hard Capelli theorem and is **not** in Mathlib. With necessity now
fully discharged (all `n`), the odd `iff` complete, and the **even base case `n = 2` now
proved** (via Mathlib's prime-exponent criterion `X_pow_sub_C_irreducible_iff_of_prime`,
whose `4 ∤ 2` makes the `−4·K⁴` obstruction vacuous), `vahlen_capelli` isolates the sole
remaining `sorry` to **even `n ≥ 4`** — the 2-power / `4 ∣ n` regime where the Sophie-Germain
obstruction is essential and Mathlib's prime-power criterion
`X_pow_sub_C_irreducible_iff_of_prime_pow` is restricted to *odd* primes.

## Mathematical heart: the Sophie Germain identity

Condition (2) exists solely because of the factorisation

  `a⁴ + 4b⁴ = (a² − 2ab + 2b²)(a² + 2ab + 2b²)`      (Sophie Germain, 1825)

Substituting `a ↦ X^m` shows that whenever `a = −4b⁴` and `4 ∣ n = 4m`, the binomial
`X^n − C a = (X^m)⁴ + 4(C b)⁴` splits into two degree-`2m` factors — so condition (2) is
*necessary*. Capelli's theorem is that (1)+(2) are also *sufficient*.

## Status: builds cleanly (verified via Docker); sole `sorry` = even-sufficiency (Mathlib TODO)
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
-- PART 5: Necessity of the criterion, for every `n` (both parities)
-- ============================================================

/-- If a nonzero polynomial `f` has a divisor `d` whose degree is strictly between `0` and
`f.natDegree`, then `f` is **not** irreducible: both `d` and its cofactor have positive
degree, so neither is a unit. Over a field this is the workhorse behind "a proper factor
witnesses reducibility". -/
theorem not_irreducible_of_proper_dvd {K : Type*} [Field K] {f d : K[X]}
    (hf : f ≠ 0) (hd : d ∣ f) (hd0 : 0 < d.natDegree)
    (hdf : d.natDegree < f.natDegree) : ¬ Irreducible f := by
  rintro hirr
  obtain ⟨e, rfl⟩ := hd
  have hd_ne : d ≠ 0 := left_ne_zero_of_mul hf
  have he_ne : e ≠ 0 := right_ne_zero_of_mul hf
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  · have hde : e.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have hadd : (d * e).natDegree = d.natDegree + e.natDegree :=
      natDegree_mul hd_ne he_ne
    rw [hde, add_zero] at hadd
    rw [hadd] at hdf
    exact absurd hdf (lt_irrefl _)

/-- **Necessity of the Vahlen–Capelli conditions**, for every `n ≥ 1` and *both* parities.

If `X^n − C a` is irreducible then conditions (1) and (2) both hold. The contrapositive is
elementary: a failure of either condition exhibits a proper divisor —
`obstruction_pow_dvd` for condition (1) (the `p`-th power `X^m − C c`), and the Sophie
Germain factor `capelli_factor_dvd` for condition (2) (the degree-`2m` quadratic). Each has
degree strictly between `0` and `n`, so `not_irreducible_of_proper_dvd` applies.

This is the full "easy half" of the criterion; only the *even sufficiency* direction
remains open (see `vahlen_capelli`). -/
theorem vahlen_capelli_necessity {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) {a : K}
    (hirr : Irreducible (X ^ n - C a)) : VahlenCapelliCond K n a := by
  have hfdeg : (X ^ n - C a : K[X]).natDegree = n := natDegree_X_pow_sub_C
  have hfne : (X ^ n - C a : K[X]) ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hfdeg; omega
  refine ⟨?_, ?_⟩
  · -- Condition (1): `a` is not a `p`-th power for any prime `p ∣ n`.
    intro p hp hpn b hba
    obtain ⟨m, hm⟩ := hpn
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso; rw [h, Nat.mul_zero] at hm; omega
      · exact h
    have hdvd : (X ^ m - C b : K[X]) ∣ (X ^ n - C a) := by
      rw [hm, ← hba]; exact obstruction_pow_dvd m p b
    have hddeg : (X ^ m - C b : K[X]).natDegree = m := natDegree_X_pow_sub_C
    have hmn : m < n := by
      have h2 : 2 ≤ p := hp.two_le
      rw [hm]
      calc m < 2 * m := by omega
        _ ≤ p * m := by gcongr
    exact not_irreducible_of_proper_dvd hfne hdvd (by rw [hddeg]; omega)
      (by rw [hddeg, hfdeg]; exact hmn) hirr
  · -- Condition (2): if `4 ∣ n` then `a ≠ −4b⁴` for any `b`.
    intro h4 b heq
    obtain ⟨m, hm⟩ := h4
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso; rw [h, Nat.mul_zero] at hm; omega
      · exact h
    -- the explicit Sophie Germain factorisation into two degree-`2m` quadratics
    have hfac : (X ^ n - C a : K[X]) =
        ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2) *
          ((X ^ m) ^ 2 + 2 * C b * X ^ m + 2 * (C b) ^ 2) := by
      rw [hm, heq, C_neg_four_mul_pow, sub_neg_eq_add, factor_capelli]
    have hdvd : ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]) ∣ (X ^ n - C a) :=
      ⟨_, hfac⟩
    have hq1ne : ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]) ≠ 0 :=
      left_ne_zero_of_mul (hfac ▸ hfne)
    have hq2ne : ((X ^ m) ^ 2 + 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]) ≠ 0 :=
      right_ne_zero_of_mul (hfac ▸ hfne)
    have hq1le :
        ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]).natDegree ≤ 2 * m := by
      compute_degree; omega
    have hq2le :
        ((X ^ m) ^ 2 + 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]).natDegree ≤ 2 * m := by
      compute_degree; omega
    have hsum :
        ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]).natDegree
          + ((X ^ m) ^ 2 + 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]).natDegree = n := by
      have hmul := natDegree_mul hq1ne hq2ne
      rw [← hfac, hfdeg] at hmul; omega
    have hq1eq :
        ((X ^ m) ^ 2 - 2 * C b * X ^ m + 2 * (C b) ^ 2 : K[X]).natDegree = 2 * m := by
      omega
    exact not_irreducible_of_proper_dvd hfne hdvd (by rw [hq1eq]; omega)
      (by rw [hq1eq, hfdeg]; omega) hirr

-- ============================================================
-- PART 6: The full criterion (even sufficiency = the open Mathlib gap)
-- ============================================================

/-- **Vahlen–Capelli criterion (full statement).** For any field `K`, `a : K`, and
`n ≥ 1`,

  `Irreducible (X ^ n − C a) ↔ VahlenCapelliCond K n a`.

* **Necessity** (`⟹`) is fully proved for all `n` as `vahlen_capelli_necessity`.
* **Sufficiency** for **odd** `n` is `vahlen_capelli_odd` (complete, via Mathlib).
* **Sufficiency** for **even** `n` — conditions (1),(2) ⟹ irreducible when `4 ∣ n` — is the
  hard Capelli theorem (Lang, *Algebra*, VI §9), currently an open `TODO` in Mathlib. It is
  the **sole remaining `sorry`**; both directions of the odd case and the necessity of the
  even case are now machine-checked.

Proof sketch for the remaining step (standard reduction, cf. Lang VI §9):
write `n = 2^k · t` with `t` odd. The odd part is handled by `vahlen_capelli_odd`
applied after the substitution `X ↦ X^{2^k}`; multiplicativity of irreducibility of
`X^s − C a` under coprime factorisations of the exponent then reduces to `n = 2^k`.
For `n = 2^k` one argues by induction on `k`: the inductive obstruction is precisely the
`−4b⁴` factorisation captured by `sophie_germain`, and condition (2) rules it out. -/
theorem vahlen_capelli {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) {a : K} :
    Irreducible (X ^ n - C a) ↔ VahlenCapelliCond K n a := by
  constructor
  · exact vahlen_capelli_necessity hn
  · intro hcond
    rcases Nat.even_or_odd n with _he | ho
    · -- even sufficiency
      by_cases h2 : n = 2
      · -- base case n = 2 (prime exponent): the 4·K⁴ obstruction cannot occur since 4 ∤ 2,
        -- so the criterion collapses to condition (1) at p = 2, i.e. `a` is not a square.
        -- This is Mathlib's prime-exponent Kummer criterion `X_pow_sub_C_irreducible_iff_of_prime`.
        subst h2
        have hp2 : Nat.Prime 2 := Nat.prime_two
        exact (X_pow_sub_C_irreducible_iff_of_prime hp2).mpr (hcond.1 2 hp2 (dvd_refl 2))
      · -- even `n ≥ 4`: the genuine open gap (Lang VI §9 / Mathlib TODO — 2-power exponents,
        -- where the `−4·K⁴` Sophie-Germain obstruction is the essential extra content and
        -- Mathlib's prime-power criterion `X_pow_sub_C_irreducible_iff_of_prime_pow` is
        -- restricted to odd primes).
        sorry
    · exact (vahlen_capelli_odd ho).mpr hcond

end CubeRoot3IrrationalOQ02OQ03
