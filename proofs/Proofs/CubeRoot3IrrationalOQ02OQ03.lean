/-
# Vahlen–Capelli Irreducibility Criterion for Xⁿ − a

**Open Question OQ-02-OQ-03** from `cube-root-3-irrational`:
The gallery proof `cube-root-3-irrational-oq-02` shows ∛3 is irrational by proving
`X³ - 3` is irreducible over ℚ via Eisenstein at p = 3.  That is a single instance
of a general phenomenon.  This file develops the **full classical criterion** for
when `Xⁿ - a` is irreducible over a field `K` — the **Vahlen–Capelli theorem**
(Lang, *Algebra*, VI.9.1):

> `Xⁿ - a` is irreducible over `K` **iff**
> 1. `a ∉ Kᵖ` for every prime `p ∣ n`, **and**
> 2. if `4 ∣ n`, then `a ∉ -4·K⁴`.

## What is already in Mathlib

`Mathlib.FieldTheory.KummerExtension` proves the **odd** part completely:

* `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`
  (for `Odd n`: irreducible ↔ condition 1), and
* `X_pow_sub_C_irreducible_of_prime_pow` (odd prime powers).

That file explicitly leaves **`TODO: criteria for even n`** — the delicate
`4 ∣ n` exceptional case (condition 2) is *not* in Mathlib.  That exceptional
case is the whole mathematical content here.

## What this file contributes

The heart of the even case is the **Sophie Germain / Aurifeuillian factorization**

    Y⁴ + 4c⁴ = (Y² - 2cY + 2c²)(Y² + 2cY + 2c²),

an identity valid over any commutative ring.  Setting `Y = Xᵏ`, `c = C b` gives an
*explicit* nontrivial factorization of `X^{4k} - a` whenever `a = -4b⁴`, which is
exactly why membership in `-4K⁴` forces reducibility when `4 ∣ n`.

Using this we prove, for **all** `n > 0`:

* `sophie_germain_factor`           — the ring identity (bulletproof `ring`).
* `X_pow_four_mul_sub_C_factorization` — the explicit factorization of `X^{4k} - C(-(4b⁴))`.
* `reducible_of_prime_pow_eq`       — condition 1 is necessary (perfect `p`-th power ⇒ reducible).
* `reducible_of_neg_four_mul_pow4`  — condition 2 is necessary (member of `-4K⁴` with `4∣n` ⇒ reducible).
* `vahlen_capelli_necessity`        — **`Irreducible ⇒ VahlenCapelliCond`** for all `n`  (fully proved).
* `vahlen_capelli_of_odd`           — the full criterion for odd `n`, via Mathlib (fully proved).
* `vahlen_capelli`                  — the full criterion for all `n`; the even-`n` *sufficiency*
                                      direction is the single remaining `sorry` (the open frontier).

So the **necessity** direction — including the genuinely-missing `4 ∣ n` clause —
is established here for every `n`, and the only gap is the even-`n` sufficiency
proof, which is the deep half of Vahlen–Capelli.

## Status: 1 sorry (even-n sufficiency of the full criterion; the open frontier)
-/

import Mathlib.Tactic
import Mathlib.FieldTheory.KummerExtension

open Polynomial

namespace CubeRoot3IrrationalOQ02OQ03

-- ============================================================
-- PART 1: The Sophie Germain / Aurifeuillian factorization
-- ============================================================

/-- **Sophie Germain factorization** (a.k.a. the Aurifeuillian identity for the
fourth power).  Over any commutative ring,

    Y⁴ + 4c⁴ = (Y² - 2cY + 2c²)(Y² + 2cY + 2c²).

This is the algebraic engine behind the exceptional `4 ∣ n` case of
Vahlen–Capelli: it exhibits an explicit factorization of a "sum of a fourth power
and four times a fourth power", which is what `a ∈ -4K⁴` produces. -/
theorem sophie_germain_factor {R : Type*} [CommRing R] (Y c : R) :
    (Y ^ 2 - 2 * c * Y + 2 * c ^ 2) * (Y ^ 2 + 2 * c * Y + 2 * c ^ 2)
      = Y ^ 4 + 4 * c ^ 4 := by
  ring

/-- The explicit factorization of `X^{4k} - C a` when `a = -(4·b⁴)`, obtained from
`sophie_germain_factor` with `Y = Xᵏ`, `c = C b`.  Both factors are the genuine
degree-`2k` "halves" — this is the reducibility witness for the `4 ∣ n` exception. -/
theorem X_pow_four_mul_sub_C_factorization {K : Type*} [Field K] (k : ℕ) (b : K) :
    (X ^ (4 * k) - C (-(4 * b ^ 4)) : K[X]) =
      ((X ^ k) ^ 2 - 2 * C b * X ^ k + 2 * C b ^ 2) *
        ((X ^ k) ^ 2 + 2 * C b * X ^ k + 2 * C b ^ 2) := by
  rw [sophie_germain_factor (X ^ k) (C b), ← pow_mul, mul_comm k 4]
  simp only [map_neg, map_mul, map_pow, map_ofNat]
  ring

-- ============================================================
-- PART 2: Necessity clause 1 — perfect prime powers are reducible
-- ============================================================

/-- If `a` is a perfect `p`-th power for some prime `p ∣ n` (with `n > 0`), then
`Xⁿ - C a` is **reducible**.  Indeed `Xᵐ - C b` (with `m = n/p`, `bᵖ = a`) is a
proper factor: it divides `Xⁿ - C a` and both it and the cofactor have positive
degree.  This is the necessity of Vahlen–Capelli's condition 1. -/
theorem reducible_of_prime_pow_eq {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    {a : K} {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) {b : K} (hb : b ^ p = a) :
    ¬ Irreducible (X ^ n - C a : K[X]) := by
  obtain ⟨m, rfl⟩ := hpn
  -- `m > 0` since `p * m > 0`
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hn
    · exact h
  have h2m : 2 * m ≤ p * m := Nat.mul_le_mul hp.two_le (le_refl m)
  -- `Xᵐ - C b` divides `X^{p*m} - C a`
  have hdvd : (X ^ m - C b) ∣ (X ^ (p * m) - C a) := by
    have h := sub_dvd_pow_sub_pow (X ^ m) (C b) p
    rwa [← pow_mul, ← C_pow, hb, mul_comm m p] at h
  obtain ⟨Q, hQ⟩ := hdvd
  intro hirr
  rcases hirr.isUnit_or_isUnit hQ with hu | hu
  · -- `Xᵐ - C b` is not a unit: its degree is `m ≥ 1`
    have hd := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_pow_sub_C] at hd
    omega
  · -- if `Q` were a unit the whole degree would collapse to `m < p*m`
    have hfne : (X ^ m - C b : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hm b
    have hgne : Q ≠ 0 := hu.ne_zero
    have hdeg : (X ^ (p * m) - C a).natDegree = m + 0 := by
      rw [hQ, natDegree_mul hfne hgne, natDegree_X_pow_sub_C,
        natDegree_eq_zero_of_isUnit hu]
    rw [natDegree_X_pow_sub_C] at hdeg
    omega

-- ============================================================
-- PART 3: Necessity clause 2 — the exceptional `4 ∣ n` case
-- ============================================================

/-- If `4 ∣ n` (with `n > 0`) and `a = -(4·b⁴) ∈ -4K⁴`, then `Xⁿ - C a` is
**reducible**, via the Sophie Germain factorization.  This is the necessity of
Vahlen–Capelli's condition 2 — precisely the even-`n` case Mathlib leaves open. -/
theorem reducible_of_neg_four_mul_pow4 {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (hn4 : 4 ∣ n) {a b : K} (hb : a = -(4 * b ^ 4)) :
    ¬ Irreducible (X ^ n - C a : K[X]) := by
  obtain ⟨k, rfl⟩ := hn4
  have hk : 0 < k := by omega
  subst hb
  have hfac := X_pow_four_mul_sub_C_factorization k b
  set F : K[X] := (X ^ k) ^ 2 - 2 * C b * X ^ k + 2 * C b ^ 2 with hFdef
  set G : K[X] := (X ^ k) ^ 2 + 2 * C b * X ^ k + 2 * C b ^ 2 with hGdef
  -- `natDegree F = 2k` via `F = q.comp (Xᵏ)` with `q` a monic quadratic
  have hdF : F.natDegree = 2 * k := by
    have hcomp : (X ^ 2 - C (2 * b) * X + C (2 * b ^ 2) : K[X]).comp (X ^ k) = F := by
      simp only [hFdef, sub_comp, add_comp, mul_comp, pow_comp, C_comp, X_comp,
        map_mul, map_pow, map_ofNat]
    have hq2 : (X ^ 2 - C (2 * b) * X + C (2 * b ^ 2) : K[X]).natDegree = 2 := by
      compute_degree!
    rw [← hcomp, natDegree_comp, hq2, natDegree_X_pow]
  have hdG : G.natDegree = 2 * k := by
    have hcomp : (X ^ 2 + C (2 * b) * X + C (2 * b ^ 2) : K[X]).comp (X ^ k) = G := by
      simp only [hGdef, add_comp, mul_comp, pow_comp, C_comp, X_comp,
        map_mul, map_pow, map_ofNat]
    have hq2 : (X ^ 2 + C (2 * b) * X + C (2 * b ^ 2) : K[X]).natDegree = 2 := by
      compute_degree!
    rw [← hcomp, natDegree_comp, hq2, natDegree_X_pow]
  intro hirr
  rcases hirr.isUnit_or_isUnit hfac with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [hdF] at this; omega
  · have := natDegree_eq_zero_of_isUnit hu
    rw [hdG] at this; omega

-- ============================================================
-- PART 4: The Vahlen–Capelli criterion
-- ============================================================

/-- The two Vahlen–Capelli conditions for irreducibility of `Xⁿ - C a` over `K`:
1. `a` is not a `p`-th power for any prime `p ∣ n`; and
2. if `4 ∣ n`, then `a ∉ -4K⁴`. -/
def VahlenCapelliCond {K : Type*} [Field K] (n : ℕ) (a : K) : Prop :=
  (∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) ∧
    (4 ∣ n → ∀ b : K, a ≠ -(4 * b ^ 4))

/-- **Necessity direction of Vahlen–Capelli, for all `n > 0`.**  If `Xⁿ - C a` is
irreducible then both Vahlen–Capelli conditions hold.  Both clauses are proved
here — clause 1 from `reducible_of_prime_pow_eq`, clause 2 (the even-`n`
exceptional case that Mathlib omits) from `reducible_of_neg_four_mul_pow4`. -/
theorem vahlen_capelli_necessity {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    {a : K} (h : Irreducible (X ^ n - C a)) : VahlenCapelliCond n a := by
  refine ⟨?_, ?_⟩
  · intro p hp hpn b hbp
    exact reducible_of_prime_pow_eq hn hp hpn hbp h
  · intro h4 b hab
    exact reducible_of_neg_four_mul_pow4 hn h4 hab h

/-- **The full Vahlen–Capelli criterion for odd `n`.**  For odd `n` the `4 ∣ n`
clause is vacuous, so the criterion reduces exactly to Mathlib's
`X_pow_sub_C_irreducible_iff_forall_prime_of_odd`. -/
theorem vahlen_capelli_of_odd {K : Type*} [Field K] {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ VahlenCapelliCond n a := by
  have hnot4 : ¬ (4 ∣ n) := by
    rintro ⟨k, rfl⟩
    rw [Nat.odd_iff] at hn
    omega
  rw [X_pow_sub_C_irreducible_iff_forall_prime_of_odd hn]
  unfold VahlenCapelliCond
  exact ⟨fun h => ⟨h, fun h4 => absurd h4 hnot4⟩, fun h => h.1⟩

/-- **The full Vahlen–Capelli criterion, all `n > 0`.**

The **necessity** direction (`→`) is fully proved by `vahlen_capelli_necessity`,
including the delicate `4 ∣ n` exceptional clause.

The **sufficiency** direction (`←`) is complete for odd `n`
(`vahlen_capelli_of_odd`, via Mathlib) but the **even-`n`** sufficiency is the
deep half of the theorem and remains open here — it is exactly the
`TODO: criteria for even n` that Mathlib's `KummerExtension` leaves unproved.
This single `sorry` is the genuine research frontier of this problem. -/
theorem vahlen_capelli {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) {a : K} :
    Irreducible (X ^ n - C a) ↔ VahlenCapelliCond n a := by
  refine ⟨vahlen_capelli_necessity hn, ?_⟩
  intro hcond
  -- Sufficiency: odd `n` is `vahlen_capelli_of_odd`; even `n` is the open case.
  sorry

end CubeRoot3IrrationalOQ02OQ03
