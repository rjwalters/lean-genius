/-
# Eisenstein Irreducibility for Squarefree Radicands: X^n − m and ⁿ√m

**Open Question OQ-04** (of `cube-root-3-irrational-oq-02`):
The parent gives an Eisenstein proof that X³ − 3 is irreducible over ℚ.
Does the Eisenstein approach extend to **non-prime** radicands? The seeker note asks:
X^n − 6 is Eisenstein-irreducible (at p = 2 or 3), X^n − 30 at p = 2, 3, or 5 —
does *any squarefree* m give an Eisenstein-irreducible X^n − m?

## Answer: YES — squarefree is sufficient (but not necessary)

The dependency `CubeRoot2IrrationalOQ03` already proves the *criterion form*:
if m has a prime factor p with p ∣ m but p² ∤ m, then X^n − m is irreducible over ℚ.
This file connects that criterion to Mathlib's `Squarefree` predicate and draws the
sharp boundary the open question is fishing for.

1. **Squarefree ⟹ Eisenstein prime exists.** For squarefree m ≥ 2, *every* prime
   divisor p satisfies p² ∤ m (that is the definition of squarefree), and m ≥ 2
   guarantees at least one prime divisor exists. So the criterion always applies.

2. **Irreducibility.** Hence `Squarefree m → 2 ≤ m → 2 ≤ n → Irreducible (Xⁿ − m)` over ℚ.

3. **Irrationality.** An irreducible polynomial of degree ≥ 2 has no rational root,
   so `Squarefree m → 2 ≤ m → 2 ≤ n → Irrational (ⁿ√m)`. This generalizes the
   parent's ∛3 result to *every* squarefree radicand and *every* root degree.

4. **Field degree.** `[ℚ(ⁿ√m) : ℚ] = n` for squarefree m ≥ 2 (via the parent's degree
   machinery), reproving cbrt6 / cbrt10 / fourthrt30 as instances of one clean hypothesis.

5. **Sharp boundary — sufficient, NOT necessary.** Squarefreeness is *not* required:
   m = 12 = 2²·3 is not squarefree, yet X^n − 12 is still Eisenstein-irreducible at
   p = 3 (since 3 ∥ 12). The true criterion is "some prime exactly divides m", which is
   strictly weaker than squarefree. We witness this explicitly.

## Status: 0 sorries, axiom-free (relative to Mathlib)
-/

import Proofs.CubeRoot2IrrationalOQ03
import Mathlib.NumberTheory.Real.Irrational

open Polynomial IntermediateField CubeRoot2IrrationalOQ03

namespace CubeRoot3IrrationalOQ02OQ04

-- ============================================================
-- PART 1: Squarefree radicands admit an Eisenstein prime
-- ============================================================

/-- For a squarefree `m ≥ 2` there is a prime `p` with `p ∣ m` but `p² ∤ m`.

Existence of a prime divisor comes from `m ≠ 1`. Squarefreeness upgrades it to an
*Eisenstein* prime: if `p² ∣ m` then `p * p ∣ m`, so `Squarefree m` would force
`IsUnit p`, impossible for a prime. Thus `p ∥ m` (p exactly divides m). -/
theorem sqfree_exists_eisenstein_prime {m : ℕ} (hsf : Squarefree m) (hm : 2 ≤ m) :
    ∃ p, p.Prime ∧ p ∣ m ∧ ¬ p ^ 2 ∣ m := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨p, hp, hpd, ?_⟩
  intro hp2
  have hpp : p * p ∣ m := by rw [← pow_two]; exact hp2
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p hpp))

-- ============================================================
-- PART 2: Irreducibility of X^n − m for squarefree m
-- ============================================================

/-- **Main irreducibility result.** For squarefree `m ≥ 2` and `n ≥ 2`, the polynomial
`Xⁿ − m` is irreducible over ℚ. Every squarefree radicand yields an Eisenstein-irreducible
`Xⁿ − m`, answering the open question. -/
theorem X_pow_sub_C_irreducible_of_squarefree {m : ℕ} (hsf : Squarefree m) (hm : 2 ≤ m)
    {n : ℕ} (hn : 2 ≤ n) : Irreducible (X ^ n - C (m : ℚ) : ℚ[X]) := by
  obtain ⟨p, hp, hpd, hpnd⟩ := sqfree_exists_eisenstein_prime hsf hm
  exact eisenstein_X_pow_sub_of_sqfree_factor n m p hn hp hpd hpnd (by omega)

-- ============================================================
-- PART 3: No rational roots ⟹ irrationality of ⁿ√m
-- ============================================================

/-- An irreducible polynomial over ℚ of natDegree ≥ 2 has no rational root.

If `q` were a root then `(X − C q) ∣ P`; write `P = (X − C q) · R`. Irreducibility forces
one factor to be a unit. `X − C q` is not a unit (natDegree 1), and if `R` is a unit then
`natDegree P = 1`, contradicting `natDegree P ≥ 2`. -/
theorem no_rat_root_of_irreducible {P : ℚ[X]} (hirr : Irreducible P)
    (hdeg : 2 ≤ P.natDegree) (q : ℚ) : P.eval q ≠ 0 := by
  intro hroot
  have hdvd : (X - C q) ∣ P := dvd_iff_isRoot.mpr hroot
  obtain ⟨R, hR⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hR with h | h
  · -- X − C q is a unit: impossible, natDegree = 1
    have h0 : (X - C q : ℚ[X]).natDegree = 0 := natDegree_eq_zero_of_isUnit h
    rw [natDegree_X_sub_C] at h0
    exact one_ne_zero h0
  · -- R is a unit: then natDegree P = 1, contradiction with hdeg
    have hRu : R.natDegree = 0 := natDegree_eq_zero_of_isUnit h
    have hP_ne : P ≠ 0 := hirr.ne_zero
    have hXq_ne : (X - C q : ℚ[X]) ≠ 0 := X_sub_C_ne_zero q
    have hR_ne : R ≠ 0 := by
      intro h0; exact hP_ne (by rw [hR, h0, mul_zero])
    have hP1 : P.natDegree = 1 := by
      rw [hR, natDegree_mul hXq_ne hR_ne, natDegree_X_sub_C, hRu]
    omega

/-- **Irrationality from irreducibility.** If `Xⁿ − m` is irreducible over ℚ with `n ≥ 2`
and `m ≠ 0`, then the real `n`-th root `m^(1/n)` is irrational.

`m^(1/n)` is a root of `Xⁿ − m` (its `n`-th power is `m`); if it were rational it would be
a rational root of an irreducible degree-`n ≥ 2` polynomial, which is impossible. -/
theorem irrational_nthRoot_of_irreducible {m n : ℕ} (hn : 2 ≤ n) (hm : m ≠ 0)
    (hirr : Irreducible (X ^ n - C (m : ℚ) : ℚ[X])) :
    Irrational ((m : ℝ) ^ ((1 : ℝ) / n)) := by
  rintro ⟨q, hq⟩
  -- q^n = m over ℝ, hence over ℚ
  have hqn_real : (q : ℝ) ^ n = m := by
    rw [hq, ← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / n)) n,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (m : ℝ)), one_div,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega : n ≠ 0)), Real.rpow_one]
  have hqn : q ^ n = (m : ℚ) := by exact_mod_cast hqn_real
  have heval : (X ^ n - C (m : ℚ) : ℚ[X]).eval q = 0 := by
    simp [hqn]
  have hdeg : (X ^ n - C (m : ℚ) : ℚ[X]).natDegree = n :=
    natDegree_X_pow_sub_nat_eq (by omega) hm
  exact no_rat_root_of_irreducible hirr (by rw [hdeg]; exact hn) q heval

/-- **Irrationality for squarefree radicands.** For squarefree `m ≥ 2` and `n ≥ 2`, the
`n`-th root `ⁿ√m` is irrational. Generalizes the parent's ∛3 to any squarefree radicand
and any root degree. -/
theorem irrational_nthRoot_of_squarefree {m n : ℕ} (hsf : Squarefree m) (hm : 2 ≤ m)
    (hn : 2 ≤ n) : Irrational ((m : ℝ) ^ ((1 : ℝ) / n)) :=
  irrational_nthRoot_of_irreducible hn (by omega)
    (X_pow_sub_C_irreducible_of_squarefree hsf hm hn)

-- ============================================================
-- PART 4: Field extension degree for squarefree radicands
-- ============================================================

/-- **Field degree.** `[ℚ(ⁿ√m) : ℚ] = n` for squarefree `m ≥ 2` and `n ≥ 2`.
The parent proves this for numbers with an exact-prime-power factor; here the hypothesis
is the single clean condition `Squarefree m`. -/
theorem adjoin_nthRoot_squarefree_finrank {m n : ℕ} (hsf : Squarefree m) (hm : 2 ≤ m)
    (hn : 2 ≤ n) : Module.finrank ℚ ℚ⟮(m : ℝ) ^ ((1 : ℝ) / (n : ℝ))⟯ = n := by
  obtain ⟨p, hp, hpd, hpnd⟩ := sqfree_exists_eisenstein_prime hsf hm
  exact adjoin_nthRoot_finrank n m p hn hp hpd hpnd (by omega)

-- ============================================================
-- PART 5: Sharp boundary — squarefree is SUFFICIENT, not NECESSARY
-- ============================================================

/-- `12 = 2² · 3` is not squarefree: `2 * 2 = 4 ∣ 12` but `2` is not a unit. -/
theorem not_squarefree_twelve : ¬ Squarefree 12 := by
  intro h
  have h2 : IsUnit (2 : ℕ) := h 2 (by norm_num)
  rw [Nat.isUnit_iff] at h2
  norm_num at h2

/-- Yet `Xⁿ − 12` is Eisenstein-irreducible at `p = 3` (since `3 ∥ 12`: `3 ∣ 12` but `9 ∤ 12`).
This witnesses that squarefreeness of the radicand is **sufficient but not necessary** — the
genuine criterion is "some prime exactly divides `m`", which is strictly weaker. -/
theorem X_pow_sub_C_twelve_irreducible {n : ℕ} (hn : 2 ≤ n) :
    Irreducible (X ^ n - C (12 : ℚ) : ℚ[X]) :=
  eisenstein_X_pow_sub_of_sqfree_factor n 12 3 hn (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `ⁿ√12` is irrational for every `n ≥ 2`, even though `12` is not squarefree. -/
theorem irrational_nthRoot_twelve {n : ℕ} (hn : 2 ≤ n) :
    Irrational (((12 : ℕ) : ℝ) ^ ((1 : ℝ) / n)) :=
  irrational_nthRoot_of_irreducible hn (by norm_num) (X_pow_sub_C_twelve_irreducible hn)

-- ============================================================
-- PART 6: Concrete instances of the squarefree theorem
-- ============================================================

/-- `6 = 2·3` is squarefree. -/
theorem squarefree_six : Squarefree 6 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, Nat.prime_two.prime.squarefree,
         (by norm_num : Nat.Prime 3).prime.squarefree⟩

/-- `15 = 3·5` is squarefree. -/
theorem squarefree_fifteen : Squarefree 15 := by
  rw [show (15 : ℕ) = 3 * 5 by norm_num, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, (by norm_num : Nat.Prime 3).prime.squarefree,
         (by norm_num : Nat.Prime 5).prime.squarefree⟩

/-- `30 = 2·3·5` is squarefree. -/
theorem squarefree_thirty : Squarefree 30 := by
  rw [show (30 : ℕ) = 2 * 15 by norm_num, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, Nat.prime_two.prime.squarefree, squarefree_fifteen⟩

/-- `√6` is irrational (`6 = 2·3` is squarefree). -/
theorem irrational_sqrt_six : Irrational (((6 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :=
  irrational_nthRoot_of_squarefree squarefree_six (by norm_num) (by norm_num)

/-- `√30` is irrational (`30 = 2·3·5` is squarefree). -/
theorem irrational_sqrt_thirty : Irrational (((30 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :=
  irrational_nthRoot_of_squarefree squarefree_thirty (by norm_num) (by norm_num)

/-- `∛30` is irrational. -/
theorem irrational_cbrt_thirty : Irrational (((30 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) :=
  irrational_nthRoot_of_squarefree squarefree_thirty (by norm_num) (by norm_num)

end CubeRoot3IrrationalOQ02OQ04
