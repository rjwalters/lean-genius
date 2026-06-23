import Mathlib

/-
# Erdős #1004 — Why Totient Fibers Are Finite: the Elementary Bound `φ(n)² ≥ n/2`

## Background
Erdős #1004 asks how long a run of *distinct* consecutive totient values
`φ(n+1), φ(n+2), …, φ(n+K)` can be.  For this to be a meaningful arithmetic
question at all, each individual totient value must be attained by only
*finitely many* integers — otherwise the distinctness of values would carry no
information.  The companion entry (oq-03) bounds the run *length* `K` from above;
this entry supplies the complementary structural fact: the totient is
**finite-to-one**, with an explicit, fully elementary fiber bound.

## What this file proves (0 axioms, no `native_decide`)
The classical lower bound

    φ(n)² ≥ n/2,    equivalently    n ≤ 2·φ(n)²,            (★)

for every `n`, together with the sharp **odd refinement**

    n odd  ⟹  n ≤ φ(n)².

From (★) we read off the explicit fiber bound `φ(n) = v ⟹ n ≤ 2v²`, hence every
totient value is attained by only finitely many integers (`totient_fiber_finite`).
(★) is **sharp** at `n = 2`, where `2·φ(2)² = 2·1 = 2`.  A real-analytic
restatement `√(n/2) ≤ φ(n)` is recorded as well.

## The idea
Both bounds are *multiplicative invariants*.  Factoring `n` into coprime
prime powers, the inequality is tight only at the single prime power `2¹`
(`φ(2) = 1`).  We therefore package the two bounds as the **conjunction**

    P(n) :  (Odd n → n ≤ φ(n)²)  ∧  (n ≤ 2·φ(n)²)

and prove it by `Nat.recOnPosPrimePosCoprime`.  In a coprime product `a·b` at
most one factor is even, so the lone "factor of 2" deficit from the prime `2` is
never spent twice — which is exactly why the strengthened conjunction is closed
under coprime multiplication.  Per prime power the bound is a one-variable
polynomial inequality dispatched by `nlinarith`.
-/

namespace Erdos1004OQ02

open Nat

/-! ### Per-prime-power core inequalities -/

/-- For an odd prime `p` (`p ≥ 3`) and exponent `k ≥ 1`, the totient of the
prime power already beats the square root: `p^k ≤ φ(p^k)²`. -/
lemma primePow_odd_bound {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 1 ≤ k) :
    p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  set Q := p ^ j with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  -- base case `p ≤ (p-1)²` for `p ≥ 3`
  have key : p ≤ (p - 1) ^ 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 3 := ⟨p - 3, by omega⟩
    have hsub : (m + 3) - 1 = m + 2 := rfl
    rw [hsub]; nlinarith
  calc Q * p ≤ Q * (p - 1) ^ 2 := by gcongr
    _ ≤ Q ^ 2 * (p - 1) ^ 2 := by gcongr; nlinarith [hQ1]
    _ = (Q * (p - 1)) ^ 2 := by ring

/-- For any prime `p` and exponent `k ≥ 1`, `p^k ≤ 2·φ(p^k)²`.  (The factor of
`2` is needed only for `p = 2`.) -/
lemma primePow_two_bound {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    p ^ k ≤ 2 * (Nat.totient (p ^ k)) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  have h2 : 2 ≤ p := hp.two_le
  set Q := p ^ j with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  -- base case `p ≤ 2·(p-1)²` for `p ≥ 2`
  have key : p ≤ 2 * (p - 1) ^ 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
    have hsub : (m + 2) - 1 = m + 1 := rfl
    rw [hsub]; nlinarith
  calc Q * p ≤ Q * (2 * (p - 1) ^ 2) := by gcongr
    _ ≤ Q ^ 2 * (2 * (p - 1) ^ 2) := by gcongr; nlinarith [hQ1]
    _ = 2 * (Q * (p - 1)) ^ 2 := by ring

/-! ### The multiplicative invariant -/

/-- The strengthened, multiplicatively-closed invariant proved for all `n`. -/
theorem totient_invariant (n : ℕ) :
    (Odd n → n ≤ (Nat.totient n) ^ 2) ∧ (n ≤ 2 * (Nat.totient n) ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      have hpp : p.Prime := hp
      refine ⟨?_, primePow_two_bound hpp (by omega)⟩
      intro hodd
      -- `Odd (p^k)` forces `p ≠ 2`, hence `p ≥ 3`
      have hp3 : 3 ≤ p := by
        rcases hpp.eq_two_or_odd' with rfl | hpodd
        · exact absurd hodd (Nat.not_odd_iff_even.mpr
            (Nat.even_pow.mpr ⟨even_two, by omega⟩))
        · obtain ⟨t, ht⟩ := hpodd
          have := hpp.two_le; omega
      exact primePow_odd_bound hpp hp3 (by omega)
  | zero => exact ⟨fun h => absurd h (by decide), Nat.zero_le _⟩
  | one => exact ⟨fun _ => by simp [Nat.totient_one], by simp [Nat.totient_one]⟩
  | coprime a b ha hb hcop Pa Pb =>
      obtain ⟨Pa1, Pa2⟩ := Pa
      obtain ⟨Pb1, Pb2⟩ := Pb
      rw [Nat.totient_mul hcop]
      refine ⟨?_, ?_⟩
      · -- odd part: both factors odd, neither needs the factor of 2
        intro hodd
        obtain ⟨hoa, hob⟩ := odd_mul.mp hodd
        calc a * b ≤ (Nat.totient a) ^ 2 * (Nat.totient b) ^ 2 :=
              Nat.mul_le_mul (Pa1 hoa) (Pb1 hob)
          _ = (Nat.totient a * Nat.totient b) ^ 2 := by ring
      · -- general part: at most one factor is even, so spend the `2` there
        rcases Nat.even_or_odd a with hae | hao
        · -- `a` even ⟹ `b` odd (coprimality)
          have hob : Odd b := by
            rw [← Nat.not_even_iff_odd]
            intro hbe
            have hdvd : (2 : ℕ) ∣ Nat.gcd a b :=
              Nat.dvd_gcd (even_iff_two_dvd.mp hae) (even_iff_two_dvd.mp hbe)
            rw [Nat.Coprime] at hcop
            rw [hcop] at hdvd
            exact absurd hdvd (by decide)
          calc a * b ≤ (2 * (Nat.totient a) ^ 2) * (Nat.totient b) ^ 2 :=
                Nat.mul_le_mul Pa2 (Pb1 hob)
            _ = 2 * (Nat.totient a * Nat.totient b) ^ 2 := by ring
        · -- `a` odd ⟹ use the bare bound for `a`, factor of 2 for `b`
          calc a * b ≤ (Nat.totient a) ^ 2 * (2 * (Nat.totient b) ^ 2) :=
                Nat.mul_le_mul (Pa1 hao) Pb2
            _ = 2 * (Nat.totient a * Nat.totient b) ^ 2 := by ring

/-! ### Headline results -/

/-- **Main bound (★).** For every `n`, `n ≤ 2·φ(n)²`, i.e. `φ(n) ≥ √(n/2)`.
Sharp at `n = 2`. -/
theorem totient_sq_two_ge (n : ℕ) : n ≤ 2 * (Nat.totient n) ^ 2 :=
  (totient_invariant n).2

/-- **Odd refinement.** For odd `n`, the bound holds without the factor of `2`:
`n ≤ φ(n)²`. -/
theorem totient_sq_ge_of_odd {n : ℕ} (h : Odd n) : n ≤ (Nat.totient n) ^ 2 :=
  (totient_invariant n).1 h

/-- Sharpness of `(★)` at `n = 2`: equality `2 = 2·φ(2)²`. -/
example : 2 = 2 * (Nat.totient 2) ^ 2 := by decide

/-- **Explicit fiber bound.** If `φ(n) = v` then `n ≤ 2v²`: every preimage of a
totient value lies in an explicit finite initial segment. -/
theorem totient_fiber_bound {n v : ℕ} (h : Nat.totient n = v) : n ≤ 2 * v ^ 2 := by
  rw [← h]; exact totient_sq_two_ge n

/-- **The totient is finite-to-one.**  Each value `v` is attained by only
finitely many integers — the structural reason runs of distinct consecutive
totient values (Erdős #1004) are a well-posed object of study. -/
theorem totient_fiber_finite (v : ℕ) : {n : ℕ | Nat.totient n = v}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (2 * v ^ 2))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  exact totient_fiber_bound hn

/-- **Real-analytic restatement.** `√(n/2) ≤ φ(n)` for every `n`. -/
theorem totient_ge_sqrt_half (n : ℕ) :
    Real.sqrt ((n : ℝ) / 2) ≤ (Nat.totient n : ℝ) := by
  have hb : (n : ℝ) ≤ 2 * (Nat.totient n : ℝ) ^ 2 := by exact_mod_cast totient_sq_two_ge n
  have h2 : (n : ℝ) / 2 ≤ (Nat.totient n : ℝ) ^ 2 := by linarith
  calc Real.sqrt ((n : ℝ) / 2)
        ≤ Real.sqrt ((Nat.totient n : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
    _ = (Nat.totient n : ℝ) := Real.sqrt_sq (by positivity)

end Erdos1004OQ02
