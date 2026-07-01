/-
  Angle Trisection OQ-03 OQ-02 OQ-03: The Halvings Count IS the p-adic Valuation

  The parent (AngleTrisectionOQ03OQ02) introduced an ad-hoc `halvings` step counter:
  repeatedly halve d until it becomes odd, and count the steps. That entry proved the
  count is Θ(log d) — exactly k on inputs d = 2^k.

  This entry answers the open question by IDENTIFYING that ad-hoc counter with a
  standard arithmetic object:

      halvings n = padicValNat 2 n        (the 2-adic valuation v₂(n))

  and then GENERALIZES the entire complexity story to an arbitrary prime p. We define
  a p-adic halving counter `pHalvings p` — repeatedly divide by p while divisible —
  and prove:

    * pHalvings p n = padicValNat p n            (the counter is the p-adic valuation)
    * halvings n    = pHalvings 2 n              (the parent is the p = 2 instance)
    * pHalvings p (p^k) = k = Nat.log p (p^k)    (Θ(logₚ d): the count is tight)
    * the count is unbounded, and separates p^k from the immediately-rejected p^k − 1.

  Everything below is fully machine-checked with no axioms or sorries.

  Companion to AngleTrisectionOQ03OQ02.lean (the p = 2 special case).
-/

import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Proofs.AngleTrisectionOQ03OQ02

namespace AngleTrisectionOQ03OQ02OQ03

open AngleTrisectionOQ03OQ02 Nat

/-!
## Part I: The Halvings Count is the 2-adic Valuation

The parent's `halvings` function counts how many times 2 divides its input. That is
precisely the definition of the 2-adic valuation `padicValNat 2`. We prove the two
agree on every input by strong induction, using the parent's own recursion lemmas.
-/

/-- **Central identification**: the ad-hoc halvings step counter equals the standard
    2-adic valuation `v₂(n) = padicValNat 2 n`.

    Strong induction with a three-way split on `n`:
    * `n = 0`: both are `0`;
    * `n` odd: both are `0` (odd numbers carry no factor of `2`);
    * `n = 2·k` with `k > 0`: both peel one factor, reducing to `1 + (value at k)`. -/
theorem halvings_eq_padicValNat_two (n : ℕ) : halvings n = padicValNat 2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rcases Nat.even_or_odd n with he | ho
      · -- even and positive: write n = 2 * k with k > 0
        obtain ⟨k, rfl⟩ := he.two_dvd
        have hk : 0 < k := by omega
        rw [halvings_two_mul hk, ih k (by omega),
            padicValNat.mul two_ne_zero (by omega), padicValNat.self (by norm_num)]
      · -- odd: neither counts a factor of 2
        have hodd : n % 2 = 1 := Nat.odd_iff.mp ho
        rw [halvings_odd hodd, padicValNat.eq_zero_of_not_dvd (by omega)]

/-- Restated with the classical `v₂` name: the constructibility algorithm's step count
    on input `n` is exactly the 2-adic valuation of `n`. -/
theorem halvings_eq_two_adic_valuation (n : ℕ) :
    halvings n = padicValNat 2 n := halvings_eq_padicValNat_two n

/-!
## Part II: A p-adic Halving Counter for an Arbitrary Prime

We generalize the parent's algorithm: `pHalvings p n` repeatedly divides `n` by `p`
while `p ∣ n`, counting the steps. The guard `1 < p` in the recursion is what makes
the quotient strictly smaller, so the definition terminates for every `p` (and is a
harmless constant `0` for the degenerate `p ≤ 1`).
-/

/-- Count the p-adic halvings of `n`: how many times `p` divides out of `n`. -/
def pHalvings (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
      if p ∣ (n + 1) ∧ 1 < p then 1 + pHalvings p ((n + 1) / p) else 0
  termination_by n => n
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by omega)

@[simp] theorem pHalvings_zero (p : ℕ) : pHalvings p 0 = 0 := by rw [pHalvings]

/-- Equation lemma for the successor case. -/
theorem pHalvings_succ (p n : ℕ) :
    pHalvings p (n + 1)
      = if p ∣ (n + 1) ∧ 1 < p then 1 + pHalvings p ((n + 1) / p) else 0 := by
  rw [pHalvings]

/-- If `p` does not divide `m`, the algorithm stops immediately with count `0`. -/
theorem pHalvings_eq_zero_of_not_dvd {p m : ℕ} (hd : ¬ p ∣ m) : pHalvings p m = 0 := by
  cases m with
  | zero => simp
  | succ n => rw [pHalvings_succ, if_neg (fun h => hd h.1)]

/-- The recursion step: for `1 < p`, `p ∣ m` and `m > 0`, one halving is peeled off. -/
theorem pHalvings_of_dvd {p m : ℕ} (hp : 1 < p) (hd : p ∣ m) (hm : 0 < m) :
    pHalvings p m = 1 + pHalvings p (m / p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [pHalvings_succ, if_pos ⟨hd, hp⟩]

/-!
## Part III: The Counter is the p-adic Valuation

The same three-way strong induction now identifies `pHalvings p` with `padicValNat p`
for every prime `p`. This is the exact generalization of Part I.
-/

/-- **Main generalization**: for a prime `p`, the p-adic halving count equals the
    p-adic valuation `padicValNat p n`. -/
theorem pHalvings_eq_padicValNat {p : ℕ} (hp : p.Prime) (n : ℕ) :
    pHalvings p n = padicValNat p n := by
  have hp1 : 1 < p := hp.one_lt
  haveI : Fact p.Prime := ⟨hp⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · by_cases hd : p ∣ n
      · -- p ∣ n: write n = p * k with k > 0, peel one factor from each side
        obtain ⟨k, rfl⟩ := hd
        have hk : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · simp [h] at hn
          · exact h
        rw [pHalvings_of_dvd hp1 ⟨k, rfl⟩ hn, Nat.mul_div_cancel_left k (by omega),
            ih k (lt_mul_of_one_lt_left hk hp1), padicValNat.mul (by omega) (by omega),
            padicValNat.self hp1]
      · -- p ∤ n: both sides are 0
        rw [pHalvings_eq_zero_of_not_dvd hd, padicValNat.eq_zero_of_not_dvd hd]

/-- The parent's 2-adic algorithm is exactly the `p = 2` instance of the general one. -/
theorem halvings_eq_pHalvings_two (n : ℕ) : halvings n = pHalvings 2 n := by
  rw [halvings_eq_padicValNat_two n, pHalvings_eq_padicValNat Nat.prime_two n]

/-!
## Part IV: Θ(logₚ d) — the Generalized Tightness Bound

For inputs `d = p^k` the counter returns exactly `k`, matching the floor logarithm
`Nat.log p (p^k) = k`. This is the direct analogue of the parent's Ω(log d) result,
now for every prime base `p`.
-/

/-- **Exact step count**: `pHalvings p (p^k) = k`. -/
theorem pHalvings_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    pHalvings p (p ^ k) = k := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [pHalvings_eq_padicValNat hp, padicValNat.prime_pow]

/-- The count matches the base-`p` floor logarithm on inputs `p^k`. -/
theorem pHalvings_eq_log_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    pHalvings p (p ^ k) = Nat.log p (p ^ k) := by
  rw [pHalvings_prime_pow hp, Nat.log_pow hp.one_lt]

/-- **Θ(logₚ d) tightness**: the count and the floor logarithm agree exactly on `p^k`,
    and both equal `k`. -/
theorem pHalvings_complexity_tight {p : ℕ} (hp : p.Prime) (k : ℕ) :
    pHalvings p (p ^ k) = Nat.log p (p ^ k) ∧ Nat.log p (p ^ k) = k :=
  ⟨pHalvings_eq_log_prime_pow hp k, Nat.log_pow hp.one_lt k⟩

/-- The step count is unbounded: no constant bounds the p-adic halving count. -/
theorem pHalvings_unbounded {p : ℕ} (hp : p.Prime) (c : ℕ) :
    ∃ d : ℕ, pHalvings p d ≥ c :=
  ⟨p ^ c, by rw [pHalvings_prime_pow hp]⟩

/-- Larger powers of `p` require more halvings (monotone in the exponent). -/
theorem pHalvings_monotone_prime_pow {p : ℕ} (hp : p.Prime) {i j : ℕ} (h : i ≤ j) :
    pHalvings p (p ^ i) ≤ pHalvings p (p ^ j) := by
  rw [pHalvings_prime_pow hp, pHalvings_prime_pow hp]; exact h

/-!
## Part V: Separation of Powers from Non-Powers

Just as `2^k − 1` is odd and rejected immediately, `p^k − 1` is never divisible by `p`
(for `k ≥ 1`), so the counter rejects it at the first step while accepting `p^k` after
`k` halvings. This confirms the `Θ(logₚ d)` cost is inherent to the YES-path.
-/

/-- For `k ≥ 1`, `p ∤ (p^k − 1)`, so the counter returns `0` immediately. -/
theorem pHalvings_pred_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    pHalvings p (p ^ k - 1) = 0 := by
  apply pHalvings_eq_zero_of_not_dvd
  intro hdvd
  have hpk : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
  have hge : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have h1 : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub hpk hdvd
  rw [show p ^ k - (p ^ k - 1) = 1 from by omega] at h1
  have := Nat.le_of_dvd one_pos h1
  have := hp.one_lt
  omega

/-- The halving count separates `p^k` from `p^k − 1` for `k ≥ 1`. -/
theorem pHalvings_separates_pred {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    pHalvings p (p ^ k - 1) < pHalvings p (p ^ k) := by
  rw [pHalvings_pred_prime_pow hp hk, pHalvings_prime_pow hp]
  omega

/-!
## Part VI: Concrete Computations

Numerical verification across several prime bases. (In `example` blocks only.)
-/

-- p = 2 recovers the parent's halvings values
example : pHalvings 2 (2 ^ 5) = 5 := by native_decide
example : halvings 12 = pHalvings 2 12 := by native_decide

-- p = 3
example : pHalvings 3 (3 ^ 4) = 4 := by native_decide
example : pHalvings 3 54 = 3 := by native_decide   -- 54 = 2 · 27 = 2 · 3^3
example : pHalvings 3 10 = 0 := by native_decide    -- 3 ∤ 10

-- p = 5
example : pHalvings 5 (5 ^ 3) = 3 := by native_decide
example : pHalvings 5 (5 ^ 3 - 1) = 0 := by native_decide  -- 124 not divisible by 5

end AngleTrisectionOQ03OQ02OQ03
