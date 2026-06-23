import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-
# The trichotomy of `(n-1)! mod n` — the complete classification, ZMod-free

**Open Question (`wilsons-theorem-oq-05-oq-01`)**: package Wilson's theorem and
its converse into a *single closed-form* description of the bare remainder
`(n - 1)! % n`, valid for every `n ≥ 2`:

```
                 ⎧ n - 1   if n is prime,
(n - 1)! % n  =  ⎨ 2       if n = 4,
                 ⎩ 0       if n is composite and n > 4.
```

## What is genuinely new here

The sibling entry `Proofs/WilsonsTheoremOQ01.lean` already proves the trichotomy,
but as a three-way *disjunction* whose residues live in `ZMod n`
(`wilson_complete_classification`), and it discharges the exceptional `n = 4`
branch with `native_decide` (hence depends on `Lean.ofReduceBool`).  The parent
entry `Proofs/WilsonsTheoremOQ05.lean` argues that the classically-stated,
`ZMod`-free remainder form `(n - 1)! % n = n - 1` is the genuinely useful shape,
but only supplies the *prime* branch in that form.

This file completes that programme: it states the **full** classification as one
honest closed-form equation between natural numbers,

  `factorial_pred_mod : 2 ≤ n → (n-1)! % n = if n.Prime then n - 1 else if n = 4 then 2 else 0`,

with **no `ZMod` anywhere in any statement** and **no `native_decide`** (the
`n = 4` branch is closed by `decide` on a `Nat` equality, which is axiom-free).
On top of it sit two crisp structural consequences that the disjunction form does
not isolate:

* `mod_eq_zero_iff_composite` : for `n ≥ 2`, `(n-1)! % n = 0 ↔ (¬ n.Prime ∧ n ≠ 4)`
  — the remainder vanishes *exactly* on the genuine composites, the clean
  "compositeness is detected by a zero remainder" half of the criterion.
* `four_unique_anomaly` : for `n ≥ 2`, `n = 4` is the **unique** value at which the
  remainder is neither `0` nor `n - 1`.  Wilson's theorem says primes give `n - 1`
  and (almost all) composites give `0`; this pins down `4` as the lone exception.

To keep the file self-contained and `native_decide`-free it re-derives the two
inputs from Mathlib directly: the prime remainder identity (from
`Nat.prime_iff_fac_equiv_neg_one`) and the composite divisibility
`n ∣ (n-1)!` for composite `n > 4` (two distinct factors `< n`, with the
perfect-square subcase `n = p²` handled by the pair `p, 2p`).

Fully machine-checked: `0` sorries, `0` axioms (no `native_decide`).
-/

namespace WilsonsTheoremOQ05OQ01

open Nat
open scoped Nat

/-! ## Inputs, re-derived from Mathlib (self-contained, `native_decide`-free) -/

/-- The natural number `n - 1` reduces to `-1` in `ZMod n` (for `n ≥ 1`). The
hinge that turns Mathlib's `ZMod`-valued Wilson statement into a remainder. -/
theorem natCast_pred_eq_neg_one {n : ℕ} (hn : 1 ≤ n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  have h : ((n - 1 : ℕ) : ZMod n) = (n : ZMod n) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [h, ZMod.natCast_self, zero_sub]

/-- **Prime branch (remainder form).** For prime `n`, `(n-1)! % n = n - 1`.
Re-derived from `Nat.prime_iff_fac_equiv_neg_one`. -/
theorem factorial_pred_mod_of_prime {n : ℕ} (hp : Nat.Prime n) :
    (n - 1)! % n = n - 1 := by
  have hn1 : n ≠ 1 := hp.one_lt.ne'
  have h2 : 2 ≤ n := hp.two_le
  have hzmod : ((n - 1)! : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    rw [(Nat.prime_iff_fac_equiv_neg_one hn1).mp hp, natCast_pred_eq_neg_one (by omega)]
  have hcong : (n - 1)! ≡ n - 1 [MOD n] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hzmod
  -- `n - 1 < n`, so its residue is itself
  have hlt : n - 1 < n := by omega
  calc (n - 1)! % n = (n - 1) % n := hcong
    _ = n - 1 := Nat.mod_eq_of_lt hlt

/-- `n! = ∏_{k=1}^{n} k`, as a product over `Finset.Icc 1 n`. -/
theorem factorial_eq_Icc_prod (n : ℕ) : n.factorial = (Finset.Icc 1 n).prod id := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ m ih =>
    rw [Nat.factorial_succ, ih]
    have hmem : m + 1 ∉ Finset.Icc 1 m := by simp
    have hinsert : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hinsert, Finset.prod_insert hmem, id, mul_comm]

/-- If `a, b` are distinct elements of `{1, …, n}`, then `a * b ∣ n!`. -/
theorem distinct_factors_dvd_factorial {a b n : ℕ}
    (ha : 1 ≤ a) (ha' : a ≤ n) (hb : 1 ≤ b) (hb' : b ≤ n) (hab : a ≠ b) :
    a * b ∣ n.factorial := by
  rw [factorial_eq_Icc_prod]
  have hpair : ({a, b} : Finset ℕ).prod id = a * b := by
    rw [Finset.prod_pair hab]; rfl
  rw [← hpair]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl <;> omega

/-- **Composite branch (divisibility).** For composite `n > 4`, `n ∣ (n-1)!`.
The two distinct factors are `minFac n` and its cofactor; the perfect-square
case `n = p²` (where the cofactor coincides with `p`) uses the pair `p, 2p`. -/
theorem composite_factorial_dvd {n : ℕ} (hn_comp : ¬Nat.Prime n) (hn_gt : n > 4) :
    n ∣ (n - 1).factorial := by
  have hn_pos : 0 < n := by omega
  have hn_ne_one : n ≠ 1 := by omega
  set p := n.minFac with hp_def
  have hp_prime : Nat.Prime p := Nat.minFac_prime hn_ne_one
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_gt_one : 1 < p := hp_prime.one_lt
  set q := n / p with hq_def
  have hpq : p * q = n := Nat.mul_div_cancel' hp_dvd
  have hp_sq_le : p ^ 2 ≤ n := Nat.minFac_sq_le_self hn_pos hn_comp
  have hq_ge_p : p ≤ q := by
    by_contra h
    push_neg at h
    have h1 : p * q < p * p := by nlinarith
    nlinarith
  have hq_gt_one : 1 < q := by linarith
  have hp_lt_n : p < n := by nlinarith
  have hq_lt_n : q < n := by nlinarith
  by_cases hpq_eq : p = q
  · -- Case n = p² (p = q), forcing p ≥ 3
    have hn_eq : n = p * p := by rw [← hpq, hpq_eq]
    have hp_ge_3 : p ≥ 3 := by
      by_contra h
      push_neg at h
      have hp2 : p = 2 := by omega
      rw [hp2] at hn_eq; omega
    have h2p_lt : 2 * p < p * p := by nlinarith
    have h2p_le : 2 * p ≤ n - 1 := by omega
    have hp_ne_2p : p ≠ 2 * p := by omega
    have h_prod_dvd : p * (2 * p) ∣ (n - 1).factorial :=
      distinct_factors_dvd_factorial (by omega) (by omega) (by omega) h2p_le hp_ne_2p
    have h_pp_dvd : p * p ∣ p * (2 * p) := ⟨2, by ring⟩
    have h_goal : p * p ∣ (n - 1).factorial := dvd_trans h_pp_dvd h_prod_dvd
    exact hn_eq ▸ h_goal
  · -- Case p ≠ q, both in {1, …, n-1}
    rw [← hpq]
    exact distinct_factors_dvd_factorial (by omega) (by omega) (by omega) (by omega) hpq_eq

/-- **Composite branch (remainder form).** For composite `n > 4`, `(n-1)! % n = 0`. -/
theorem factorial_pred_mod_of_composite {n : ℕ} (hn_comp : ¬Nat.Prime n) (hn_gt : n > 4) :
    (n - 1)! % n = 0 := by
  obtain ⟨k, hk⟩ := composite_factorial_dvd hn_comp hn_gt
  rw [hk, Nat.mul_mod_right]

/-- **Exceptional branch.** `(4-1)! % 4 = 2`, by `decide` on a `Nat` equality
(axiom-free; no `native_decide`). -/
theorem factorial_pred_mod_four : (4 - 1)! % 4 = 2 := by decide

/-! ## The headline closed-form classification -/

/-- **Trichotomy of `(n-1)! mod n`, ZMod-free closed form.** For every `n ≥ 2`,

```
(n - 1)! % n = if n.Prime then n - 1 else if n = 4 then 2 else 0.
```

A single closed-form equation between natural numbers, with no `ZMod` and no
`native_decide`: the prime regime gives the Wilson residue `n - 1 (= -1)`, the
lone anomaly `n = 4` gives `2`, and every genuine composite gives `0`. -/
theorem factorial_pred_mod {n : ℕ} (hn : 2 ≤ n) :
    (n - 1)! % n = if n.Prime then n - 1 else if n = 4 then 2 else 0 := by
  by_cases hp : Nat.Prime n
  · rw [if_pos hp]; exact factorial_pred_mod_of_prime hp
  · rw [if_neg hp]
    by_cases h4 : n = 4
    · rw [if_pos h4, h4]; exact factorial_pred_mod_four
    · rw [if_neg h4]
      have hgt4 : n > 4 := by
        by_contra h_le
        push_neg at h_le
        interval_cases n
        · exact hp Nat.prime_two
        · exact hp Nat.prime_three
        · exact h4 rfl
      exact factorial_pred_mod_of_composite hp hgt4

/-! ## Structural consequences not isolated by the disjunction form -/

/-- **Compositeness is detected by a zero remainder.** For `n ≥ 2`,
`(n-1)! % n = 0` *exactly* when `n` is a genuine composite (`¬ Prime` and `≠ 4`).
This is the clean "if" half of the Wilson primality criterion in remainder form:
the converse of Wilson, with the `n = 4` exception explicitly excised. -/
theorem mod_eq_zero_iff_composite {n : ℕ} (hn : 2 ≤ n) :
    (n - 1)! % n = 0 ↔ (¬ Nat.Prime n ∧ n ≠ 4) := by
  rw [factorial_pred_mod hn]
  constructor
  · intro h
    by_cases hp : Nat.Prime n
    · rw [if_pos hp] at h; omega
    · refine ⟨hp, ?_⟩
      rw [if_neg hp] at h
      by_cases h4 : n = 4
      · rw [if_pos h4] at h; omega
      · exact h4
  · rintro ⟨hp, h4⟩
    rw [if_neg hp, if_neg h4]

/-- **`n = 4` is the unique remainder anomaly.** For `n ≥ 2`, the remainder
`(n-1)! % n` fails to be one of the two "expected" values `0` (composite) or
`n - 1` (prime) at *exactly* one number, `n = 4`, where it equals `2`. -/
theorem four_unique_anomaly {n : ℕ} (hn : 2 ≤ n) :
    ((n - 1)! % n ≠ 0 ∧ (n - 1)! % n ≠ n - 1) ↔ n = 4 := by
  rw [factorial_pred_mod hn]
  constructor
  · rintro ⟨hne0, hnep⟩
    by_cases hp : Nat.Prime n
    · rw [if_pos hp] at hnep; exact absurd rfl hnep
    · rw [if_neg hp] at hne0 hnep
      by_cases h4 : n = 4
      · exact h4
      · rw [if_neg h4] at hne0; exact absurd rfl hne0
  · intro h4
    subst h4
    rw [if_neg (by decide : ¬ Nat.Prime 4), if_pos rfl]
    exact ⟨by decide, by decide⟩

end WilsonsTheoremOQ05OQ01
