import Mathlib

/-
# Birthday Problem — OQ-03-OQ-01-OQ-01-OQ-03-OQ-03: The general k-fold Coincidence Threshold

## Research Problem: birthday-problem-oq-03-oq-01-oq-01-oq-03-oq-03

The parent (`birthday-problem-oq-03-oq-01-oq-01-oq-03`) proved the **k = 3** (triple)
coincidence threshold `n ≈ (6 d² ln 2)^{1/3}` via the cube-root sandwich
`(n-2)³ ≤ n(n-1)(n-2) ≤ n³`.  Its open question OQ-03 asks to **generalize to arbitrary k**:

> Show the k-fold birthday-coincidence threshold is `n = (k!·d^{k-1}·ln 2)^{1/k} + O(1)` via
> the analogous falling-factorial sandwich `(n-k+1)^k ≤ n^{\underline{k}} ≤ n^k` combined with
> rpow monotonicity, mirroring the parent's cube-root sandwich for `k = 3`.

The heuristic is the standard Poisson/expected-count balance: with `d` equally likely days, the
probability that a *fixed* set of `k` people all share a day is `1/d^{k-1}`, so the expected
number of `k`-wise coincidences is

      C(n,k) / d^{k-1}  =  n(n-1)⋯(n-k+1) / (k!·d^{k-1})  =  n^{\underline{k}} / (k!·d^{k-1}),

where `n^{\underline{k}} = ∏_{i=0}^{k-1} (n-i)` is the falling factorial.  The 50%-chance
threshold is where this expected count equals `ln 2`:

      n^{\underline{k}} / (k!·d^{k-1}) = ln 2,   i.e.   ∏_{i=0}^{k-1} (n - i) = k!·d^{k-1}·ln 2.

This file proves, **rigorously and with an explicit O(1) error bound**, that the `n` solving this
balance equation is exactly the claimed threshold to leading order:

      (k!·d^{k-1}·ln 2)^{1/k}  ≤  n  ≤  (k!·d^{k-1}·ln 2)^{1/k} + (k-1).

So `n = (k!·d^{k-1}·ln 2)^{1/k} + O(1)`, the lower order term bounded by the constant `k-1`,
**independent of `d`**.  The proof is the falling-factorial sandwich requested by OQ-03:

* `∏_{i<k} (n-i) ≤ n^k`               gives the lower bound `(k!·d^{k-1}·ln 2)^{1/k} ≤ n`;
* `(n-(k-1))^k ≤ ∏_{i<k} (n-i)`       gives the upper bound `n ≤ (k!·d^{k-1}·ln 2)^{1/k} + (k-1)`.

For `k = 3` this specializes to the parent's `(n-2)³ ≤ n(n-1)(n-2) ≤ n³` and the error bound
`k-1 = 2`, recovering the parent result exactly.

## What is proved

* `kthRoot_pow`       — the k-th-root identity `(x^k)^{1/k} = x` for `x ≥ 0`, `k ≠ 0`.
* `falling_le_pow`    — upper sandwich `∏_{i<k} (n-i) ≤ n^k`.
* `pow_le_falling`    — lower sandwich `(n-(k-1))^k ≤ ∏_{i<k} (n-i)`.
* `birthday_kfold_threshold`     — the two-sided bound above.
* `birthday_kfold_threshold_gap` — packaged as `|n − (k!·d^{k-1}·ln 2)^{1/k}| ≤ k-1`.

Tags: probability, birthday-problem, asymptotics, threshold, k-th-root, falling-factorial,
real-analysis
-/

namespace BirthdayProblemOQ03OQ01OQ01OQ03OQ03

open Real

/-- **k-th-root identity.**  `(x^k)^{1/k} = x` for `x ≥ 0` and `k ≠ 0`.  Generalizes the
parent's `cubeRoot_cube` (`k = 3`). -/
theorem kthRoot_pow {x : ℝ} {k : ℕ} (hx : 0 ≤ x) (hk : k ≠ 0) :
    (x ^ k) ^ ((k : ℝ)⁻¹) = x :=
  Real.pow_rpow_inv_natCast hx hk

/-- **Upper sandwich.**  Every factor of the falling factorial `∏_{i<k} (n-i)` is `≤ n` and is
nonnegative (as `n ≥ k-1`), so the product is `≤ nᵏ`. -/
theorem falling_le_pow (k : ℕ) (n : ℝ) (hn : (k : ℝ) - 1 ≤ n) :
    ∏ i ∈ Finset.range k, (n - (i : ℝ)) ≤ n ^ k := by
  calc ∏ i ∈ Finset.range k, (n - (i : ℝ))
      ≤ ∏ _i ∈ Finset.range k, n := by
        refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
        · -- 0 ≤ n - i
          simp only [Finset.mem_range] at hi
          have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hi
          linarith
        · -- n - i ≤ n
          have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          linarith
    _ = n ^ k := by rw [Finset.prod_const, Finset.card_range]

/-- **Lower sandwich.**  Every factor `n-i` (`i < k`) is `≥ n-(k-1) ≥ 0`, so the falling
factorial `∏_{i<k} (n-i)` is `≥ (n-(k-1))ᵏ`. -/
theorem pow_le_falling (k : ℕ) (n : ℝ) (hn : (k : ℝ) - 1 ≤ n) :
    (n - ((k : ℝ) - 1)) ^ k ≤ ∏ i ∈ Finset.range k, (n - (i : ℝ)) := by
  calc (n - ((k : ℝ) - 1)) ^ k
      = ∏ _i ∈ Finset.range k, (n - ((k : ℝ) - 1)) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range k, (n - (i : ℝ)) := by
        refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
        · -- 0 ≤ n - (k-1)
          linarith
        · -- n - (k-1) ≤ n - i,  i.e.  i ≤ k-1
          simp only [Finset.mem_range] at hi
          have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hi
          linarith

/-- **The general k-fold coincidence threshold, to leading order with explicit O(1) error.**

    If `n ≥ k-1` solves the expected-coincidence balance equation
    `∏_{i<k} (n-i) = k!·d^{k-1}·ln 2` (i.e. the expected number of `k`-wise coincidences
    equals `ln 2`, the 50%-chance criterion), then

        (k!·d^{k-1}·ln 2)^{1/k} ≤ n ≤ (k!·d^{k-1}·ln 2)^{1/k} + (k-1).

    Hence `n = (k!·d^{k-1}·ln 2)^{1/k} + O(1)`: the threshold is `(k!·d^{k-1}·ln 2)^{1/k}` up to a
    bounded additive constant `k-1`, independent of `d`.  This is the rigorous form of the
    asymptotic `n ≈ (k!·d^{k-1}·ln 2)^{1/k}` and generalizes the parent's `k = 3` result. -/
theorem birthday_kfold_threshold (k : ℕ) (d n : ℝ) (hk : 1 ≤ k) (hd : 0 < d)
    (hn : (k : ℝ) - 1 ≤ n)
    (hbal : ∏ i ∈ Finset.range k, (n - (i : ℝ))
        = (k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) :
    ((k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) ^ ((k : ℝ)⁻¹) ≤ n ∧
    n ≤ ((k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) ^ ((k : ℝ)⁻¹) + ((k : ℝ) - 1) := by
  set L := (k.factorial : ℝ) * d ^ (k - 1) * Real.log 2 with hLdef
  have hk0 : k ≠ 0 := by omega
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := by rw [hLdef]; positivity
  have hn0 : 0 ≤ n := by linarith
  have hnk : 0 ≤ n - ((k : ℝ) - 1) := by linarith
  refine ⟨?_, ?_⟩
  · -- Lower bound: L ≤ nᵏ, so L^{1/k} ≤ (nᵏ)^{1/k} = n.
    have hub : L ≤ n ^ k := by rw [← hbal]; exact falling_le_pow k n hn
    calc L ^ ((k : ℝ)⁻¹)
        ≤ (n ^ k) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow hL hub (by positivity)
      _ = n := kthRoot_pow hn0 hk0
  · -- Upper bound: (n-(k-1))ᵏ ≤ L, so n-(k-1) = ((n-(k-1))ᵏ)^{1/k} ≤ L^{1/k}.
    have hlb : (n - ((k : ℝ) - 1)) ^ k ≤ L := by rw [← hbal]; exact pow_le_falling k n hn
    have hstep : n - ((k : ℝ) - 1) ≤ L ^ ((k : ℝ)⁻¹) := by
      calc n - ((k : ℝ) - 1)
          = ((n - ((k : ℝ) - 1)) ^ k) ^ ((k : ℝ)⁻¹) := (kthRoot_pow hnk hk0).symm
        _ ≤ L ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (pow_nonneg hnk k) hlb (by positivity)
    linarith

/-- **Packaged threshold gap.**  The balance-equation solution `n` is within `k-1` of the
    leading-order threshold `(k!·d^{k-1}·ln 2)^{1/k}` — a bounded, `d`-independent error. -/
theorem birthday_kfold_threshold_gap (k : ℕ) (d n : ℝ) (hk : 1 ≤ k) (hd : 0 < d)
    (hn : (k : ℝ) - 1 ≤ n)
    (hbal : ∏ i ∈ Finset.range k, (n - (i : ℝ))
        = (k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) :
    |n - ((k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) ^ ((k : ℝ)⁻¹)| ≤ (k : ℝ) - 1 := by
  obtain ⟨hlo, hhi⟩ := birthday_kfold_threshold k d n hk hd hn hbal
  rw [abs_le]
  constructor <;> linarith

/-- **Consistency check.**  For `k = 3` the general threshold reduces to the parent's
    `(6 d² ln 2)^{1/3}` two-sided bound, since `3! = 6`, `d^{3-1} = d²`, and `k-1 = 2`. -/
theorem birthday_kfold_threshold_k3 (d n : ℝ) (hd : 0 < d) (hn : 2 ≤ n)
    (hbal : n * (n - 1) * (n - 2) = 6 * d ^ 2 * Real.log 2) :
    (6 * d ^ 2 * Real.log 2) ^ (((3 : ℕ) : ℝ)⁻¹) ≤ n ∧
    n ≤ (6 * d ^ 2 * Real.log 2) ^ (((3 : ℕ) : ℝ)⁻¹) + 2 := by
  have hexpand : ∏ i ∈ Finset.range 3, (n - (i : ℝ)) = n * (n - 1) * (n - 2) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat, one_mul]
    ring
  have hprod : ∏ i ∈ Finset.range 3, (n - (i : ℝ))
      = (Nat.factorial 3 : ℝ) * d ^ (3 - 1) * Real.log 2 := by
    rw [hexpand, hbal]; norm_num [Nat.factorial]
  have hn3 : ((3 : ℕ) : ℝ) - 1 ≤ n := by push_cast; linarith
  have h := birthday_kfold_threshold 3 d n (by norm_num) hd hn3 hprod
  have hc : (Nat.factorial 3 : ℝ) * d ^ (3 - 1) * Real.log 2 = 6 * d ^ 2 * Real.log 2 := by
    norm_num [Nat.factorial]
  have he : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
  rw [hc, he] at h
  exact h

#check @kthRoot_pow
#check @falling_le_pow
#check @pow_le_falling
#check @birthday_kfold_threshold
#check @birthday_kfold_threshold_gap
#check @birthday_kfold_threshold_k3

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `kthRoot_pow`       — `(x^k)^{1/k} = x` for `x ≥ 0`, `k ≠ 0` (generalizes parent `cubeRoot_cube`).
* `falling_le_pow`    — `∏_{i<k} (n-i) ≤ n^k`.
* `pow_le_falling`    — `(n-(k-1))^k ≤ ∏_{i<k} (n-i)`.
* `birthday_kfold_threshold`     — for `n ≥ k-1` solving `∏_{i<k}(n-i) = k!·d^{k-1}·ln 2`,
  `(k!·d^{k-1}·ln 2)^{1/k} ≤ n ≤ (k!·d^{k-1}·ln 2)^{1/k} + (k-1)`.
* `birthday_kfold_threshold_gap` — equivalently `|n − (k!·d^{k-1}·ln 2)^{1/k}| ≤ k-1`.
* `birthday_kfold_threshold_k3`  — specializes to the parent's `k = 3` `(6 d² ln 2)^{1/3}` bound.

This answers the parent's OQ-03: the general k-fold coincidence threshold is
`(k!·d^{k-1}·ln 2)^{1/k}` to leading order, with a bounded additive error of at most `k-1`
(independent of `d`), proved by the falling-factorial sandwich
`(n-(k-1))^k ≤ ∏_{i<k}(n-i) ≤ n^k` and rpow monotonicity — the exact generalization of the
parent's cube-root sandwich for `k = 3`.
-/

end BirthdayProblemOQ03OQ01OQ01OQ03OQ03

#print axioms BirthdayProblemOQ03OQ01OQ01OQ03OQ03.birthday_kfold_threshold
#print axioms BirthdayProblemOQ03OQ01OQ01OQ03OQ03.birthday_kfold_threshold_gap
