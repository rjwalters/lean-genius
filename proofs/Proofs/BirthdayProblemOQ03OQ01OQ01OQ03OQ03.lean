import Mathlib

/-
# Birthday Problem — OQ-03-OQ-01-OQ-01-OQ-03-OQ-03: The General k-Fold Coincidence Threshold

## Research Problem: birthday-problem-oq-03-oq-01-oq-01-oq-03-oq-03

The parent file (`birthday-problem-oq-03-oq-01-oq-01-oq-03`) proved the `k = 3` triple
coincidence threshold by a *cube-root sandwich* `(n-2)³ ≤ n(n-1)(n-2) ≤ n³`.  Its open
question OQ-03 asks:

> Generalize the `k = 3` coincidence threshold to general `k`: show the `k`-fold
> birthday-coincidence threshold is `n = (k! · d^{k-1} · ln 2)^{1/k} + O(1)` via the analogous
> falling-factorial sandwich `(n-k+1)^k ≤ n^{\underline{k}} ≤ n^k` combined with `rpow`
> monotonicity.

The heuristic is the standard Poisson/expected-count balance: the expected number of
unordered `k`-tuples sharing a day is

      C(n,k) / d^{k-1} = n^{\underline{k}} / (k! · d^{k-1}),

where `n^{\underline{k}} = n(n-1)⋯(n-k+1)` is the falling factorial.  The 50%-chance threshold
is where this expected count equals `ln 2`:

      n^{\underline{k}} / (k! · d^{k-1}) = ln 2,   i.e.   n^{\underline{k}} = k! · d^{k-1} · ln 2.

This file proves, **rigorously and with an explicit O(1) error bound**, that the `n` solving
this balance equation is exactly the claimed threshold to leading order:

      (k! · d^{k-1} · ln 2)^{1/k}  ≤  n  ≤  (k! · d^{k-1} · ln 2)^{1/k} + (k - 1).

So `n = (k! · d^{k-1} · ln 2)^{1/k} + O(1)`, the lower-order term bounded by the constant
`k - 1`, **independent of `d`**.  Specializing `k = 3` recovers the parent's
`(6 d² ln 2)^{1/3} + O(1)` with the same additive slack `2 = k - 1`.

The proof is the `k`-fold generalization of the parent's cube-root sandwich:

* `n^{\underline{k}} ≤ n^k` (each falling factor `n - i ≤ n`) gives the lower bound
  `(k! · d^{k-1} · ln 2)^{1/k} ≤ n`;
* `(n-k+1)^k ≤ n^{\underline{k}}` (each falling factor `n - i ≥ n - (k-1)`) gives the upper
  bound `n ≤ (k! · d^{k-1} · ln 2)^{1/k} + (k-1)`.

## What is proved

* `fallingR` — the real falling factorial `n^{\underline{k}} = ∏_{i<k} (n - i)`.
* `kthRoot_pow` — the `k`-th-root identity `(x^k)^{1/k} = x` for `x ≥ 0`, `k ≥ 1`.
* `falling_sandwich` — the two-sided bound `(n-(k-1))^k ≤ n^{\underline{k}} ≤ n^k`.
* `birthday_kfold_threshold` — the two-sided threshold bound above.
* `birthday_kfold_threshold_gap` — packaged as `|n − (k! d^{k-1} ln 2)^{1/k}| ≤ k - 1`.

Tags: probability, birthday-problem, asymptotics, threshold, falling-factorial, real-analysis
-/

namespace BirthdayProblemOQ03OQ01OQ01OQ03OQ03

open Real Finset

/-- **Real falling factorial.**  `n^{\underline{k}} = ∏_{i<k} (n - i) = n(n-1)⋯(n-k+1)`. -/
noncomputable def fallingR (n : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (n - (i : ℝ))

@[simp] lemma fallingR_zero (n : ℝ) : fallingR n 0 = 1 := by simp [fallingR]

/-- `n^{\underline{3}} = n(n-1)(n-2)`, matching the parent file's cube product. -/
lemma fallingR_three (n : ℝ) : fallingR n 3 = n * (n - 1) * (n - 2) := by
  simp [fallingR, Finset.prod_range_succ]

/-- **k-th-root identity.**  `(x^k)^{1/k} = x` for `x ≥ 0` and `k ≥ 1`. -/
theorem kthRoot_pow {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (x ^ k) ^ ((1 : ℝ) / k) = x := by
  rw [one_div]
  exact Real.pow_rpow_inv_natCast hx (by omega)

/-- **The falling-factorial sandwich.**  For `n ≥ k - 1` (so every falling factor
    `n - i` with `i < k` is nonnegative),

        (n - (k-1))^k  ≤  n^{\underline{k}}  ≤  n^k.

    The lower bound replaces each factor `n - i` by its smallest value `n - (k-1)`; the upper
    bound replaces each factor by its largest value `n`. -/
theorem falling_sandwich (n : ℝ) (k : ℕ) (hn : (k : ℝ) - 1 ≤ n) :
    (n - ((k : ℝ) - 1)) ^ k ≤ fallingR n k ∧ fallingR n k ≤ n ^ k := by
  -- For `i ∈ range k` we have `(i : ℝ) ≤ k - 1`, hence `0 ≤ n - (k-1) ≤ n - i ≤ n`.
  have hi_le : ∀ i ∈ Finset.range k, (i : ℝ) ≤ (k : ℝ) - 1 := by
    intro i hi
    have : i + 1 ≤ k := Finset.mem_range.mp hi
    have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast this
    linarith
  have hfac_nonneg : ∀ i ∈ Finset.range k, 0 ≤ n - (i : ℝ) := by
    intro i hi; have := hi_le i hi; linarith
  constructor
  · -- lower bound: (n-(k-1))^k = ∏ (n-(k-1)) ≤ ∏ (n-i)
    have hbase : (n - ((k : ℝ) - 1)) ^ k
        = ∏ _i ∈ Finset.range k, (n - ((k : ℝ) - 1)) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hbase]
    refine Finset.prod_le_prod (fun i _ => by linarith [hn]) ?_
    intro i hi; have := hi_le i hi; linarith
  · -- upper bound: ∏ (n-i) ≤ ∏ n = n^k
    have htop : n ^ k = ∏ _i ∈ Finset.range k, n := by
      rw [Finset.prod_const, Finset.card_range]
    rw [htop]
    refine Finset.prod_le_prod hfac_nonneg ?_
    intro i _; have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith

/-- **The general `k`-fold coincidence threshold, to leading order with explicit O(1) error.**

    Fix `k ≥ 1`, `d > 0`, and suppose `n ≥ k - 1` solves the expected-`k`-tuple balance
    equation

        n^{\underline{k}} = k! · d^{k-1} · ln 2

    (the expected number of coincident `k`-tuples equals `ln 2`, the 50%-chance criterion).
    Then, writing `L := k! · d^{k-1} · ln 2`,

        L^{1/k}  ≤  n  ≤  L^{1/k} + (k - 1).

    Hence `n = (k! · d^{k-1} · ln 2)^{1/k} + O(1)`: the threshold is `(k! d^{k-1} ln 2)^{1/k}`
    up to a bounded additive constant `k - 1`, independent of `d`.  This is the rigorous form
    of the asymptotic `n ≈ (k! d^{k-1} ln 2)^{1/k}`, and specializes at `k = 3` to the parent's
    `(6 d² ln 2)^{1/3} + O(1)`. -/
theorem birthday_kfold_threshold (k : ℕ) (d n : ℝ) (hk : 1 ≤ k) (hd : 0 < d)
    (hn : (k : ℝ) - 1 ≤ n)
    (hbal : fallingR n k = (k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) :
    ((k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) ^ ((1 : ℝ) / k) ≤ n ∧
    n ≤ ((k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) ^ ((1 : ℝ) / k) + ((k : ℝ) - 1) := by
  set L := (k.factorial : ℝ) * d ^ (k - 1) * Real.log 2 with hLdef
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := by rw [hLdef]; positivity
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hn0 : 0 ≤ n := le_trans hk1 hn
  have hnm : 0 ≤ n - ((k : ℝ) - 1) := by linarith
  have hexp : (0 : ℝ) ≤ (1 : ℝ) / k := by positivity
  obtain ⟨hlo, hhi⟩ := falling_sandwich n k hn
  rw [hbal] at hlo hhi
  refine ⟨?_, ?_⟩
  · -- Lower bound: L ≤ n^k, so L^{1/k} ≤ (n^k)^{1/k} = n.
    calc L ^ ((1 : ℝ) / k)
        ≤ (n ^ k) ^ ((1 : ℝ) / k) := Real.rpow_le_rpow hL hhi hexp
      _ = n := kthRoot_pow hn0 hk
  · -- Upper bound: (n-(k-1))^k ≤ L, so n-(k-1) = (((n-(k-1))^k)^{1/k} ≤ L^{1/k}.
    have hstep : n - ((k : ℝ) - 1) ≤ L ^ ((1 : ℝ) / k) := by
      calc n - ((k : ℝ) - 1)
          = ((n - ((k : ℝ) - 1)) ^ k) ^ ((1 : ℝ) / k) := (kthRoot_pow hnm hk).symm
        _ ≤ L ^ ((1 : ℝ) / k) := Real.rpow_le_rpow (pow_nonneg hnm k) hlo hexp
    linarith

/-- **Packaged threshold gap.**  The balance-equation solution `n` is within `k - 1` of the
    leading-order threshold `(k! d^{k-1} ln 2)^{1/k}` — a bounded, `d`-independent error. -/
theorem birthday_kfold_threshold_gap (k : ℕ) (d n : ℝ) (hk : 1 ≤ k) (hd : 0 < d)
    (hn : (k : ℝ) - 1 ≤ n)
    (hbal : fallingR n k = (k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) :
    |n - ((k.factorial : ℝ) * d ^ (k - 1) * Real.log 2) ^ ((1 : ℝ) / k)| ≤ (k : ℝ) - 1 := by
  obtain ⟨hlo, hhi⟩ := birthday_kfold_threshold k d n hk hd hn hbal
  rw [abs_le]
  constructor <;> linarith

/-- **Consistency with the parent.**  At `k = 3` the general threshold reduces exactly to the
    parent's cube-root statement `(6 d² ln 2)^{1/3} ≤ n ≤ (6 d² ln 2)^{1/3} + 2`. -/
theorem birthday_kfold_threshold_k3 (d n : ℝ) (hd : 0 < d) (hn : 2 ≤ n)
    (hbal : n * (n - 1) * (n - 2) = 6 * d ^ 2 * Real.log 2) :
    (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3) ≤ n ∧
    n ≤ (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3) + 2 := by
  have hbal' : fallingR n 3 = ((Nat.factorial 3 : ℝ)) * d ^ (3 - 1) * Real.log 2 := by
    rw [fallingR_three]; norm_num [Nat.factorial]; linarith [hbal]
  obtain ⟨hlo, hhi⟩ :=
    birthday_kfold_threshold 3 d n (by norm_num) hd (by norm_num; linarith) hbal'
  norm_num [Nat.factorial] at hlo hhi
  exact ⟨hlo, hhi⟩

#check @fallingR
#check @kthRoot_pow
#check @falling_sandwich
#check @birthday_kfold_threshold
#check @birthday_kfold_threshold_gap
#check @birthday_kfold_threshold_k3

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `fallingR` — real falling factorial `n^{\underline{k}} = ∏_{i<k}(n-i)`.
* `kthRoot_pow` — `(x^k)^{1/k} = x` for `x ≥ 0`, `k ≥ 1`.
* `falling_sandwich` — `(n-(k-1))^k ≤ n^{\underline{k}} ≤ n^k` for `n ≥ k-1`.
* `birthday_kfold_threshold` — for `k ≥ 1`, `d > 0`, `n ≥ k-1` solving
  `n^{\underline{k}} = k! d^{k-1} ln 2`,
  `(k! d^{k-1} ln 2)^{1/k} ≤ n ≤ (k! d^{k-1} ln 2)^{1/k} + (k-1)`.
* `birthday_kfold_threshold_gap` — equivalently `|n − (k! d^{k-1} ln 2)^{1/k}| ≤ k-1`.
* `birthday_kfold_threshold_k3` — the `k = 3` specialization recovers the parent verbatim.

This answers the parent's OQ-03: the general `k`-fold coincidence threshold is
`(k! d^{k-1} ln 2)^{1/k}` to leading order, with a bounded additive error of at most `k - 1`
(independent of `d`), proved by the falling-factorial sandwich
`(n-k+1)^k ≤ n^{\underline{k}} ≤ n^k` and `rpow` monotonicity — the exact `k`-fold lift of the
parent's cube-root sandwich, with the `k = 3` slack `2 = k - 1` recovered as a special case.
-/

end BirthdayProblemOQ03OQ01OQ01OQ03OQ03

#print axioms BirthdayProblemOQ03OQ01OQ01OQ03OQ03.birthday_kfold_threshold
#print axioms BirthdayProblemOQ03OQ01OQ01OQ03OQ03.birthday_kfold_threshold_gap
