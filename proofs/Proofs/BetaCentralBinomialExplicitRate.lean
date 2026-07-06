import Mathlib

/-
# An Explicit `1 + O(1/n)` Rate for the Diagonal Beta Value

## What This Proves

The parent entry (`beta-integral-recurrence-oq-01-oq-01-oq-01`) establishes the bare
asymptotic equivalence

  `B(n+1, n+1) ~ √(πn) / ((2n+1)·4ⁿ)`   (`Asymptotics.IsEquivalent`),

i.e. the ratio of the two sides tends to `1`, *with no control on the rate*.  This
entry upgrades that to an **explicit two-sided rate with effective constants**.

Write `T n := √(πn) / ((2n+1)·4ⁿ)` for the leading term and
`q n := B(n+1,n+1) / T n` for the multiplicative correction factor.  We prove:

* **`betaDiag_eq_target_mul`** (exact) : `B(n+1,n+1) = T n · q n`, where
  `q n = stirlingSeq(n)² / (√π · stirlingSeq(2n))`.

* **`betaDiag_correction_bracket`** (main, effective) : for `n ≥ 2`,
    `exp(-1/(4(2n-1))) ≤ q n ≤ exp(1/(2(n-1)))`.
  Both bounding exponents are `O(1/n)`, so this is precisely the statement
  `q n = 1 + O(1/n)` made effective: the correction is squeezed between two
  explicit exponentials that both collapse to `1`.

* **`betaDiag_correction_isBigO`** (clean Landau form) :
    `(fun n => q n - 1) =O[atTop] (fun n => 1/n)`,
  the honest `1 + O(1/n)` statement, derived from the effective bracket.

## The Engine

The correction factor is governed entirely by Mathlib's Stirling sequence
`stirlingSeq k = k! / (√(2k)·(k/e)^k) → √π`.  The exact identity

  `C(2n,n) = stirlingSeq(2n)/stirlingSeq(n)² · 4ⁿ/√n`

collapses `q n` to `√π·stirlingSeq(2n)/stirlingSeq(n)²`⁻¹, and the quantitative
convergence of `stirlingSeq` — packaged here as
`log stirlingSeq(m+1) - log√π ≤ 1/(4m)` (a telescoping consequence of Mathlib's
`Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ`) — supplies the `O(1/n)` rate.

## Relation to Mathlib

Mathlib has `Stirling.factorial_isEquivalent_stirling`, the per-step bound
`Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ`, and the effective lower bound
`Stirling.sqrt_pi_le_stirlingSeq`, but it packages **no tail bound**
`log stirlingSeq(m+1) - log√π ≤ 1/(4m)` and no rate for the central binomial
coefficient or the Beta value.  All of that is assembled here.
-/

open Filter Asymptotics
open scoped Topology Real Nat

namespace BetaDiagExplicitRate

/-! ### Part 0 — The diagonal Beta value (self-contained restatement)

To keep this file independent of the parent's build, we restate the two facts we
use from the parent chain: the diagonal Beta value as a central-binomial reciprocal
(`betaDiag`) and its factorial form (`centralBinom_cast`).  Both are proved from
Mathlib directly. -/

/-- The real diagonal Beta value, `B(n+1,n+1) = 1 / ((2n+1)·C(2n,n))`. -/
noncomputable def betaDiag (n : ℕ) : ℝ :=
  1 / ((2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ))

/-- `C(2n,n) = (2n)! / (n!·n!)` over `ℝ`. -/
lemma centralBinom_cast (n : ℕ) :
    (Nat.centralBinom n : ℝ)
      = (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
  have hfac : Nat.centralBinom n * (Nat.factorial n * Nat.factorial n)
      = Nat.factorial (2 * n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← mul_assoc]
    exact h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast hfac

/-! ### Part 1 — A quantitative tail bound for the Stirling sequence -/

/-- **Per-step telescoping bound.**  For `m ≥ 1`, each successive gap of
`log ∘ stirlingSeq` is dominated by a telescoping difference of `1/(4·)`:

`log stirlingSeq(m+j+1) - log stirlingSeq(m+j+2) ≤ 1/(4(m+j)) - 1/(4(m+j+1))`. -/
lemma log_gap_le_telescope (m j : ℕ) (hm : 1 ≤ m) :
    Real.log (Stirling.stirlingSeq (m + j + 1)) - Real.log (Stirling.stirlingSeq (m + j + 2))
      ≤ 1 / (4 * ((m : ℝ) + j)) - 1 / (4 * ((m : ℝ) + j + 1)) := by
  have hstep := Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ (m + j)
  -- `hstep : log stirlingSeq((m+j)+1) - log stirlingSeq((m+j)+2) ≤ 1/(4·((m+j)+1)²)`
  refine hstep.trans ?_
  have hmj : (0 : ℝ) < (m : ℝ) + j := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    positivity
  have hmj1 : (0 : ℝ) < (m : ℝ) + j + 1 := by positivity
  push_cast
  have e1 : 1 / (4 * ((m : ℝ) + (j : ℝ))) - 1 / (4 * ((m : ℝ) + (j : ℝ) + 1))
      = 1 / (4 * ((m : ℝ) + (j : ℝ)) * ((m : ℝ) + (j : ℝ) + 1)) := by
    field_simp; ring
  rw [e1]
  apply one_div_le_one_div_of_le (mul_pos (mul_pos (by norm_num) hmj) hmj1)
  nlinarith [hmj, hmj1]

/-- **Quantitative Stirling tail bound (new).**  For `m ≥ 1`,
`log stirlingSeq(m+1) - log √π ≤ 1/(4m)`.

Proof: telescope `log stirlingSeq(m+1) - log stirlingSeq(m+1+N)` using
`log_gap_le_telescope`, obtaining a partial-sum bound `≤ 1/(4m)` uniform in `N`,
then send `N → ∞` using `stirlingSeq → √π`. -/
lemma log_stirlingSeq_sub_sqrt_pi_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π) ≤ 1 / (4 * (m : ℝ)) := by
  set g : ℕ → ℝ := fun j => Real.log (Stirling.stirlingSeq (m + j + 1)) with hg
  -- partial telescoping sum
  have hsum : ∀ N : ℕ, (∑ j ∈ Finset.range N, (g j - g (j + 1)))
      = Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + N + 1)) := by
    intro N
    rw [Finset.sum_range_sub' g N]
  -- explicit telescoping value of the dominating sum
  have tel : ∀ N : ℕ, (∑ j ∈ Finset.range N,
      (1 / (4 * ((m : ℝ) + (j : ℝ))) - 1 / (4 * ((m : ℝ) + (j : ℝ) + 1))))
      = 1 / (4 * (m : ℝ)) - 1 / (4 * ((m : ℝ) + (N : ℝ))) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  -- uniform bound on the partial sums
  have hbound : ∀ N : ℕ, (∑ j ∈ Finset.range N, (g j - g (j + 1))) ≤ 1 / (4 * (m : ℝ)) := by
    intro N
    have hle : (∑ j ∈ Finset.range N, (g j - g (j + 1)))
        ≤ ∑ j ∈ Finset.range N,
            (1 / (4 * ((m : ℝ) + (j : ℝ))) - 1 / (4 * ((m : ℝ) + (j : ℝ) + 1))) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [hg] using log_gap_le_telescope m j hm
    rw [tel N] at hle
    have h0 : (0 : ℝ) ≤ 1 / (4 * ((m : ℝ) + (N : ℝ))) := by positivity
    linarith
  -- limit of the partial sums
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have htend_arg : Tendsto (fun N : ℕ => m + N + 1) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have htend_s : Tendsto (fun N : ℕ => Stirling.stirlingSeq (m + N + 1)) atTop (𝓝 (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp htend_arg
  have htend_log : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq (m + N + 1))) atTop
      (𝓝 (Real.log (Real.sqrt π))) :=
    (Real.continuousAt_log hπ.ne').tendsto.comp htend_s
  have htend : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (g j - g (j + 1))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π))) := by
    have := (tendsto_const_nhds (x := Real.log (Stirling.stirlingSeq (m + 1)))).sub htend_log
    refine this.congr ?_
    intro N; rw [hsum N]
  exact le_of_tendsto' htend hbound

/-- The Stirling sequence deviation `log stirlingSeq k - log √π` is nonnegative for `k ≥ 1`
(since `√π ≤ stirlingSeq k`). -/
lemma zero_le_log_stirlingSeq_sub_sqrt_pi {k : ℕ} (hk : k ≠ 0) :
    0 ≤ Real.log (Stirling.stirlingSeq k) - Real.log (Real.sqrt π) := by
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have := Stirling.sqrt_pi_le_stirlingSeq hk
  have := Real.log_le_log hπ this
  linarith

/-! ### Part 2 — The exact central-binomial / Stirling identity -/

/-- **Exact central-binomial identity (new).**  For `n ≥ 1`,
`C(2n,n) = stirlingSeq(2n) / stirlingSeq(n)² · (4ⁿ / √n)`.

Pure algebra from the definition `stirlingSeq k = k!/(√(2k)·(k/e)^k)` and the
factorial form `C(2n,n) = (2n)!/(n!·n!)`. -/
lemma centralBinom_stirling (n : ℕ) (hn : 1 ≤ n) :
    (Nat.centralBinom n : ℝ)
      = Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n) ^ 2 * (4 ^ n / Real.sqrt n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have hfac2 : ((n / Real.exp 1 : ℝ)) ^ n ≠ 0 := by positivity
  have hnfac : ((Nat.factorial n : ℝ)) ≠ 0 := by positivity
  -- √(2·(2n)) = 2·√n
  have h4n : Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    rw [show (2 * ((2 * n : ℕ) : ℝ)) = (2 : ℝ) ^ 2 * (n : ℝ) by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  -- (√(2n))² = 2n
  have h2n : Real.sqrt (2 * (n : ℝ)) ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  -- ((2n)/e)^(2n) = 4ⁿ · ((n/e)^n)²
  have hpow : (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n) = 4 ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := by
    have h2 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    rw [show ((2 * n : ℕ) : ℝ) / Real.exp 1 = 2 * ((n : ℝ) / Real.exp 1) by push_cast; ring,
      mul_pow, h2, ← pow_mul, Nat.mul_comm n 2, pow_mul]
  have hune : Real.sqrt (2 * (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [centralBinom_cast, Stirling.stirlingSeq, Stirling.stirlingSeq, h4n, hpow]
  set A := ((n : ℝ) / Real.exp 1) ^ n with hAdef
  set s := Real.sqrt (n : ℝ) with hsdef
  set u := Real.sqrt (2 * (n : ℝ)) with hudef
  have hApos : (0 : ℝ) < A := by rw [hAdef]; positivity
  have hAne : A ≠ 0 := hApos.ne'
  have hsu : u ^ 2 = 2 * s ^ 2 := by
    rw [hsdef, hudef, Real.sq_sqrt (by positivity), Real.sq_sqrt hn0.le]
  field_simp
  rw [hsu]

/-! ### Part 3 — The correction factor and its bracket -/

/-- The leading term `T n = √(πn)/((2n+1)·4ⁿ)`. -/
noncomputable def target (n : ℕ) : ℝ := Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n)

/-- The multiplicative correction `q n = stirlingSeq(n)² / (√π · stirlingSeq(2n))`. -/
noncomputable def correction (n : ℕ) : ℝ :=
  (Stirling.stirlingSeq n) ^ 2 / (Real.sqrt π * Stirling.stirlingSeq (2 * n))

lemma target_pos {n : ℕ} (hn : 1 ≤ n) : 0 < target n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold target
  have : 0 < Real.sqrt (π * n) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma correction_pos {n : ℕ} (hn : 1 ≤ n) : 0 < correction n := by
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hs1 : 0 < Stirling.stirlingSeq n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  have hs2 : 0 < Stirling.stirlingSeq (2 * n) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [hm]; exact Stirling.stirlingSeq'_pos m
  unfold correction
  positivity

/-- **Exact factorisation (new).**  `B(n+1,n+1) = T n · q n` for `n ≥ 1`. -/
theorem betaDiag_eq_target_mul (n : ℕ) (hn : 1 ≤ n) :
    betaDiag n = target n * correction n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hs1 : 0 < Stirling.stirlingSeq n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  have hs2 : 0 < Stirling.stirlingSeq (2 * n) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [hm]; exact Stirling.stirlingSeq'_pos m
  have hC : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
    have := Nat.centralBinom_pos n; exact_mod_cast this
  -- √(πn) = √π · √n
  have hsplit : Real.sqrt (π * (n : ℝ)) = Real.sqrt π * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul Real.pi_pos.le _
  have hCid := centralBinom_stirling n hn
  unfold betaDiag target correction
  rw [hsplit]
  rw [show (1 : ℝ) / ((2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ))
      = 1 / ((2 * (n : ℝ) + 1)) * (1 / (Nat.centralBinom n : ℝ)) by rw [one_div_mul_one_div]]
  rw [hCid]
  field_simp

/-- `log (correction n) = 2·(log stirlingSeq n − log√π) − (log stirlingSeq(2n) − log√π)`. -/
lemma log_correction_eq (n : ℕ) (hn : 1 ≤ n) :
    Real.log (correction n)
      = 2 * (Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt π))
        - (Real.log (Stirling.stirlingSeq (2 * n)) - Real.log (Real.sqrt π)) := by
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hs1 : 0 < Stirling.stirlingSeq n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  have hs2 : 0 < Stirling.stirlingSeq (2 * n) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [hm]; exact Stirling.stirlingSeq'_pos m
  unfold correction
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hπ.ne' hs2.ne',
    Real.log_pow]
  push_cast
  ring

/-- **Upper bound on the log-correction.**  For `n ≥ 2`,
`log (correction n) ≤ 1/(2(n-1))`. -/
lemma log_correction_upper (n : ℕ) (hn : 2 ≤ n) :
    Real.log (correction n) ≤ 1 / (2 * ((n : ℝ) - 1)) := by
  have hLn : Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt π) ≤ 1 / (4 * ((n : ℝ) - 1)) := by
    obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
    have ha : 1 ≤ a := by omega
    have := log_stirlingSeq_sub_sqrt_pi_le a ha
    have hcast : ((a + 1 : ℕ) : ℝ) - 1 = (a : ℝ) := by push_cast; ring
    rw [hcast]; exact this
  have hL2n : 0 ≤ Real.log (Stirling.stirlingSeq (2 * n)) - Real.log (Real.sqrt π) :=
    zero_le_log_stirlingSeq_sub_sqrt_pi (by omega)
  rw [log_correction_eq n (by omega)]
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have : 2 * (1 / (4 * ((n : ℝ) - 1))) = 1 / (2 * ((n : ℝ) - 1)) := by
    rw [mul_one_div]; rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  linarith

/-- **Lower bound on the log-correction.**  For `n ≥ 1`,
`-1/(4(2n-1)) ≤ log (correction n)`. -/
lemma log_correction_lower (n : ℕ) (hn : 1 ≤ n) :
    -(1 / (4 * (2 * (n : ℝ) - 1))) ≤ Real.log (correction n) := by
  have hLn : 0 ≤ Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt π) :=
    zero_le_log_stirlingSeq_sub_sqrt_pi (by omega)
  have hL2n : Real.log (Stirling.stirlingSeq (2 * n)) - Real.log (Real.sqrt π)
      ≤ 1 / (4 * (2 * (n : ℝ) - 1)) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    have hmge : 1 ≤ m := by omega
    have hbd := log_stirlingSeq_sub_sqrt_pi_le m hmge
    have hcast : (m : ℝ) = 2 * (n : ℝ) - 1 := by
      have : ((2 * n : ℕ) : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hm
      push_cast at this; linarith
    rw [hm]; rw [hcast] at hbd; exact hbd
  rw [log_correction_eq n hn]
  linarith

/-! ### Part 4 — The explicit two-sided rate and the `O(1/n)` corollary -/

/-- **Main result — effective two-sided rate.**  For `n ≥ 2`, the correction factor
`q n = B(n+1,n+1)/T n` is bracketed by two explicit exponentials whose exponents are
`O(1/n)`:

`exp(-1/(4(2n-1))) ≤ q n ≤ exp(1/(2(n-1)))`.

This is the effective form of `q n = 1 + O(1/n)`. -/
theorem betaDiag_correction_bracket (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (-(1 / (4 * (2 * (n : ℝ) - 1)))) ≤ correction n ∧
      correction n ≤ Real.exp (1 / (2 * ((n : ℝ) - 1))) := by
  have hcp : 0 < correction n := correction_pos (by omega)
  constructor
  · exact (Real.le_log_iff_exp_le hcp).mp (log_correction_lower n (by omega))
  · exact (Real.log_le_iff_le_exp hcp).mp (log_correction_upper n hn)

/-- **Clean Landau form.**  `q n - 1 = O(1/n)`.  The honest `1 + O(1/n)` statement. -/
theorem betaDiag_correction_isBigO :
    (fun n : ℕ => correction n - 1) =O[atTop] (fun n : ℕ => 1 / (n : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hd1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hd2 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := betaDiag_correction_bracket n hn
  set a : ℝ := 1 / (4 * (2 * (n : ℝ) - 1)) with ha
  set b : ℝ := 1 / (2 * ((n : ℝ) - 1)) with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have hble : b ≤ 1 := by rw [hb, div_le_one (by positivity)]; linarith
  -- exp b ≤ 3
  have hexpb_le : Real.exp b ≤ 3 := by
    have h9 := Real.exp_one_lt_d9
    calc Real.exp b ≤ Real.exp 1 := Real.exp_le_exp.mpr hble
      _ ≤ 3 := by linarith
  -- exp b - 1 ≤ b * exp b  (from 1 - b ≤ exp(-b))
  have hstep : Real.exp b - 1 ≤ b * Real.exp b := by
    have h1 : (1 : ℝ) - b ≤ (Real.exp b)⁻¹ := by
      have h := Real.add_one_le_exp (-b); rw [Real.exp_neg] at h; linarith
    have h3 : (0 : ℝ) < Real.exp b := Real.exp_pos b
    have h4 : (1 - b) * Real.exp b ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h1 h3.le
      rwa [inv_mul_cancel₀ h3.ne'] at this
    nlinarith [h4]
  -- 3·b ≤ 3/n  and  a ≤ 3/n
  have hbn : (3 : ℝ) * b ≤ 3 / (n : ℝ) := by
    rw [hb, mul_one_div, le_div_iff₀ hnpos, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hn2]
  have han : a ≤ 3 / (n : ℝ) := by
    rw [ha, le_div_iff₀ hnpos, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hn2]
  -- upper direction: correction n - 1 ≤ 3/n
  have hupper : correction n - 1 ≤ 3 / (n : ℝ) := by
    have hb3 : b * Real.exp b ≤ b * 3 := mul_le_mul_of_nonneg_left hexpb_le hbpos.le
    have hcm : correction n - 1 ≤ Real.exp b - 1 := by linarith [hhi]
    nlinarith [hcm, hstep, hb3, hbn]
  -- lower direction: 1 - correction n ≤ 3/n
  have hlower : 1 - correction n ≤ 3 / (n : ℝ) := by
    have h1 : (1 : ℝ) - a ≤ Real.exp (-a) := by
      have h := Real.add_one_le_exp (-a); linarith
    linarith [hlo, h1, han]
  -- combine into the norm bound
  have h3n : (3 : ℝ) * (1 / (n : ℝ)) = 3 / (n : ℝ) := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/(n:ℝ)), abs_le]
  exact ⟨by linarith [hlower, h3n], by linarith [hupper, h3n]⟩

/-- **Capstone.**  The diagonal Beta value obeys the explicit `1 + O(1/n)` rate
relative to its leading term:  `B(n+1,n+1)/T n - 1 = O(1/n)`. -/
theorem betaDiag_rate :
    (fun n : ℕ => betaDiag n / target n - 1) =O[atTop] (fun n : ℕ => 1 / (n : ℝ)) := by
  refine betaDiag_correction_isBigO.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have htp : 0 < target n := target_pos hn
  rw [betaDiag_eq_target_mul n hn, mul_comm (target n) (correction n),
    mul_div_assoc, div_self htp.ne', mul_one]

end BetaDiagExplicitRate
