/-
  First Moment Method — OQ-04: non-strict averaging (some outcome meets the mean)

  The gallery entry `ProbMethodExpectation` proves the *strict* first moment
  principle: `E[X] > t ⟹ ∃ ω, X(ω) > t` (`first_moment_principle`) and its dual.
  The strict form cannot conclude anything at the threshold `E[X] = t`, yet the
  most common use of the probabilistic method is exactly the non-strict statement
  *"some outcome is at least the average"* — used to extract a witness meeting the
  expectation.  This file supplies the non-strict averaging lemmas.

  * `exists_ge_of_card_mul_le` / `exists_le_of_card_mul_ge` — the division-free
    practical forms: `t·|s| ≤ ∑ f ⟹ ∃ a, t ≤ f a` (and dual).  This is the shape
    actually used in lower-bound arguments (avoids dividing by `|s|`).
  * `exists_ge_average` / `exists_le_average` — *some element is at least / at most
    the mean*: `∃ a ∈ s, (∑ f)/|s| ≤ f a` and the dual.  The pigeonhole core of the
    first moment method.
  * `first_moment_ge` / `first_moment_le` — the non-strict threshold forms,
    `E[X] ≥ t ⟹ ∃ a, f a ≥ t`, completing the strict `first_moment_principle` at
    the boundary.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Spencer, *The Probabilistic Method*, Ch. 2 (first moment).
-/

import Mathlib

namespace ProbMethod.ExpectationOQ04

open Finset BigOperators

variable {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℚ} {t : ℚ}

/-- **Division-free first moment (≥).**  If `t·|s| ≤ ∑ f` over a nonempty set, then
    some element is at least `t`.  This is the practical lower-bound shape of the
    first moment method (no division by `|s|`). -/
theorem exists_ge_of_card_mul_le (hs : s.Nonempty) (h : t * s.card ≤ s.sum f) :
    ∃ a ∈ s, t ≤ f a := by
  by_contra hc
  push_neg at hc
  have hlt : s.sum f < s.sum (fun _ => t) := Finset.sum_lt_sum_of_nonempty hs hc
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at hlt
  linarith

/-- **Division-free first moment (≤).**  If `∑ f ≤ t·|s|`, some element is at most
    `t`. -/
theorem exists_le_of_card_mul_ge (hs : s.Nonempty) (h : s.sum f ≤ t * s.card) :
    ∃ a ∈ s, f a ≤ t := by
  by_contra hc
  push_neg at hc
  have hlt : s.sum (fun _ => t) < s.sum f := Finset.sum_lt_sum_of_nonempty hs hc
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at hlt
  linarith

/-- **Some element is at least the mean.**  `∃ a ∈ s, (∑ f)/|s| ≤ f a`. -/
theorem exists_ge_average (hs : s.Nonempty) :
    ∃ a ∈ s, (s.sum f) / s.card ≤ f a := by
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs.card_pos)
  refine exists_ge_of_card_mul_le hs (le_of_eq ?_)
  field_simp

/-- **Some element is at most the mean.**  `∃ a ∈ s, f a ≤ (∑ f)/|s|`. -/
theorem exists_le_average (hs : s.Nonempty) :
    ∃ a ∈ s, f a ≤ (s.sum f) / s.card := by
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs.card_pos)
  refine exists_le_of_card_mul_ge hs (le_of_eq ?_)
  field_simp

/-- **Non-strict first moment principle (≥).**  If the average is at least `t`,
    some element is at least `t` — the boundary case the strict
    `first_moment_principle` cannot reach. -/
theorem first_moment_ge (hs : s.Nonempty) (havg : t ≤ (s.sum f) / s.card) :
    ∃ a ∈ s, t ≤ f a := by
  obtain ⟨a, ha, hfa⟩ := exists_ge_average hs
  exact ⟨a, ha, le_trans havg hfa⟩

/-- **Non-strict first moment principle (≤).**  Dual of `first_moment_ge`. -/
theorem first_moment_le (hs : s.Nonempty) (havg : (s.sum f) / s.card ≤ t) :
    ∃ a ∈ s, f a ≤ t := by
  obtain ⟨a, ha, hfa⟩ := exists_le_average hs
  exact ⟨a, ha, le_trans hfa havg⟩

/-- **Two-sided first moment.**  The mean is *straddled* by the sample: some
    element lies at or below it and some element at or above it, simultaneously.
    Immediate from `exists_le_average` and `exists_ge_average` together — the base
    of any argument that needs both tails of the mean at once (spread bounds,
    second-moment / variance arguments). -/
theorem exists_le_and_ge_average (hs : s.Nonempty) :
    ∃ a ∈ s, ∃ b ∈ s,
      f a ≤ (s.sum f) / s.card ∧ (s.sum f) / s.card ≤ f b := by
  obtain ⟨a, ha, hfa⟩ := exists_le_average hs
  obtain ⟨b, hb, hfb⟩ := exists_ge_average hs
  exact ⟨a, ha, b, hb, hfa, hfb⟩

/-- **Nonnegative spread around the mean.**  There are sample points `a, b ∈ s`
    with `f a ≤ (∑ f)/|s| ≤ f b`, hence `0 ≤ f b − f a`: the max-minus-min spread
    of any sample is nonnegative and dominates the deviation of both extremes from
    the mean.  The two-sided companion of the one-sided `first_moment_ge` /
    `first_moment_le`. -/
theorem exists_nonneg_spread_of_average (hs : s.Nonempty) :
    ∃ a ∈ s, ∃ b ∈ s, 0 ≤ f b - f a := by
  obtain ⟨a, ha, b, hb, hfa, hfb⟩ := exists_le_and_ge_average hs
  exact ⟨a, ha, b, hb, by linarith⟩

/-! ## Application: strengthening `expected_mono_cliques` toward Erdős 1947

The parent gallery lemma `expected_mono_cliques` only records that the expected
number of monochromatic `k`-cliques in a uniformly random 2-colouring of the edges
of `Kₙ`, namely `E(n,k) = C(n,k)·2^{1−C(k,2)}`, is `≥ 0`.  The open question OQ-04
asks to strengthen this to `E(n,k) < 1` — which, by the (strict) first moment
principle, exhibits a 2-colouring with **no** monochromatic `k`-clique, i.e. the
Erdős 1947 lower bound `R(k,k) > n`.

This section makes two verified reductions toward that goal: it removes the integer
`zpow` by reducing `E < 1` to a clean `ℕ`-power inequality, and it records the
first-moment upper bound `E ≤ (nᵏ/k!)·2^{1−C(k,2)}` (via `Nat.choose_le_pow_div`),
the quantity Erdős's counting argument actually bounds below `1`. -/

/-- The expected number of monochromatic `k`-cliques in a uniformly random
2-colouring of `Kₙ`'s edges: `C(n,k) · 2^{1 − C(k,2)}` (matching the parent
`expected_mono_cliques`). -/
noncomputable def expectedMonoCliques (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * (2 : ℚ) ^ (1 - (k.choose 2 : ℤ))

/-- **Reduction of the Erdős strict bound to a pure power inequality.**  The
expected count is `< 1` *exactly* when `C(n,k)·2 < 2^{C(k,2)}` — a statement
entirely in `ℕ`-powers, with the integer `zpow` eliminated.  This is the clean
target a later session (or `Aristotle`) must discharge to answer OQ-04. -/
theorem expectedMonoCliques_lt_one_iff (n k : ℕ) :
    expectedMonoCliques n k < 1 ↔ (n.choose k : ℚ) * 2 < 2 ^ (k.choose 2) := by
  unfold expectedMonoCliques
  have hpow_pos : (0 : ℚ) < (2 : ℚ) ^ (k.choose 2) := by positivity
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one, zpow_neg,
    zpow_natCast,
    show (n.choose k : ℚ) * (2 * ((2 : ℚ) ^ (k.choose 2))⁻¹)
        = ((n.choose k : ℚ) * 2) / (2 : ℚ) ^ (k.choose 2) from by rw [div_eq_mul_inv]; ring,
    div_lt_one hpow_pos]

/-- **First-moment upper bound on the expected count.**  Since `C(n,k) ≤ nᵏ/k!`
(`Nat.choose_le_pow_div`), the expected number of monochromatic `k`-cliques is at
most `(nᵏ/k!) · 2^{1 − C(k,2)}`.  Isolating this quantity reduces OQ-04 to the
elementary estimate `nᵏ · 2 < k! · 2^{C(k,2)}`. -/
theorem expectedMonoCliques_le (n k : ℕ) :
    expectedMonoCliques n k
      ≤ ((n : ℚ) ^ k / (k.factorial : ℚ)) * (2 : ℚ) ^ (1 - (k.choose 2 : ℤ)) := by
  unfold expectedMonoCliques
  apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)
  have h := Nat.choose_le_pow_div k n (α := ℚ)
  simpa using h

/-! ## The ℕ-power inequality behind Erdős 1947 (OQ-04 core)

OQ-04 asks to strengthen `expected_mono_cliques` to `E(n,k) < 1` for `n < 2^(k/2)`.
Via `expectedMonoCliques_lt_one_iff` this reduces to the pure `ℕ`-power inequality
`2·C(n,k) < 2^{C(k,2)}`, and the half-integer hypothesis `n < 2^(k/2)` is equivalent
(square both sides) to the clean `ℕ` statement `n² < 2^k`.  This section discharges
that inequality outright (`erdos_1947_clique_bound`), so OQ-04's target
`expectedMonoCliques n k < 1` now holds unconditionally on `n² < 2^k`, `k ≥ 3`
(`expectedMonoCliques_lt_one_of_sq_lt`).  Mathematically this is the Erdős 1947
diagonal Ramsey lower bound `R(k,k) > n` for every `n` with `n² < 2^k`.

The proof compares squares to stay entirely in `ℕ`: from `C(n,k)·k! ≤ nᵏ`
(`Nat.descFactorial_le_pow`) and `n² < 2^k` one gets
`(2·C(n,k))²·(k!)² ≤ 4·n^{2k} < 4·2^{k²} = 2^{k²+2}`, while
`(2^{C(k,2)})²·(k!)² ≥ 2^{2·C(k,2)}·2^{k+2} = 2^{k²+2}` using the factorial growth
lemma `2^{k+2} ≤ (k!)²` and the identity `2·C(k,2)+k = k²`. -/

/-- `2·C(k,2) + k = k²`, i.e. `2·C(k,2) = k(k−1)`.  Holds for every `k`. -/
private lemma two_mul_choose_two_add (k : ℕ) : 2 * k.choose 2 + k = k * k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    have h : (j + 1).choose 2 = j.choose 2 + j := by
      rw [Nat.choose_succ_succ']
      simp [Nat.choose_one_right, Nat.add_comm]
    rw [h]; nlinarith [ih]

/-- Factorial growth: `2^{k+2} ≤ (k!)²` for `k ≥ 3` (base `2⁵ = 32 ≤ 36 = (3!)²`). -/
private lemma two_pow_add_two_le_factorial_sq {k : ℕ} (hk : 3 ≤ k) :
    2 ^ (k + 2) ≤ (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc 2 ^ (k + 1 + 2)
        = 2 ^ (k + 2) * 2 := by rw [show k + 1 + 2 = (k + 2) + 1 from by ring, pow_succ]
      _ ≤ (k.factorial) ^ 2 * 2 := by gcongr
      _ ≤ (k.factorial) ^ 2 * (k + 1) ^ 2 := by gcongr; nlinarith [hk]
      _ = ((k + 1).factorial) ^ 2 := by rw [Nat.factorial_succ]; ring

/-- **Erdős 1947 clique bound (pure `ℕ` form).**  If `n² < 2^k` and `k ≥ 3`, then
`2·C(n,k) < 2^{C(k,2)}`.  Combined with `expectedMonoCliques_lt_one_iff` this gives
`E(n,k) < 1`, hence (strict first moment) a 2-colouring of `Kₙ` with no
monochromatic `k`-clique — the diagonal Ramsey lower bound `R(k,k) > n`. -/
theorem erdos_1947_clique_bound {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 < 2 ^ k) :
    2 * n.choose k < 2 ^ (k.choose 2) := by
  have hk0 : k ≠ 0 := by omega
  -- `C(n,k)·k! ≤ nᵏ` via `descFactorial`.
  have hCk : n.choose k * k.factorial ≤ n ^ k := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n k
    have hle := Nat.descFactorial_le_pow n k
    rw [h] at hle
    calc n.choose k * k.factorial = k.factorial * n.choose k := by ring
      _ ≤ n ^ k := hle
  have hkey := two_mul_choose_two_add k
  have hgrow := two_pow_add_two_le_factorial_sq hk
  have hpow : (n ^ 2) ^ k < (2 ^ k) ^ k := Nat.pow_lt_pow_left hn hk0
  -- Compare squares, multiplied through by `(k!)²`.
  have hmul : (2 * n.choose k) ^ 2 * (k.factorial) ^ 2
                < (2 ^ (k.choose 2)) ^ 2 * (k.factorial) ^ 2 := by
    calc (2 * n.choose k) ^ 2 * (k.factorial) ^ 2
        = 4 * (n.choose k * k.factorial) ^ 2 := by ring
      _ ≤ 4 * (n ^ k) ^ 2 := by gcongr
      _ = 4 * (n ^ 2) ^ k := by
            have hnn : (n ^ k) ^ 2 = (n ^ 2) ^ k := by
              rw [← pow_mul, ← pow_mul, Nat.mul_comm]
            rw [hnn]
      _ < 4 * (2 ^ k) ^ k := by gcongr
      _ = 2 ^ (k * k + 2) := by
            rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, Nat.add_comm]
      _ = 2 ^ (2 * k.choose 2 + k + 2) := by rw [← hkey]
      _ = (2 ^ (k.choose 2)) ^ 2 * 2 ^ (k + 2) := by
            rw [← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ (2 ^ (k.choose 2)) ^ 2 * (k.factorial) ^ 2 := by gcongr
  have hsq : (2 * n.choose k) ^ 2 < (2 ^ (k.choose 2)) ^ 2 :=
    lt_of_mul_lt_mul_right hmul (Nat.zero_le _)
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hsq

/-- **OQ-04 resolved.**  The expected number of monochromatic `k`-cliques is `< 1`
whenever `n² < 2^k` (equivalently `n < 2^{k/2}`) and `k ≥ 3` — the strengthening of
`expected_mono_cliques` the gallery entry asked for.  By the strict first moment
principle this exhibits a 2-colouring of `Kₙ` with no monochromatic `k`-clique. -/
theorem expectedMonoCliques_lt_one_of_sq_lt {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 < 2 ^ k) :
    expectedMonoCliques n k < 1 := by
  rw [expectedMonoCliques_lt_one_iff]
  have h := erdos_1947_clique_bound hk hn
  have hcast : ((2 * n.choose k : ℕ) : ℚ) < ((2 ^ k.choose 2 : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at hcast
  linarith

/-- **Erdős 1947, explicit witness form.**  The conditional bound
`expectedMonoCliques_lt_one_of_sq_lt` requires an `n` with `n² < 2^k`; here we exhibit one
that grows like `2^{k/2}`.  For every `k ≥ 3`, the explicit choice
`n = 2^{⌊(k−1)/2⌋}` satisfies `expectedMonoCliques n k < 1`.  This is the textbook
*unconditional* diagonal Ramsey lower bound `R(k,k) > 2^{⌊(k−1)/2⌋}` (Erdős 1947): a
random 2-colouring of `K_{2^{⌊(k−1)/2⌋}}` almost surely has no monochromatic `k`-clique.

The witness works because `2·⌊(k−1)/2⌋ ≤ k−1 < k`, so
`n² = (2^{⌊(k−1)/2⌋})² = 2^{2·⌊(k−1)/2⌋} < 2^k`. -/
theorem expectedMonoCliques_lt_one_pow {k : ℕ} (hk : 3 ≤ k) :
    expectedMonoCliques (2 ^ ((k - 1) / 2)) k < 1 := by
  apply expectedMonoCliques_lt_one_of_sq_lt hk
  have hm : 2 * ((k - 1) / 2) < k := by omega
  calc (2 ^ ((k - 1) / 2)) ^ 2
      = 2 ^ (2 * ((k - 1) / 2)) := by rw [← pow_mul, Nat.mul_comm]
    _ < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hm

/-! ## Extensions: monotonicity, the full sub-threshold range, and the literal `2^{k/2}` form

`expectedMonoCliques_lt_one_of_sq_lt` and its witness `expectedMonoCliques_lt_one_pow`
settle OQ-04 at the single point `n = 2^{⌊(k-1)/2⌋}`.  The following round out the result:
the expected count is monotone in `n` (so the bound holds for *every* `n` below the
witness, not just at it), and the hypothesis can be stated in the literal half-power form
`n < 2^{k/2}` the gallery question uses, over `ℝ`. -/

/-- **Monotonicity in `n`.**  The expected number of monochromatic `k`-cliques is
non-decreasing in the number of vertices: `m ≤ n ⟹ E(m,k) ≤ E(n,k)`.  Immediate from
monotonicity of `C(·,k)` and positivity of the constant factor `2^{1−C(k,2)}`. -/
theorem expectedMonoCliques_mono_left {m n k : ℕ} (h : m ≤ n) :
    expectedMonoCliques m k ≤ expectedMonoCliques n k := by
  unfold expectedMonoCliques
  apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)
  exact_mod_cast Nat.choose_mono k h

/-- **OQ-04 over the whole sub-threshold range.**  For `k ≥ 3`, *every* `n` with
`n ≤ 2^{⌊(k-1)/2⌋}` has `E(n,k) < 1` — not merely the endpoint.  Combines
`expectedMonoCliques_mono_left` with the endpoint witness `expectedMonoCliques_lt_one_pow`. -/
theorem expectedMonoCliques_lt_one_of_le_pow {k : ℕ} (hk : 3 ≤ k) {n : ℕ}
    (hn : n ≤ 2 ^ ((k - 1) / 2)) : expectedMonoCliques n k < 1 :=
  (expectedMonoCliques_mono_left hn).trans_lt (expectedMonoCliques_lt_one_pow hk)

/-- **OQ-04 in the literal half-power form.**  The gallery question asks for `E(n,k) < 1`
when `n < 2^{k/2}`.  Here that hypothesis is stated over `ℝ` with the genuine real
exponent `(k:ℝ)/2`; squaring it recovers the `ℕ` hypothesis `n² < 2^k` of
`expectedMonoCliques_lt_one_of_sq_lt`, so the two forms are equivalent and this closes the
statement exactly as phrased. -/
theorem expectedMonoCliques_lt_one_of_lt_sqrt {n k : ℕ} (hk : 3 ≤ k)
    (hn : (n : ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2)) : expectedMonoCliques n k < 1 := by
  apply expectedMonoCliques_lt_one_of_sq_lt hk
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  -- `(2^{k/2})² = 2^k` in `ℝ`.
  have hpow : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ (2 : ℕ) = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul h2,
      show (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = (k : ℝ) from by push_cast; ring, Real.rpow_natCast]
  -- Square the hypothesis and rewrite the RHS.
  have hsq : (n : ℝ) ^ 2 < (2 : ℝ) ^ k := by
    have hstep : (n : ℝ) ^ 2 < ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ (2 : ℕ) := by
      nlinarith [mul_pos (show (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2) - n by linarith)
        (show (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2) + n by positivity)]
    exact hstep.trans_eq hpow
  -- Descend to `ℕ`.
  have hcast : ((n ^ 2 : ℕ) : ℝ) < ((2 ^ k : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast hcast

end ProbMethod.ExpectationOQ04
