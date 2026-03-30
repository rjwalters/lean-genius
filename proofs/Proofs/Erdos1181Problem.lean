/-
Erdős Problem #1181: Upper Bound on q(n, log n)

Let q(n,k) denote the least prime which does not divide ∏_{1≤i≤k}(n+i).
Is it true that there exists some c > 0 such that, for all large n,
  q(n, log n) < (1-c)(log n)²?

The upper bound q(n, log n) ≤ (1+o(1))(log n)² follows from the
primorial argument: all primes below q(n,k) divide the product,
so their primorial is at most n^k. By PNT, this gives q ≲ (log n)².

Probabilistic heuristics (Tao) suggest q(n, log n) ≪ (log log n / log log log n) · log n
for all n, which would make the answer "yes" with room to spare.

**Status**: OPEN
**Origin**: Erdős [Er79d, p.78]
**Related**: Erdős Problem #457 (lower bound question)

Reference: https://erdosproblems.com/1181
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib

open Filter Finset

namespace Erdos1181

-- ============================================================================
-- Part I: Core Definitions (shared infrastructure with Problem #457)
-- ============================================================================

/- The product ∏_{1 ≤ i ≤ k} (n + i) = (n+1)(n+2)···(n+k). -/
noncomputable def consecutiveProduct (n : ℕ) (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

/- The consecutive product is always positive. -/
theorem consecutiveProduct_pos (n k : ℕ) (hk : k ≥ 1) :
    consecutiveProduct n k > 0 := by
  unfold consecutiveProduct
  apply Finset.prod_pos
  intro i hi
  simp only [Finset.mem_Icc] at hi
  omega

/- q(n, k): the smallest prime not dividing ∏_{1 ≤ i ≤ k} (n + i). -/
noncomputable def q (n k : ℕ) : ℕ :=
  have : ∃ p, p.Prime ∧ ¬(p ∣ consecutiveProduct n k) := by
    obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (consecutiveProduct n k + 1)
    refine ⟨p, hp, fun hdvd => ?_⟩
    have hpos : 0 < consecutiveProduct n k :=
      Finset.prod_pos (fun i hi => by simp only [Finset.mem_Icc] at hi; omega)
    have hle_prod := Nat.le_of_dvd hpos hdvd
    omega
  Nat.find this

-- ============================================================================
-- Part II: Properties of q(n, k)
-- ============================================================================

/- q(n,k) is prime. -/
theorem q_prime (n k : ℕ) : (q n k).Prime := by
  unfold q
  exact (Nat.find_spec _).1

/- q(n,k) does not divide the consecutive product. -/
theorem q_not_dvd (n k : ℕ) : ¬((q n k) ∣ consecutiveProduct n k) := by
  unfold q
  exact (Nat.find_spec _).2

/- q(n,k) is minimal: every prime below q(n,k) divides the product. -/
theorem q_minimal (n k : ℕ) (p : ℕ) (hp : p.Prime) (hp_lt : p < q n k)
    (hdvd : ¬(p ∣ consecutiveProduct n k)) : False := by
  unfold q at hp_lt
  have := Nat.find_min _ hp_lt
  exact this ⟨hp, hdvd⟩

-- ============================================================================
-- Part III: Trivial Upper Bound — q(n,k) ≤ (1+o(1))(log n)²
-- ============================================================================

/- The primorial of x is the product of all primes up to x.
   By PNT, log(primorial(x)) ~ x.

   Key argument: All primes p < q(n,k) divide ∏(n+i), so
   primorial(q(n,k)) ≤ ∏(n+i) ≤ (n+k)^k.
   Taking logs: q(n,k) ~ (1+o(1)) · k · log(n+k).
   For k = ⌊log n⌋: q(n, log n) ≤ (1+o(1))(log n)². -/

-- ============================================================================
-- Part IV: The Main Conjecture (Erdős #1181, OPEN)
-- ============================================================================

/- Erdős #1181 asks: can we improve the 1+o(1) to 1-c for fixed c > 0?
   That is, does q(n, log n) < (1-c)(log n)² hold eventually?

   The distinction matters: the trivial bound gives (1+o(1)) which
   approaches 1 from above. The conjecture asks whether the constant
   is strictly BELOW 1 for all large n. -/

/-- Erdős Problem #1181: ∃ c > 0 such that q(n, ⌊log n⌋) < (1-c)(log n)²
    for all sufficiently large n. -/
def erdos1181_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop,
    (q n ⌊Real.log (n : ℝ)⌋₊ : ℝ) < (1 - c) * (Real.log n) ^ 2

/-- The conjecture is axiomatized as it remains open. -/
axiom erdos_1181 : erdos1181_conjecture

-- ============================================================================
-- Part V: Tao's Heuristic Bound
-- ============================================================================

/- Probabilistic heuristics described by Tao suggest that
   q(n, log n) ≪ (log log n / log log log n) · log n
   for all n. If true, this is dramatically stronger than
   the (1-c)(log n)² bound in the conjecture. -/

/-- Tao's heuristic: q(n, log n) ≪ (log log n / log log log n) · log n.
    This would imply Erdős #1181 since log log n · log n ≪ (log n)². -/
def tao_heuristic_bound : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in atTop,
    (q n ⌊Real.log (n : ℝ)⌋₊ : ℝ) ≤
      C * (Real.log (Real.log n) / Real.log (Real.log (Real.log n))) * Real.log n

/-- Iterated logarithms grow slower than log:
    C · (log log n / log log log n) < (1/2) · log n eventually.
    This is because log n → ∞ while log log n / log log log n grows much slower. -/
theorem iterated_log_sublinear (C : ℝ) (hC : C > 0) :
    ∀ᶠ (n : ℕ) in atTop,
      C * (Real.log (Real.log (n : ℝ)) / Real.log (Real.log (Real.log (n : ℝ)))) <
        (1 : ℝ) / 2 * Real.log (n : ℝ) := by
  -- Strategy: for large n, log(log(log n)) ≥ 1 so the division makes things smaller.
  -- Then C * log(log n) < (1/2) * log n since log(log n)/log n → 0.
  -- (a) Eventually log(log n) < (1/(2C)) * log n
  have ha : ∀ᶠ n in (atTop : Filter ℕ),
      Real.log (Real.log (n : ℝ)) < (1 / (2 * C)) * Real.log (n : ℝ) := by
    -- log(log n) / log n → 0 (from log x / x → 0 composed with log n → ∞)
    have hlogn_tend : Tendsto (fun n : ℕ => Real.log (↑n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlogx_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
      have h := Real.tendsto_log_div_rpow_atTop 1 one_pos
      simp only [Real.rpow_one] at h; exact h
    -- Compose: log(log n) / log n → 0
    have h_ratio := hlogx_div.comp hlogn_tend
    -- Extract: eventually log(log n) / log n < 1/(2C)
    have h_small := h_ratio.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C) by positivity))
    -- Eventually log n > 0 (for multiplication)
    have h_logn_pos : ∀ᶠ n in (atTop : Filter ℕ), 0 < Real.log (↑n : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    filter_upwards [h_small, h_logn_pos] with n h_small h_pos
    rw [Set.mem_Iio, div_lt_iff h_pos] at h_small
    linarith
  -- (b) Eventually log(log(log n)) ≥ 1 (iterated log → ∞)
  have hb : ∀ᶠ n in (atTop : Filter ℕ),
      1 ≤ Real.log (Real.log (Real.log (n : ℝ))) := by
    have : Tendsto (Real.log ∘ Real.log ∘ Real.log ∘ (Nat.cast : ℕ → ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    exact this (Filter.mem_atTop 1)
  -- (c) Eventually log(log n) > 0
  have hc : ∀ᶠ n in (atTop : Filter ℕ),
      0 < Real.log (Real.log (n : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    apply Real.log_pos
    calc Real.log (n : ℝ) ≥ Real.log 16 := by
          apply Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      _ > 1 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℝ) from by norm_num]
          rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)]
          nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  -- Combine: C * (ll/lll) ≤ C * ll < (1/2) * l
  filter_upwards [ha, hb, hc] with n ha hb hc
  have hlll_pos : 0 < Real.log (Real.log (Real.log (n : ℝ))) := by linarith
  calc C * (Real.log (Real.log ↑n) / Real.log (Real.log (Real.log ↑n)))
      ≤ C * Real.log (Real.log ↑n) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
        exact div_le_self (le_of_lt hc) hb
    _ < C * ((1 / (2 * C)) * Real.log ↑n) := by
        exact mul_lt_mul_of_pos_left ha hC
    _ = 1 / 2 * Real.log ↑n := by field_simp

/-- If Tao's heuristic holds, then Erdős #1181 follows.
    Proof sketch: C · (log log n / log log log n) · log n ≪ (log n)²
    since (log log n / log log log n) → ∞ much slower than log n. -/
theorem tao_implies_erdos1181 (h : tao_heuristic_bound) : erdos1181_conjecture := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨1/2, by norm_num, ?_⟩
  -- For large n, the Tao bound implies the Erdős bound:
  -- q ≤ C·(loglog/logloglog)·log n < (1/2)·(log n)² when C·(loglog/logloglog) < (1/2)·log n
  filter_upwards [hev, iterated_log_sublinear C hC,
    Filter.eventually_ge_atTop 3] with n hn hgrowth hn3
  have hln_pos : (0 : ℝ) < Real.log (n : ℝ) := by
    apply Real.log_pos; push_cast; omega
  calc (q n ⌊Real.log (↑n : ℝ)⌋₊ : ℝ)
      ≤ C * (Real.log (Real.log n) / Real.log (Real.log (Real.log n))) * Real.log n := hn
    _ < (1 : ℝ) / 2 * Real.log (n : ℝ) * Real.log (n : ℝ) := by nlinarith
    _ = (1 - 1 / 2) * (Real.log (n : ℝ)) ^ 2 := by ring

-- ============================================================================
-- Part VI: Connection to Primorials and PNT
-- ============================================================================

/- The Chebyshev function θ(x) = ∑_{p ≤ x} log p satisfies
   θ(x) ~ x by PNT. The primorial p# = ∏_{p ≤ x} p satisfies
   log(p#) = θ(x) ~ x.

   For q(n,k): all primes below q divide ∏(n+i), so
   ∏_{p < q, p prime} p ≤ ∏(n+i) ≤ (n+k)^k
   ⟹ θ(q) ≤ k · log(n+k)
   ⟹ q ≤ (1+o(1)) · k · log(n+k)     (by PNT)
   For k = ⌊log n⌋: q ≤ (1+o(1))(log n)². -/

-- ============================================================================
-- Part VII: Connection to Problem #457
-- ============================================================================

/- Erdős #457 concerns the LOWER bound for q(n, log n):
   is q(n, log n) ≥ (2+ε) log n infinitely often?

   Problem #1181 concerns the UPPER bound:
   is q(n, log n) < (1-c)(log n)² for all large n?

   Together they would sandwich q(n, log n) between
   Ω(log n) and O((log n)²), with specific constants. -/

/-- Problem #457 conjecture: q(n, log n) ≥ (2+ε) log n infinitely often. -/
def erdos457_conjecture : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    { n : ℕ | (2 + ε) * Real.log n ≤ (q n ⌊Real.log (n : ℝ)⌋₊ : ℝ) }.Infinite

/-- The two conjectures are compatible: if both hold, then
    for large n we have (2+ε) log n ≤ q(n, log n) < (1-c)(log n)²
    infinitely often. -/
theorem conjectures_compatible (h457 : erdos457_conjecture) (h1181 : erdos1181_conjecture) :
    ∃ ε c : ℝ, ε > 0 ∧ c > 0 ∧
      { n : ℕ | (2 + ε) * Real.log n ≤ (q n ⌊Real.log (n : ℝ)⌋₊ : ℝ) ∧
                 (q n ⌊Real.log (n : ℝ)⌋₊ : ℝ) < (1 - c) * (Real.log n) ^ 2 }.Infinite := by
  obtain ⟨ε, hε, h457_inf⟩ := h457
  obtain ⟨c, hc, h1181_ev⟩ := h1181
  refine ⟨ε, c, hε, hc, ?_⟩
  -- The set satisfying the upper bound is cofinite (from the eventually condition).
  -- The set satisfying the lower bound is infinite (from #457).
  -- An infinite set minus a finite set is infinite.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h1181_ev
  have h_comp_finite :
      {n : ℕ | ¬((q n ⌊Real.log (↑n : ℝ)⌋₊ : ℝ) <
        (1 - c) * (Real.log (↑n : ℝ)) ^ 2)}.Finite := by
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_Iio]
    by_contra h_ge
    push_neg at h_ge
    exact hn (hN n h_ge)
  exact (h457_inf.diff h_comp_finite).mono fun n hn =>
    ⟨hn.1, not_not.mp hn.2⟩

-- ============================================================================
-- Part VIII: Summary
-- ============================================================================

/-
**Erdős Problem #1181: Summary**

PROBLEM: Let q(n,k) be the least prime not dividing ∏_{1≤i≤k}(n+i).
         Is there c > 0 such that q(n, ⌊log n⌋) < (1-c)(log n)²
         for all sufficiently large n?

STATUS: OPEN

KNOWN:
- q(n, log n) ≤ (1+o(1))(log n)²  (primorial/PNT argument)
- The question asks for improvement from (1+o(1)) to (1-c) for fixed c > 0
- Tao's heuristic suggests q(n, log n) ≪ (log log n / log log log n) · log n

RELATED:
- Problem #457: lower bound q(n, log n) ≥ (2+ε) log n infinitely often
- Together they would sandwich q between Ω(log n) and O((log n)²)

The gap between the trivial (1+o(1)) and the conjectured (1-c)
represents genuine mathematical content about the distribution
of prime factors in consecutive products.
-/
theorem erdos_1181_main : erdos1181_conjecture := erdos_1181

end Erdos1181
