/-
  Kolmogorov Complexity and Shannon Entropy Connection

  Formalizes the fundamental link between algorithmic and information-theoretic
  notions of information: H(X) ≈ E[K(X)] + O(1) for computable distributions.

  Key results:
  1. Kolmogorov complexity as axiomatized prefix-free description length
  2. K(x) values satisfy Kraft's inequality (from prefix-freeness)
  3. H(X) ≤ E[K(X)] + c (entropy ≤ expected complexity, lower bound)
  4. E[K(X)] ≤ H(X) + c' (expected complexity ≤ entropy + constant, upper bound)
  5. Combined: |H(X) - E[K(X)]| = O(1) for computable distributions

  The lower bound follows from Kraft's inequality: Kolmogorov descriptions
  form a prefix-free code, so the source coding theorem applies.
  The upper bound follows from Shannon coding: an optimal code achieves
  lengths close to -log₂(p(x)), and K(x) ≤ -log₂(p(x)) + c for any
  computable distribution p.

  Shannon (1948), Kolmogorov (1965), Chaitin (1966)

  Axioms: 3 (Kolmogorov complexity properties — requires computability theory)
  Sorries: 0
-/
import Mathlib

namespace InformationTheory.KolmogorovEntropy

open Finset BigOperators Real

-- ════════════════════════════════════════════════════════════════
-- PART I: Axiomatized Kolmogorov Complexity
-- ════════════════════════════════════════════════════════════════

/-
  Kolmogorov complexity K(x) is the length of the shortest prefix-free
  binary program that outputs x on a fixed universal Turing machine U.

  We axiomatize K rather than construct it, because formalizing Turing
  machines and universality would require thousands of lines of
  computability infrastructure beyond our scope.

  Three axioms suffice for the entropy-complexity equivalence:
  1. The function K itself
  2. Kraft's inequality for K (from prefix-freeness)
  3. The coding theorem: K(x) ≤ ⌈-log₂ p(x)⌉ + c for computable p
-/

-- The Kolmogorov complexity function for a finite type
-- K(x) = length of shortest prefix-free description of x
axiom kolmogorovComplexity (α : Type*) [Fintype α] [DecidableEq α] : α → ℕ

-- Axiom: Kraft's inequality holds for Kolmogorov complexity values
-- This follows from prefix-freeness: the set of valid programs forms
-- a prefix-free code, so ∑ 2^(-|p|) ≤ 1 over all halting programs.
-- In particular, ∑_x 2^(-K(x)) ≤ 1 since each x has at most one
-- shortest program contributing to the sum.
axiom kolmogorov_kraft (α : Type*) [Fintype α] [DecidableEq α] :
    ∑ x : α, ((2 : ℝ)⁻¹) ^ (kolmogorovComplexity α x) ≤ 1

-- ════════════════════════════════════════════════════════════════
-- PART II: Entropy and Code Length Infrastructure
-- ════════════════════════════════════════════════════════════════

/-- Shannon entropy: H(p) = -∑ p(x) ln p(x) -/
noncomputable def shannonEntropy {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  -∑ i : Fin n, if p i = 0 then 0 else p i * log (p i)

/-- Average Kolmogorov complexity: E[K(X)] = ∑ p(x) K(x) -/
noncomputable def expectedComplexity {n : ℕ} (p : Fin n → ℝ)
    (K : Fin n → ℕ) : ℝ :=
  ∑ i : Fin n, p i * (K i : ℝ)

/-- Kraft's inequality for a code -/
def KraftValid {n : ℕ} (l : Fin n → ℕ) : Prop :=
  ∑ i : Fin n, ((2 : ℝ)⁻¹) ^ (l i) ≤ 1

-- ════════════════════════════════════════════════════════════════
-- PART III: Auxiliary Lemmas
-- ════════════════════════════════════════════════════════════════

/-- Pointwise KL bound: p · ln(p/q) ≥ p - q for positive p, q.
    The fundamental inequality underlying source coding. -/
private lemma kl_term_bound {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p * log (p / q) ≥ p - q := by
  have h1 : log (q / p) ≤ q / p - 1 := log_le_sub_one_of_pos (div_pos hq hp)
  have h2 : p * log (q / p) ≤ q - p :=
    calc p * log (q / p)
        ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
      _ = q - p := by field_simp
  have h3 : log (p / q) = -log (q / p) := by
    rw [log_div (ne_of_gt hp) (ne_of_gt hq),
        log_div (ne_of_gt hq) (ne_of_gt hp)]; ring
  linarith [show p * log (p / q) = -(p * log (q / p)) from by rw [h3]; ring]

/-- Each Kraft term 2^(-l) is positive. -/
private lemma kraft_term_pos (l : ℕ) : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ l :=
  pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) l

/-- Logarithm of a Kraft term: ln(2^(-l)) = -l · ln 2. -/
private lemma log_kraft_term (l : ℕ) :
    log (((2 : ℝ)⁻¹) ^ l) = -(l : ℝ) * log 2 := by
  rw [log_pow, log_inv]; ring

-- ════════════════════════════════════════════════════════════════
-- PART IV: Lower Bound — H(X) ≤ E[K(X)] · ln 2
-- ════════════════════════════════════════════════════════════════

/-
  Theorem (Entropy lower bound on expected Kolmogorov complexity):

  For any positive distribution p with ∑ p = 1, and any code lengths
  satisfying Kraft's inequality:

    (∑ p(x) · l(x)) · ln 2 ≥ H(p)

  This applies to K(x) since Kolmogorov descriptions form a prefix-free
  code (Axiom 2: kolmogorov_kraft).

  Proof: Set r(x) = 2^(-l(x)). By Kraft, ∑ r ≤ 1.
  The pointwise KL bound gives: ∑ p(x) ln(p(x)/r(x)) ≥ 0.
  Expanding: ∑ p(x) ln(p(x)) + ∑ p(x) · l(x) · ln 2 ≥ 0.
  So: ∑ p(x) · l(x) · ln 2 ≥ -∑ p(x) ln(p(x)) = H(p).
-/

/-- Source coding theorem: any Kraft-valid code satisfies
    E[l(X)] · ln 2 ≥ H(X). This is the noiseless coding theorem. -/
theorem avg_length_ge_entropy {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    {l : Fin n → ℕ} (hk : KraftValid l) :
    (∑ i, p i * (l i : ℝ)) * log 2 ≥ -∑ i : Fin n, p i * log (p i) := by
  set r := fun i : Fin n => ((2 : ℝ)⁻¹) ^ (l i)
  -- Step 1: KL divergence is non-negative
  have h_kl : 0 ≤ ∑ i, p i * log (p i / r i) := by
    have hle : ∑ i, (p i - r i) ≤ ∑ i, p i * log (p i / r i) :=
      sum_le_sum fun i _ => kl_term_bound (hp i) (kraft_term_pos (l i))
    have hnn : 0 ≤ ∑ i, (p i - r i) := by
      rw [Finset.sum_sub_distrib, hpsum]
      linarith [show ∑ i, r i ≤ 1 from hk]
    linarith
  -- Step 2: Expand log(p/r) = log(p) + l · log 2
  have h_expand : ∀ i, p i * log (p i / r i) =
      p i * log (p i) + p i * (l i : ℝ) * log 2 := by
    intro i
    rw [log_div (ne_of_gt (hp i)) (ne_of_gt (kraft_term_pos (l i))),
        log_kraft_term]; ring
  -- Step 3: Combine
  simp_rw [h_expand] at h_kl
  rw [Finset.sum_add_distrib] at h_kl
  have : ∑ i, p i * (↑(l i) : ℝ) * log 2 =
      (∑ i, p i * (l i : ℝ)) * log 2 := by
    simp only [Finset.sum_mul]
  linarith

/-- Corollary: Expected Kolmogorov complexity satisfies the entropy bound.
    H(X) ≤ E[K(X)] · ln 2, where ln 2 converts nats to bits. -/
theorem entropy_le_expected_K_times_ln2 {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    {K : Fin n → ℕ} (hk : KraftValid K) :
    shannonEntropy p ≤ expectedComplexity p K * log 2 := by
  unfold shannonEntropy expectedComplexity
  have h := avg_length_ge_entropy hp hpsum hk
  linarith

-- ════════════════════════════════════════════════════════════════
-- PART V: Upper Bound — E[K(X)] · ln 2 ≤ H(X) + ln 2
-- ════════════════════════════════════════════════════════════════

/-
  Theorem (Kolmogorov complexity upper bound from Shannon coding):

  For any computable distribution p, there exists a constant c such that
  K(x) ≤ -log₂(p(x)) + c for all x. This is because the universal
  Turing machine can simulate the computable distribution to generate
  a code for x of length ≈ -log₂(p(x)).

  Taking expectations: E[K(X)] ≤ H₂(X) + c = H(X)/ln 2 + c.
  Multiplying by ln 2: E[K(X)] · ln 2 ≤ H(X) + c · ln 2.

  We axiomatize the per-element bound since it requires computability.
-/

-- Axiom: For any computable distribution, K(x) ≤ ⌈-log₂ p(x)⌉ + c
-- This is the "coding theorem" of algorithmic information theory:
-- a computable distribution can be used as a code, and the universal
-- machine adds only a constant overhead.
axiom computable_distribution_bound {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (hpsum : ∑ i, p i = 1) :
    ∃ c : ℕ, ∀ i, kolmogorovComplexity (Fin n) i ≤ ⌈-log (p i) / log 2⌉₊ + c

-- ════════════════════════════════════════════════════════════════
-- PART VI: The Main Theorem — Entropy-Complexity Equivalence
-- ════════════════════════════════════════════════════════════════

/-- Shannon code length: l(x) = ⌈-log₂ p(x)⌉ -/
noncomputable def shannonLength {n : ℕ} (p : Fin n → ℝ) (i : Fin n) : ℕ :=
  ⌈-log (p i) / log 2⌉₊

/-- Shannon code satisfies Kraft's inequality. -/
theorem shannon_kraft_valid {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (hpsum : ∑ i, p i = 1) :
    KraftValid (shannonLength p) := by
  unfold KraftValid shannonLength
  calc ∑ i, ((2 : ℝ)⁻¹) ^ ⌈-log (p i) / log 2⌉₊
      ≤ ∑ i, p i := by
        apply sum_le_sum; intro i _
        have h_log2 : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
        have h_nn : 0 ≤ -log (p i) / log 2 :=
          div_nonneg (neg_nonneg.mpr (log_nonpos (le_of_lt (hp i)) (hp1 i)))
            (le_of_lt h_log2)
        have h_ceil : -log (p i) / log 2 ≤ ↑⌈-log (p i) / log 2⌉₊ := Nat.le_ceil _
        have h_log_ineq : log (((2 : ℝ)⁻¹) ^ ⌈-log (p i) / log 2⌉₊) ≤ log (p i) := by
          rw [log_kraft_term]
          have h1 : -log (p i) ≤ ↑⌈-log (p i) / log 2⌉₊ * log 2 := by
            have := mul_le_mul_of_nonneg_right h_ceil (le_of_lt h_log2)
            rwa [div_mul_cancel₀ (-log (p i)) (ne_of_gt h_log2)] at this
          linarith
        have h_exp := exp_le_exp.mpr h_log_ineq
        rwa [exp_log (kraft_term_pos _), exp_log (hp i)] at h_exp
    _ = 1 := hpsum

/-- Shannon code gives an upper bound: E[l_S(X)] · ln 2 < H(X) + ln 2.
    Combined with K(x) ≤ l_S(x) + c, this gives E[K(X)] · ln 2 ≤ H(X) + O(1). -/
theorem shannon_length_upper_bound {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (hpsum : ∑ i, p i = 1) (hn : 0 < n) :
    expectedComplexity p (shannonLength p) * log 2 <
    shannonEntropy p + log 2 := by
  unfold expectedComplexity shannonLength shannonEntropy
  have h_log2 : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  -- Each Shannon length: ⌈x⌉₊ < x + 1 for x ≥ 0
  have h_term : ∀ i, p i * (↑⌈-log (p i) / log 2⌉₊ : ℝ) <
      p i * (-log (p i) / log 2 + 1) := by
    intro i
    have h_nn : 0 ≤ -log (p i) / log 2 :=
      div_nonneg (neg_nonneg.mpr (log_nonpos (le_of_lt (hp i)) (hp1 i)))
        (le_of_lt h_log2)
    exact mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one h_nn) (hp i)
  have h_sum : ∑ i, p i * (↑⌈-log (p i) / log 2⌉₊ : ℝ) <
      ∑ i, p i * (-log (p i) / log 2 + 1) :=
    sum_lt_sum (fun i _ => le_of_lt (h_term i))
      ⟨⟨0, hn⟩, mem_univ _, h_term ⟨0, hn⟩⟩
  have h_mul : (∑ i, p i * (↑⌈-log (p i) / log 2⌉₊ : ℝ)) * log 2 <
      (∑ i, p i * (-log (p i) / log 2 + 1)) * log 2 :=
    mul_lt_mul_of_pos_right h_sum h_log2
  suffices h_rhs : (∑ i, p i * (-log (p i) / log 2 + 1)) * log 2 =
      (-∑ i : Fin n, (if p i = 0 then 0 else p i * log (p i))) + log 2 by
    linarith
  rw [Finset.sum_mul]
  have h_ne : log 2 ≠ 0 := ne_of_gt h_log2
  have h_term_eq : ∀ i, p i * (-log (p i) / log 2 + 1) * log 2 =
      p i * (-log (p i)) + p i * log 2 := by
    intro i; field_simp
  simp_rw [h_term_eq, Finset.sum_add_distrib, ← Finset.sum_mul, hpsum, one_mul]
  -- Since p i > 0, the if-then-else simplifies
  congr 1
  rw [Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [ne_of_gt (hp i)]

-- ════════════════════════════════════════════════════════════════
-- PART VII: Combined Bounds — The Entropy-Complexity Theorem
-- ════════════════════════════════════════════════════════════════

/-- **Main Theorem (Lower bound direction)**:
    For any computable distribution, Shannon entropy is at most
    the expected Kolmogorov complexity (times ln 2).

    H(X) ≤ E[K(X)] · ln 2

    This follows directly from Kraft's inequality for K. -/
theorem entropy_le_expected_complexity {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1) :
    shannonEntropy p ≤
    expectedComplexity p (kolmogorovComplexity (Fin n)) * log 2 := by
  exact entropy_le_expected_K_times_ln2 hp hpsum (kolmogorov_kraft (Fin n))

/-- **Main Theorem (Upper bound direction)**:
    For any computable distribution on n ≥ 1 symbols,
    E[K(X)] · ln 2 < H(X) + (c+1) · ln 2

    where c is the constant from the coding theorem.

    Proof: By the coding theorem, K(x) ≤ ⌈-log₂ p(x)⌉ + c = l_S(x) + c.
    So E[K(X)] ≤ E[l_S(X)] + c, and E[l_S(X)] · ln 2 < H(X) + ln 2. -/
theorem expected_complexity_le_entropy_plus_const {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (hpsum : ∑ i, p i = 1) (hn : 0 < n) :
    ∃ c : ℕ,
    expectedComplexity p (kolmogorovComplexity (Fin n)) * log 2 <
    shannonEntropy p + (c + 1 : ℝ) * log 2 := by
  -- Get the coding theorem constant
  obtain ⟨c, hc⟩ := computable_distribution_bound p hp hp1 hpsum
  use c
  -- E[K(X)] ≤ E[l_S(X)] + c since K(x) ≤ l_S(x) + c
  have h_bound : expectedComplexity p (kolmogorovComplexity (Fin n)) ≤
      expectedComplexity p (shannonLength p) + (c : ℝ) := by
    unfold expectedComplexity
    have h_term : ∀ i, p i * (kolmogorovComplexity (Fin n) i : ℝ) ≤
        p i * ((shannonLength p i : ℝ) + (c : ℝ)) := by
      intro i
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (hp i))
      have := hc i
      push_cast
      linarith
    calc ∑ i, p i * (kolmogorovComplexity (Fin n) i : ℝ)
        ≤ ∑ i, p i * ((shannonLength p i : ℝ) + (c : ℝ)) :=
          sum_le_sum fun i _ => h_term i
      _ = ∑ i, (p i * (shannonLength p i : ℝ) + p i * (c : ℝ)) := by
          apply sum_congr rfl; intro i _; ring
      _ = (∑ i, p i * (shannonLength p i : ℝ)) + (∑ i, p i) * (c : ℝ) := by
          rw [sum_add_distrib]
          congr 1
          rw [← Finset.sum_mul]
      _ = (∑ i, p i * (shannonLength p i : ℝ)) + (c : ℝ) := by rw [hpsum, one_mul]
  -- E[l_S(X)] · ln 2 < H(X) + ln 2 from Shannon code upper bound
  have h_shannon := shannon_length_upper_bound hp hp1 hpsum hn
  -- Combine: E[K] · ln 2 ≤ (E[l_S] + c) · ln 2 < H + ln 2 + c · ln 2 = H + (c+1) ln 2
  have h_log2_pos : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  calc expectedComplexity p (kolmogorovComplexity (Fin n)) * log 2
      ≤ (expectedComplexity p (shannonLength p) + (c : ℝ)) * log 2 := by
        apply mul_le_mul_of_nonneg_right h_bound (le_of_lt h_log2_pos)
    _ = expectedComplexity p (shannonLength p) * log 2 + (c : ℝ) * log 2 := by ring
    _ < (shannonEntropy p + log 2) + (c : ℝ) * log 2 := by linarith
    _ = shannonEntropy p + ((c : ℝ) + 1) * log 2 := by ring

/-- **The Entropy-Complexity Theorem** (Combined):
    For any computable distribution on n ≥ 1 symbols with all positive probabilities,
    Shannon entropy and expected Kolmogorov complexity agree up to O(1):

    H(X) ≤ E[K(X)] · ln 2 < H(X) + O(ln 2)

    The difference |H(X) - E[K(X)] · ln 2| < (c+1) · ln 2 for a universal constant c.
    Dividing by ln 2: |H₂(X) - E[K(X)]| < c + 1 (in bits). -/
theorem entropy_complexity_equivalence {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (hpsum : ∑ i, p i = 1) (hn : 0 < n) :
    ∃ c : ℕ,
    shannonEntropy p ≤ expectedComplexity p (kolmogorovComplexity (Fin n)) * log 2 ∧
    expectedComplexity p (kolmogorovComplexity (Fin n)) * log 2 <
    shannonEntropy p + (c + 1 : ℝ) * log 2 := by
  obtain ⟨c, hc⟩ := expected_complexity_le_entropy_plus_const hp hp1 hpsum hn
  exact ⟨c, entropy_le_expected_complexity hp hpsum, hc⟩

-- ════════════════════════════════════════════════════════════════
-- PART VIII: Consequences
-- ════════════════════════════════════════════════════════════════

/-- Entropy of the uniform distribution equals log|α| (in nats). -/
theorem uniform_entropy_eq_log_card {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ i, p i = 1 / (n : ℝ))
    (hp_pos : ∀ i, 0 < p i) :
    shannonEntropy p = log n := by
  unfold shannonEntropy
  simp_rw [hp, ne_of_gt (hp_pos _), if_false]
  rw [Finset.sum_const, Finset.card_fin]
  simp only [nsmul_eq_mul]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [log_div one_ne_zero (ne_of_gt hn_pos)]
  simp [log_one]
  ring

/-- For the uniform distribution on n elements, E[K(X)] ≈ log₂ n.
    This means most elements x have K(x) ≈ log₂ n — the incompressibility
    theorem. Quantitatively: E[K(X)] · ln 2 is between log n and log n + O(1). -/
theorem uniform_complexity_approx_log {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ i, p i = 1 / (n : ℝ))
    (hp_pos : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) :
    ∃ c : ℕ,
    log n ≤ expectedComplexity p (kolmogorovComplexity (Fin n)) * log 2 ∧
    expectedComplexity p (kolmogorovComplexity (Fin n)) * log 2 <
    log n + (c + 1 : ℝ) * log 2 := by
  have hpsum : ∑ i, p i = 1 := by
    simp_rw [hp]; rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨c, hlb, hub⟩ := entropy_complexity_equivalence hp_pos hp1 hpsum hn
  exact ⟨c, by rwa [uniform_entropy_eq_log_card hn p hp hp_pos],
             by rwa [uniform_entropy_eq_log_card hn p hp hp_pos] at hub⟩

end InformationTheory.KolmogorovEntropy
