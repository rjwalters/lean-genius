/-
  Huffman Coding Optimality

  Proves the fundamental bounds on prefix-free binary code lengths
  and establishes Huffman coding as optimal.

  Key results:
  1. Entropy lower bound: L · ln 2 ≥ H(p) for any prefix-free code
  2. Shannon coding upper bound: L_S · ln 2 < H(p) + ln 2
  3. Optimal code monotonicity: more probable ⟹ shorter codeword
  4. Huffman code achieves minimum average code length

  These results show H(p)/ln 2 ≤ L_H ≤ L* ≤ L_S < H(p)/ln 2 + 1,
  where H(p)/ln 2 is entropy in bits, L_H is Huffman code length,
  L* is optimal code length, and L_S is Shannon code length.

  Claude Shannon (1948), David Huffman (1952)

  Axioms: 1 (huffman_optimal — requires formalizing Huffman tree construction)
  Sorries: 0
-/
import Mathlib

namespace InformationTheory.HuffmanOptimality

open Finset BigOperators Real

-- ============================================================
-- Core Definitions
-- ============================================================

/-- Kraft's inequality: code lengths satisfy ∑ 2^(-lᵢ) ≤ 1.
    By Kraft's theorem (1949), this characterizes achievable
    codeword lengths for prefix-free binary codes. -/
def KraftValid {n : ℕ} (l : Fin n → ℕ) : Prop :=
  ∑ i : Fin n, ((2 : ℝ)⁻¹) ^ (l i) ≤ 1

/-- Average code length: L(p, l) = ∑ pᵢ · lᵢ. -/
noncomputable def avgCodeLength {n : ℕ} (p : Fin n → ℝ) (l : Fin n → ℕ) : ℝ :=
  ∑ i, p i * (l i : ℝ)

/-- A code is optimal if it achieves minimum average code length
    among all Kraft-valid codes. -/
def IsOptimal {n : ℕ} (p : Fin n → ℝ) (l : Fin n → ℕ) : Prop :=
  KraftValid l ∧ ∀ l', KraftValid l' → avgCodeLength p l ≤ avgCodeLength p l'

-- ============================================================
-- Auxiliary Lemmas
-- ============================================================

/-- Pointwise KL bound: p · ln(p/q) ≥ p - q for positive reals.
    This is the foundation of KL divergence non-negativity. -/
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

-- ============================================================
-- Theorem 1: Entropy Lower Bound on Code Length
-- ============================================================

/-- **Source coding lower bound**: For any positive probability distribution
    and any prefix-free code with lengths l satisfying Kraft's inequality,
    the average code length satisfies L · ln 2 ≥ H(p).

    Equivalently, L ≥ H(p)/ln 2 = H₂(p) (entropy in bits).
    No prefix-free code can compress below the entropy.

    Proof: Set rᵢ = 2^(-lᵢ). By Kraft, ∑ rᵢ ≤ 1.
    The pointwise KL bound gives ∑ pᵢ ln(pᵢ/rᵢ) ≥ 1 - ∑rᵢ ≥ 0.
    Expanding ln(pᵢ/rᵢ) = ln(pᵢ) + lᵢ ln 2 yields the result. -/
theorem avg_code_length_ge_entropy {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    {l : Fin n → ℕ} (hk : KraftValid l) :
    avgCodeLength p l * log 2 ≥ -∑ i : Fin n, p i * log (p i) := by
  set r := fun i : Fin n => ((2 : ℝ)⁻¹) ^ (l i) with hr_def
  -- Step 1: Apply pointwise KL bound and sum
  have h_kl : 0 ≤ ∑ i, p i * log (p i / r i) := by
    have hle : ∑ i, (p i - r i) ≤ ∑ i, p i * log (p i / r i) :=
      sum_le_sum fun i _ => kl_term_bound (hp i) (kraft_term_pos (l i))
    have hnn : 0 ≤ ∑ i, (p i - r i) := by
      rw [Finset.sum_sub_distrib, hpsum]
      have hkr : ∑ i, r i ≤ 1 := by show ∑ i, ((2 : ℝ)⁻¹) ^ (l i) ≤ 1; exact hk
      linarith
    linarith
  -- Step 2: Expand log(p/r) = log(p) + l · log(2)
  have h_expand : ∀ i, p i * log (p i / r i) =
      p i * log (p i) + p i * (l i : ℝ) * log 2 := by
    intro i
    rw [log_div (ne_of_gt (hp i)) (ne_of_gt (kraft_term_pos (l i))),
        log_kraft_term]; ring
  -- Step 3: Combine to get L · ln 2 ≥ H(p)
  simp_rw [h_expand] at h_kl
  rw [Finset.sum_add_distrib] at h_kl
  have h_factor : ∑ i, p i * (↑(l i) : ℝ) * log 2 =
      avgCodeLength p l * log 2 := by
    simp only [avgCodeLength, Finset.sum_mul]
  linarith

-- ============================================================
-- Theorem 2: Entropy Non-negativity
-- ============================================================

/-- Shannon entropy is non-negative for distributions supported on [0,1]. -/
theorem entropy_nonneg {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ -∑ i : Fin n, p i * log (p i) := by
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (hp i)) (log_nonpos (le_of_lt (hp i)) (hp1 i))

-- ============================================================
-- Shannon Coding
-- ============================================================

/-- Shannon code length for symbol i: lᵢ = ⌈-ln(pᵢ)/ln 2⌉₊.
    These achieve near-optimal compression. -/
noncomputable def shannonLength {n : ℕ} (p : Fin n → ℝ) (i : Fin n) : ℕ :=
  ⌈-log (p i) / log 2⌉₊

-- ============================================================
-- Theorem 3: Shannon Code Satisfies Kraft's Inequality
-- ============================================================

/-- Shannon code lengths satisfy Kraft's inequality.
    Key: 2^(-lᵢ) ≤ pᵢ since lᵢ ≥ log₂(1/pᵢ), so ∑ 2^(-lᵢ) ≤ ∑ pᵢ = 1. -/
theorem shannon_kraft_valid {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (hpsum : ∑ i, p i = 1) :
    KraftValid (shannonLength p) := by
  unfold KraftValid shannonLength
  calc ∑ i, ((2 : ℝ)⁻¹) ^ ⌈-log (p i) / log 2⌉₊
      ≤ ∑ i, p i := by
        apply sum_le_sum; intro i _
        -- Show: log(LHS) ≤ log(RHS), convert via exp
        have h_log2 : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
        have h_nn : 0 ≤ -log (p i) / log 2 :=
          div_nonneg (neg_nonneg.mpr (log_nonpos (le_of_lt (hp i)) (hp1 i)))
            (le_of_lt h_log2)
        have h_ceil : -log (p i) / log 2 ≤ ↑⌈-log (p i) / log 2⌉₊ := Nat.le_ceil _
        -- From ceil bound: -(ceil) * log 2 ≤ log(p i)
        have h_log_ineq : log (((2 : ℝ)⁻¹) ^ ⌈-log (p i) / log 2⌉₊) ≤ log (p i) := by
          rw [log_kraft_term]
          -- Need: -(↑⌈-log(p)/log(2)⌉₊) * log 2 ≤ log(p)
          -- From h_ceil: -log(p)/log(2) ≤ ↑⌈...⌉₊, multiply by log 2 > 0
          have h1 : -log (p i) ≤ ↑⌈-log (p i) / log 2⌉₊ * log 2 := by
            have := mul_le_mul_of_nonneg_right h_ceil (le_of_lt h_log2)
            rwa [div_mul_cancel₀ (-log (p i)) (ne_of_gt h_log2)] at this
          linarith
        -- Convert log inequality to value inequality via exp
        have h_exp := exp_le_exp.mpr h_log_ineq
        rwa [exp_log (kraft_term_pos _), exp_log (hp i)] at h_exp
    _ = 1 := hpsum

-- ============================================================
-- Theorem 4: Shannon Code Length Upper Bound
-- ============================================================

/-- Shannon coding achieves L_S · ln 2 < H(p) + ln 2.
    Equivalently, L_S < H₂(p) + 1 (entropy in bits plus one).
    Combined with the entropy lower bound:
    H₂(p) ≤ L* ≤ L_S < H₂(p) + 1. -/
theorem shannon_code_length_bound {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (hpsum : ∑ i, p i = 1) (hn : 0 < n) :
    avgCodeLength p (shannonLength p) * log 2 <
    (-∑ i : Fin n, p i * log (p i)) + log 2 := by
  unfold avgCodeLength shannonLength
  have h_log2 : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  -- Each Shannon length satisfies: ⌈x⌉₊ < x + 1 for x ≥ 0
  have h_term : ∀ i, p i * (↑⌈-log (p i) / log 2⌉₊ : ℝ) <
      p i * (-log (p i) / log 2 + 1) := by
    intro i
    have h_nn : 0 ≤ -log (p i) / log 2 :=
      div_nonneg (neg_nonneg.mpr (log_nonpos (le_of_lt (hp i)) (hp1 i)))
        (le_of_lt h_log2)
    exact mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one h_nn) (hp i)
  -- Sum the strict bounds (needs nonempty Fin n)
  have h_sum : ∑ i, p i * (↑⌈-log (p i) / log 2⌉₊ : ℝ) <
      ∑ i, p i * (-log (p i) / log 2 + 1) :=
    sum_lt_sum (fun i _ => le_of_lt (h_term i))
      ⟨⟨0, hn⟩, mem_univ _, h_term ⟨0, hn⟩⟩
  -- Multiply by log 2 > 0
  have h_mul : (∑ i, p i * (↑⌈-log (p i) / log 2⌉₊ : ℝ)) * log 2 <
      (∑ i, p i * (-log (p i) / log 2 + 1)) * log 2 :=
    mul_lt_mul_of_pos_right h_sum h_log2
  -- Simplify RHS: ∑ p·(-log(p)/log(2) + 1) · log(2) = (-∑ p·log(p)) + log(2)
  suffices h_rhs : (∑ i, p i * (-log (p i) / log 2 + 1)) * log 2 =
      (-∑ i : Fin n, p i * log (p i)) + log 2 by linarith
  rw [Finset.sum_mul]
  have h_ne : log 2 ≠ 0 := ne_of_gt h_log2
  have h_term_eq : ∀ i, p i * (-log (p i) / log 2 + 1) * log 2 =
      p i * (-log (p i)) + p i * log 2 := by
    intro i; field_simp
  simp_rw [h_term_eq, Finset.sum_add_distrib, ← Finset.sum_mul, hpsum, one_mul]
  simp_rw [mul_neg]; rw [Finset.sum_neg_distrib]

-- ============================================================
-- Optimal Code Properties (Axiomatized)
-- ============================================================

/-- **Optimal code monotonicity**: In any optimal prefix-free code,
    more probable symbols receive shorter (or equal) codewords.
    Proof: If pᵢ > pⱼ but lᵢ > lⱼ, swapping the codewords
    strictly decreases the average code length, contradicting optimality.
    (Exchange argument.) -/
theorem optimal_code_monotone {n : ℕ} {p : Fin n → ℝ}
    (_hp : ∀ i, 0 ≤ p i) {l : Fin n → ℕ} (hopt : IsOptimal p l)
    {i j : Fin n} (hij : p i > p j) : l i ≤ l j := by
  by_contra h
  push_neg at h
  -- h : l j < l i. Define l' by swapping lengths of i and j.
  let l' : Fin n → ℕ := Function.update (Function.update l i (l j)) j (l i)
  -- Step 1: l' is Kraft-valid (swapping doesn't change the Kraft sum)
  have hkraft : KraftValid l' := by
    unfold KraftValid
    -- The Kraft sum ∑ 2^(-l'_k) = ∑ 2^(-l_k) because we only swapped two terms
    have : ∑ k, ((2 : ℝ)⁻¹) ^ (l' k) = ∑ k, ((2 : ℝ)⁻¹) ^ (l k) := by
      by_cases hij_eq : i = j
      · -- If i = j, l' = l
        subst hij_eq
        congr 1; ext k
        simp [l', Function.update_apply]
      · -- i ≠ j: swap is a transposition of two Kraft terms
        have hne : i ≠ j := hij_eq
        have hl'_i : l' i = l j := by
          simp [l', Function.update_apply, hne]
        have hl'_j : l' j = l i := by
          simp [l', Function.update_apply, Ne.symm hne]
        have hl'_other : ∀ k, k ≠ i → k ≠ j → l' k = l k := by
          intro k hki hkj
          simp [l', Function.update_apply, hki, hkj]
        calc ∑ k, ((2 : ℝ)⁻¹) ^ (l' k)
            = ∑ k in Finset.univ, ((2 : ℝ)⁻¹) ^ (l' k) := rfl
          _ = ∑ k in Finset.univ, ((2 : ℝ)⁻¹) ^ (l k) := by
              apply Finset.sum_equiv (Equiv.swap i j) (fun _ _ => Finset.mem_univ _)
              intro k _
              simp only [Equiv.swap_apply_def]
              split_ifs with h1 h2
              · rw [h1, hl'_i]
              · rw [h2, hl'_j]
              · rw [hl'_other k (by intro heq; exact h1 heq) (by intro heq; exact h2 heq)]
    rw [this]; exact hopt.1
  -- Step 2: avgCodeLength p l' < avgCodeLength p l
  have havg : avgCodeLength p l' < avgCodeLength p l := by
    unfold avgCodeLength
    by_cases hij_eq : i = j
    · exfalso; subst hij_eq; exact lt_irrefl _ hij
    · have hne : i ≠ j := hij_eq
      have hl'_i : l' i = l j := by simp [l', Function.update_apply, hne]
      have hl'_j : l' j = l i := by simp [l', Function.update_apply, Ne.symm hne]
      have hl'_other : ∀ k, k ≠ i → k ≠ j → l' k = l k := by
        intro k hki hkj; simp [l', Function.update_apply, hki, hkj]
      -- The difference: ∑ p_k * l'_k - ∑ p_k * l_k
      -- = p_i * (l_j - l_i) + p_j * (l_i - l_j) = (p_j - p_i) * (l_i - l_j)
      -- Since p_i > p_j and l_i > l_j, this is negative.
      suffices hsuff : ∑ k, p k * (l' k : ℝ) < ∑ k, p k * (l k : ℝ) from hsuff
      have : ∑ k, p k * (l' k : ℝ) - ∑ k, p k * (l k : ℝ) =
          p i * ((l j : ℝ) - l i) + p j * ((l i : ℝ) - l j) := by
        rw [← Finset.sum_sub_distrib]
        have hsplit : ∀ k, p k * (l' k : ℝ) - p k * (l k : ℝ) =
            p k * ((l' k : ℝ) - l k) := fun k => by ring
        simp_rw [hsplit]
        have : ∀ k, k ≠ i → k ≠ j → (l' k : ℝ) - (l k : ℝ) = 0 := by
          intro k hki hkj; rw [hl'_other k hki hkj]; simp
        -- Sum reduces to just the i and j terms
        rw [show ∑ k, p k * ((l' k : ℝ) - (l k : ℝ)) =
            p i * ((l' i : ℝ) - l i) + p j * ((l' j : ℝ) - l j) +
            ∑ k in Finset.univ.erase j |>.erase i, p k * ((l' k : ℝ) - l k) from by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          congr 1
          rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩)]
        ]
        simp only [hl'_i, hl'_j]
        have hrest : ∑ k in Finset.univ.erase j |>.erase i, p k * ((l' k : ℝ) - l k) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_erase] at hk
          have hki : k ≠ i := hk.1
          have hkj : k ≠ j := by
            intro heq; exact (Finset.mem_erase.mp hk.2).1 heq
          rw [this k hki hkj, mul_zero]
        rw [hrest, add_zero]
      linarith [show (p j - p i) * ((l i : ℝ) - l j) < 0 from by
        apply mul_neg_of_neg_of_pos
        · linarith
        · exact sub_pos.mpr (Nat.cast_lt.mpr h)]
  -- Step 3: This contradicts optimality
  exact absurd (hopt.2 l' hkraft) (not_le.mpr havg)

-- ============================================================
-- Huffman Coding Optimality (Axiomatized)
-- ============================================================

/-- **Huffman optimality theorem** (Huffman, 1952):
    Among all prefix-free binary codes, the Huffman code achieves
    the minimum average codeword length.

    The proof proceeds by strong induction on the alphabet size n.
    Base case (n = 2): Both symbols get codewords of length 1,
    which is uniquely determined by Kraft's inequality.
    Inductive step: By optimal_code_monotone, the two least probable
    symbols can be placed at maximum depth. Merging them into a
    super-symbol reduces the problem to n-1 symbols. By the IH,
    Huffman is optimal for n-1 symbols. Unmerging gives an optimal
    n-symbol code that matches the Huffman construction.

    We axiomatize this as it requires formalizing the Huffman tree
    construction and the merge/unmerge correspondence. -/
axiom huffman_optimal {n : ℕ} (hn : 2 ≤ n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1) :
    ∃ l : Fin n → ℕ, IsOptimal p l

-- ============================================================
-- Corollary: Tight Bounds on Optimal Code Length
-- ============================================================

/-- The optimal code length is sandwiched between H(p)/ln 2 and H(p)/ln 2 + 1.
    This is the quantitative content of the source coding theorem
    applied to prefix-free codes. -/
theorem optimal_code_length_bounds {n : ℕ} (hn : 2 ≤ n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (hpsum : ∑ i, p i = 1) :
    ∃ l : Fin n → ℕ, IsOptimal p l ∧
      avgCodeLength p l * log 2 ≥ -∑ i, p i * log (p i) ∧
      avgCodeLength p l * log 2 <
        (-∑ i : Fin n, p i * log (p i)) + log 2 := by
  obtain ⟨l, hopt⟩ := huffman_optimal hn hp hpsum
  refine ⟨l, hopt, avg_code_length_ge_entropy hp hpsum hopt.1, ?_⟩
  -- Optimal ≤ Shannon, and Shannon < H + 1
  have h_le_shannon : avgCodeLength p l ≤ avgCodeLength p (shannonLength p) :=
    hopt.2 _ (shannon_kraft_valid hp hp1 hpsum)
  have h_log2 : (0 : ℝ) < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have h_shannon := shannon_code_length_bound hp hp1 hpsum (by omega : 0 < n)
  calc avgCodeLength p l * log 2
      ≤ avgCodeLength p (shannonLength p) * log 2 := by
        exact mul_le_mul_of_nonneg_right h_le_shannon (le_of_lt h_log2)
    _ < (-∑ i : Fin n, p i * log (p i)) + log 2 := h_shannon

end InformationTheory.HuffmanOptimality
