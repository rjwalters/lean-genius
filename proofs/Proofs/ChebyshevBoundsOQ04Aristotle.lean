/-
  Aristotle targets for ChebyshevBoundsOQ04
  See ChebyshevBoundsOQ04.lean for the main formalization.

  psi_doubling_le_log_centralBinom is now PROVED in the main file.
  This companion targets chebyshevPsi_upper_bound (psi(n) <= 2n*log2).

  Strategy: strong induction. Even case uses chebyshevPsi_doubling_le.
  Odd case: psi(2k+1) <= psi(2(k+1)) <= psi(k+1) + 2(k+1)*log2 <= 2(k+1)*log2 + 2(k+1)*log2
  which gives 4(k+1)*log2. Need <= 2(2k+1)*log2 = (4k+2)*log2. Off by 2*log2.
  Alternative: use psi(2k+1) - psi(k) <= log C(2k+2, k+1) <= (2k+2)*log2 by the
  same log-factorial-vonMangoldt argument.
-/
import Mathlib

namespace ChebyshevBoundsOQ04Aristotle

open Nat Finset ArithmeticFunction

noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), vonMangoldt k

private lemma chebyshevPsi_mono {m n : ℕ} (h : m ≤ n) :
    chebyshevPsi m ≤ chebyshevPsi n :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ h))
    (fun k _ _ => vonMangoldt_nonneg)

private lemma log_factorial_vonMangoldt (m : ℕ) :
    Real.log (m.factorial : ℝ) =
    ∑ d ∈ Finset.range (m + 1), vonMangoldt d * (m / d : ℕ) := by
  have hsum_log : Real.log (m.factorial : ℝ) =
      ∑ k ∈ Finset.range (m + 1), Real.log (k : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
            (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)),
          Finset.sum_range_succ]
      linarith
  rw [hsum_log]
  simp_rw [← vonMangoldt_sum]
  have hcompat : ∀ (k d : ℕ), k ∈ Finset.range (m + 1) ∧ d ∈ k.divisors ↔
      k ∈ (Finset.range (m + 1)).filter (fun k' => k' ≠ 0 ∧ d ∣ k') ∧
      d ∈ Finset.range (m + 1) := by
    intro k d
    simp only [Finset.mem_range, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hdvd, hkne⟩
      exact ⟨⟨hk, hkne, hdvd⟩, (Nat.le_of_dvd (by omega) hdvd).trans_lt hk⟩
    · rintro ⟨⟨hk, hkne, hdvd⟩, _⟩
      exact ⟨hk, hdvd, hkne⟩
  rw [Finset.sum_comm' hcompat]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_const, Nat.card_multiples']
  simp [nsmul_eq_mul, mul_comm]

private theorem psi_doubling_le_log_centralBinom (n : ℕ) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ Real.log (Nat.centralBinom n : ℝ) := by
  have hbinom : Real.log (Nat.centralBinom n : ℝ) =
      Real.log ((2 * n).factorial : ℝ) - 2 * Real.log (n.factorial : ℝ) := by
    have hdvd : n.factorial * n.factorial ∣ (2 * n).factorial := by
      have h := Nat.factorial_mul_factorial_dvd_factorial (n := 2 * n) (k := n) (by omega)
      rwa [show 2 * n - n = n by omega] at h
    rw [Nat.centralBinom, Nat.choose_eq_factorial_div_factorial (by omega : n ≤ 2 * n),
        show 2 * n - n = n by omega,
        Nat.cast_div hdvd (by positivity),
        Real.log_div (by positivity) (by positivity),
        Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hbinom, log_factorial_vonMangoldt (2 * n), log_factorial_vonMangoldt n]
  have hextend : ∑ d ∈ Finset.range (n + 1), vonMangoldt d * (n / d : ℕ) =
      ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (n / d : ℕ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro d hd hdn
    simp only [Finset.mem_range, not_lt] at hd hdn
    have : n / d = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]
  rw [hextend]
  have hpsi : chebyshevPsi (2 * n) - chebyshevPsi n =
      ∑ d ∈ Finset.Ioc n (2 * n), vonMangoldt d := by
    have hle : Finset.range (n + 1) ⊆ Finset.range (2 * n + 1) := Finset.range_mono (by omega)
    have heq : Finset.range (2 * n + 1) \ Finset.range (n + 1) = Finset.Ioc n (2 * n) := by
      ext d; simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]; omega
    simp only [chebyshevPsi, ← heq]
    linarith [Finset.sum_sdiff hle (f := vonMangoldt)]
  rw [hpsi]
  have hIoc_sub : Finset.Ioc n (2 * n) ⊆ Finset.range (2 * n + 1) := by
    intro d hd; simp only [Finset.mem_Ioc] at hd; simp only [Finset.mem_range]; omega
  have hcoeff_one : ∀ d ∈ Finset.Ioc n (2 * n),
      (2 * n / d : ℕ) = 1 ∧ (n / d : ℕ) = 0 := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    exact ⟨Nat.div_eq_of_lt_le (by omega) (by omega),
           Nat.div_eq_of_lt (by omega)⟩
  have hrhs_split : ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (2 * n / d : ℕ) -
      2 * ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (n / d : ℕ) =
      ∑ d ∈ Finset.range (2 * n + 1),
        vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext d; push_cast; ring
  rw [hrhs_split]
  calc ∑ d ∈ Finset.Ioc n (2 * n), vonMangoldt d
      = ∑ d ∈ Finset.Ioc n (2 * n),
            vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨h1, h2⟩ := hcoeff_one d hd
          simp [h1, h2]
    _ ≤ ∑ d ∈ Finset.range (2 * n + 1),
            vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hIoc_sub (fun d hd_range _ => by
            apply mul_nonneg vonMangoldt_nonneg
            have hh := Nat.mul_div_le_mul_div_assoc 2 n d
            have hR : (2 * (n / d : ℕ) : ℝ) ≤ ↑(2 * n / d) := by exact_mod_cast hh
            linarith)

private theorem chebyshevPsi_doubling_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h_psi_le := psi_doubling_le_log_centralBinom n
  have h_log_le : Real.log (Nat.centralBinom n : ℝ) ≤ 2 * ↑n * Real.log 2 := by
    have hle : Nat.centralBinom n ≤ 4 ^ n := by
      calc Nat.centralBinom n = Nat.choose (2 * n) n := rfl
        _ ≤ ∑ k ∈ range (2 * n + 1), Nat.choose (2 * n) k :=
            Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
        _ = 2 ^ (2 * n) := by rw [Nat.sum_range_choose]
        _ = (2 ^ 2) ^ n := by rw [pow_mul]
        _ = 4 ^ n := by norm_num
    calc Real.log (Nat.centralBinom n : ℝ)
        ≤ Real.log ((4 : ℝ) ^ n) := by
            apply Real.log_le_log (by exact_mod_cast Nat.centralBinom_pos n)
            exact_mod_cast hle
      _ = ↑n * Real.log 4 := by rw [Real.log_pow]
      _ = 2 * ↑n * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
  linarith

set_option maxHeartbeats 800000 in
private theorem psi_odd_le_log_choose (m : ℕ) :
    chebyshevPsi (2 * m + 1) - chebyshevPsi (m + 1) ≤
    Real.log (Nat.choose (2 * m + 1) m : ℝ) := by
  -- Express log C(2m+1, m) = log((2m+1)!) - log(m!) - log((m+1)!) using the definition of binomial coefficients.
  have h_log_choose : Real.log (Nat.choose (2 * m + 1) m) = Real.log (Nat.factorial (2 * m + 1)) - Real.log (Nat.factorial m) - Real.log (Nat.factorial (m + 1)) := by
    rw [ Nat.cast_choose ] <;> try linarith;
    rw [ Real.log_div, Real.log_mul ] <;> first | positivity | norm_num [ two_mul, add_assoc ] ; ring;
  -- Use the fact that $\log(n!) = \sum_{d=1}^{n} \Lambda(d) \left\lfloor \frac{n}{d} \right\rfloor$ for any natural number $n$.
  have h_log_factorial (n : ℕ) : Real.log (Nat.factorial n) = ∑ d ∈ Finset.Icc 1 n, vonMangoldt d * ⌊(n : ℝ) / (d : ℝ)⌋ := by
    convert log_factorial_vonMangoldt n using 1;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
    exact Finset.sum_congr rfl fun x hx => by congr; exact Int.floor_eq_iff.mpr ⟨ by rw [ le_div_iff₀ ] <;> norm_cast <;> linarith [ Nat.div_mul_le_self n ( x + 1 ) ], by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.div_add_mod n ( x + 1 ), Nat.mod_lt n ( Nat.succ_pos x ) ] ⟩ ;
  -- Apply the logarithmic factorial formula to each term in the inequality.
  have h_apply_log_factorial : ∑ d ∈ Finset.Icc 1 (2 * m + 1), vonMangoldt d * ⌊(2 * m + 1 : ℝ) / (d : ℝ)⌋ - ∑ d ∈ Finset.Icc 1 m, vonMangoldt d * ⌊(m : ℝ) / (d : ℝ)⌋ - ∑ d ∈ Finset.Icc 1 (m + 1), vonMangoldt d * ⌊((m + 1) : ℝ) / (d : ℝ)⌋ ≥ ∑ d ∈ Finset.Ioc (m + 1) (2 * m + 1), vonMangoldt d := by
    -- By separating the sums, we can focus on the terms where $d$ is in the range $(m+1, 2m+1]$.
    have h_separate_sums : ∑ d ∈ Finset.Icc 1 (2 * m + 1), vonMangoldt d * (⌊(2 * m + 1 : ℝ) / (d : ℝ)⌋ - ⌊(m : ℝ) / (d : ℝ)⌋ - ⌊((m + 1) : ℝ) / (d : ℝ)⌋) ≥ ∑ d ∈ Finset.Ioc (m + 1) (2 * m + 1), vonMangoldt d := by
      have h_separate_sums : ∀ d ∈ Finset.Icc 1 (2 * m + 1), vonMangoldt d * (⌊(2 * m + 1 : ℝ) / (d : ℝ)⌋ - ⌊(m : ℝ) / (d : ℝ)⌋ - ⌊((m + 1) : ℝ) / (d : ℝ)⌋) ≥ if d ∈ Finset.Ioc (m + 1) (2 * m + 1) then vonMangoldt d else 0 := by
        intro d hd; split_ifs <;> simp_all +decide [ Nat.cast_add, Nat.cast_mul, Nat.cast_one, div_eq_mul_inv ] ;
        · -- Since $d > m + 1$, we have $\lfloor (2m + 1) / d \rfloor = 1$, $\lfloor m / d \rfloor = 0$, and $\lfloor (m + 1) / d \rfloor = 0$.
          have h_floor : ⌊(2 * m + 1 : ℝ) / d⌋ = 1 ∧ ⌊(m : ℝ) / d⌋ = 0 ∧ ⌊((m + 1) : ℝ) / d⌋ = 0 := by
            norm_num [ Int.floor_eq_iff ];
            exact ⟨ ⟨ by rw [ le_div_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith, by rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith ⟩, ⟨ by positivity, by rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith ⟩, by positivity, by rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith ⟩;
          simp_all +decide [ div_eq_mul_inv ];
          norm_num [ show ⌊ ( m : ℝ ) * ( d : ℝ ) ⁻¹⌋ = 0 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩, show ⌊ ( m + 1 : ℝ ) * ( d : ℝ ) ⁻¹⌋ = 0 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ];
        · refine mul_nonneg ( ?_ ) ( ?_ );
          · exact vonMangoldt_nonneg;
          · norm_num [ add_mul, mul_add ];
            norm_cast;
            exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.floor_le ( ( 2 * m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( ( 2 * m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.floor_le ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ ) ] );
      refine' le_trans _ ( Finset.sum_le_sum h_separate_sums );
      simp +decide [ Finset.sum_ite ];
      refine' le_of_eq _;
      refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +arith +decide;
      lia;
    convert h_separate_sums using 1 ; norm_num [ mul_sub, Finset.sum_sub_distrib ];
    congr! 1;
    · norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
      rw [ ← Finset.sum_subset ( Finset.Ioc_subset_Ioc_right ( by linarith : m ≤ 2 * m ) ) ] <;> norm_num;
      · exact Or.inr ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> linarith ⟩;
      · exact fun x hx₁ hx₂ hx₃ => Or.inr ⟨ by positivity, by rw [ div_lt_one ( by positivity ) ] ; exact_mod_cast hx₃ hx₁ ⟩;
    · refine' Finset.sum_subset _ _ <;> intro d hd <;> norm_num at *;
      · grind;
      · exact fun h => Or.inr ⟨ by positivity, by rw [ div_lt_one ( by norm_cast; linarith ) ] ; exact_mod_cast by linarith [ h hd.1 ] ⟩;
  simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
  convert add_le_add_right h_apply_log_factorial ( chebyshevPsi ( m + 1 ) ) using 1;
  · unfold chebyshevPsi; rw [ ← Finset.sum_union ] <;> norm_num [ Finset.disjoint_right ] ;
    · rcongr x ; norm_num ; omega;
    · grind;
  · ring

private theorem chebyshevPsi_odd_step (m : ℕ) :
    chebyshevPsi (2 * m + 1) - chebyshevPsi (m + 1) ≤ 2 * ↑m * Real.log 2 := by
  -- From the problem statement, we have the inequality $\psi(2m+1) - \psi(m+1) \leq \log \binom{2m+1}{m}$.
  have h1 : (chebyshevPsi (2 * m + 1) - chebyshevPsi (m + 1)) ≤ Real.log (Nat.choose (2 * m + 1) m) := by
    exact psi_odd_le_log_choose m
  have h2 : Nat.choose (2 * m + 1) m ≤ 2 ^ (2 * m) := by
    exact choose_succ_le_two_pow (2 * m) m
  exact h1.trans ( by simpa using Real.log_le_log ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) <| Nat.cast_le.mpr h2 )

/-
**Target for Aristotle**: ψ(n) ≤ 2n · log 2 for all n.
-/
theorem chebyshevPsi_upper_bound (n : ℕ) :
    chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn_even : Even n;
  · obtain ⟨ k, rfl ⟩ := hn_even;
    by_cases hk : k = 0;
    · unfold chebyshevPsi; norm_num [ hk ];
    · have := chebyshevPsi_doubling_le k ( Nat.pos_of_ne_zero hk );
      rw [ two_mul ] at this; specialize ih k ( by linarith [ Nat.pos_of_ne_zero hk ] ) ; push_cast at *; linarith;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide;
    -- By the properties of the Chebyshev function, we have:
    have h_step : chebyshevPsi (2 * k + 1) ≤ chebyshevPsi (k + 1) + 2 * k * Real.log 2 := by
      have := chebyshevPsi_odd_step k;
      linarith;
    rcases k with ( _ | k ) <;> norm_num at *;
    · unfold chebyshevPsi; norm_num [ Finset.sum_range_succ ];
      positivity;
    · exact h_step.trans ( by have := ih ( k + 1 + 1 ) ( by linarith ) ; norm_num at * ; nlinarith [ Real.log_nonneg one_le_two ] )

end ChebyshevBoundsOQ04Aristotle