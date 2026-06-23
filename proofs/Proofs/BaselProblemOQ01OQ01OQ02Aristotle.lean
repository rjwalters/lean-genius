/-
  Aristotle targets for BaselProblemOQ01OQ01OQ02 (Apéry's ζ(3) irrationality scaffold)
  See BaselProblemOQ01OQ01OQ02.lean for the main formalization.

  Status (2026-04-21): All previous targets are now proved in the main file.
  The 5 remaining axioms in the main file are blocked for automated proof search:
  1. aperyB_recurrence — requires Zeilberger's WZ-theory
  2. denominator_control — requires explicit a-sequence formula
  3. lcm_hanson_bound — requires Chebyshev theta bound (PNT, not in Mathlib)
  4. apery_linearForm_decay — requires integral representation of Lₙ
  5. apery_linearForm_nonzero — requires integral representation of Lₙ

  Potentially useful target for Aristotle:
  - nair_lcm_bound: lcm(1,...,n) ≤ 4^n (Nair 1982, uses central binomial via ballot integral)
    This is weaker than the Hanson bound (≤ 3^n) but might be reachable if
    Mathlib has central binomial coefficient divisibility lemmas.

  Previously proved in companion file but now in main file:
  - aperyB_pos ✓ (main file, line ~101)
  - lcmUpTo_pos ✓ (main file, line ~348)
-/
import Mathlib

open BigOperators Finset Nat

namespace AperyZetaThreeAristotle

/-- lcm(1, 2, ..., n). -/
def lcmUpTo (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

/- ## Helper lemmas for the Nair bound -/

/-- C(2n, n) ≤ 4^n: the central binomial coefficient is at most 4^n.
    Proof: C(2n, n) ≤ Σ_{k=0}^{2n} C(2n, k) = 2^(2n) = 4^n. -/
lemma centralBinom_le_four_pow (n : ℕ) : Nat.centralBinom n ≤ 4 ^ n := by
  unfold Nat.centralBinom
  calc (2 * n).choose n
      ≤ ∑ m ∈ Finset.range (2 * n + 1), (2 * n).choose m := by
        apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
        simp [Finset.mem_range]; omega
    _ = 2 ^ (2 * n) := Nat.sum_range_choose (2 * n)
    _ = 4 ^ n := by rw [pow_mul]; norm_num

/-
C(2m+1, m) ≤ 4^m.
    Proof: 2 * C(2m+1, m) ≤ 2^(2m+1), so C(2m+1, m) ≤ 2^(2m) = 4^m.
-/
lemma choose_two_mul_add_one_le (m : ℕ) : (2 * m + 1).choose m ≤ 4 ^ m := by
  exact?

/-
lcm(1,...,2m) divides lcm(1,...,m) * C(2m, m).
    Key structural lemma: for each prime p,
    v_p(lcm(1,...,2m)) ≤ v_p(lcm(1,...,m)) + v_p(C(2m, m)).
-/
lemma lcmUpTo_even_dvd (m : ℕ) :
    lcmUpTo (2 * m) ∣ lcmUpTo m * (2 * m).choose m := by
  -- To prove the divisibility, it suffices to show that for any prime $p$, the $p$-adic valuation of $lcmUpTo (2m)$ is less than or equal to the $p$-adic valuation of $lcmUpTo m$ multiplied by the binomial coefficient $(2m choose m)$.
  suffices h_val : ∀ p : ℕ, Nat.Prime p → (Nat.factorization (lcmUpTo (2 * m))) p ≤ (Nat.factorization (lcmUpTo m)) p + (Nat.factorization (Nat.choose (2 * m) m)) p by
    rw [ ← Nat.factorization_le_iff_dvd ];
    · rw [ Nat.factorization_mul ];
      · exact fun p => if hp : Nat.Prime p then h_val p hp else by aesop;
      · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
      · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    · exact mul_ne_zero ( Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) <| Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
  -- Let $p$ be any prime number. We need to show that $v_p(lcm(1, ..., 2m)) \leq v_p(lcm(1, ..., m)) + v_p(C(2m, m))$.
  intro p hp
  have h_val_prime : ∀ n : ℕ, Nat.factorization (lcmUpTo n) p = Nat.log p n := by
    -- By definition of lcmUpTo, we know that the p-adic valuation of lcmUpTo n is equal to the maximum of the p-adic valuations of the numbers from 1 to n.
    have h_lcmUpTo_val : ∀ n : ℕ, Nat.factorization (lcmUpTo n) p = Finset.sup (Finset.range n) (fun k => Nat.factorization (k + 1) p) := by
      intro n
      unfold lcmUpTo;
      induction' n with n ih <;> simp_all +decide [ Finset.range_add_one ];
      erw [ Nat.factorization_lcm ] <;> simp_all +decide [ GCDMonoid.lcm ];
    intro n; rw [ h_lcmUpTo_val ] ; rcases n.eq_zero_or_pos with hn | hn <;> simp_all +decide [ Finset.sup_le_iff ] ;
    refine' le_antisymm _ _ <;> norm_num [ Finset.sup_le_iff ];
    · exact fun k hk => Nat.le_log_of_pow_le hp.one_lt <| Nat.le_trans ( Nat.le_of_dvd ( Nat.succ_pos _ ) <| Nat.ordProj_dvd _ _ ) <| by linarith;
    · refine' le_trans _ ( Finset.le_sup <| Finset.mem_range.mpr <| show p ^ log p n - 1 < n from _ );
      · rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ hp.pos ) ] ; aesop;
      · exact lt_of_lt_of_le ( Nat.sub_lt ( pow_pos hp.pos _ ) zero_lt_one ) ( Nat.pow_log_le_self p hn.ne' );
  have h_val_prime : ∀ n : ℕ, Nat.factorization (Nat.choose (2 * n) n) p ≥ Nat.log p (2 * n) - Nat.log p n := by
    intro n
    have h_kummer_step : ∀ i : ℕ, i ≤ Nat.log p (2 * n) → (Nat.floor ((2 * n) / p ^ i) - 2 * Nat.floor (n / p ^ i)) ≥ if i ≤ Nat.log p (2 * n) ∧ i > Nat.log p n then 1 else 0 := by
      intro i hi; split_ifs <;> simp_all +decide [ Nat.two_mul, Nat.add_div ] ;
      rw [ Nat.le_sub_iff_add_le ];
      · rw [ Nat.le_log_iff_pow_le hp.one_lt ] at *;
        · rw [ Nat.log_lt_iff_lt_pow hp.one_lt ] at *;
          · rw [ Nat.div_eq_of_lt ] <;> norm_num;
            · exact Nat.div_pos hi ( pow_pos hp.pos _ );
            · linarith;
          · aesop;
        · aesop;
      · rw [ Nat.le_div_iff_mul_le ( pow_pos hp.pos _ ) ] ; linarith [ Nat.div_mul_le_self n ( p ^ i ) ];
    have h_kummer_sum : Nat.factorization (Nat.choose (2 * n) n) p = ∑ i ∈ Finset.Icc 1 (Nat.log p (2 * n)), (Nat.floor ((2 * n) / p ^ i) - 2 * Nat.floor (n / p ^ i)) := by
      haveI := Fact.mk hp; rw [ Nat.factorization_def ];
      · rw [ padicValNat_choose ];
        any_goals exact Nat.lt_succ_self _;
        · norm_num [ two_mul, Nat.add_div ( pow_pos hp.pos _ ) ];
          rfl;
        · grind;
      · exact hp;
    have h_kummer_sum_ge : ∑ i ∈ Finset.Icc 1 (Nat.log p (2 * n)), (if i ≤ Nat.log p (2 * n) ∧ i > Nat.log p n then 1 else 0) ≥ Nat.log p (2 * n) - Nat.log p n := by
      simp +zetaDelta at *;
      rw [ show { x ∈ Finset.Icc 1 ( log p ( 2 * n ) ) | x ≤ log p ( 2 * n ) ∧ log p n < x } = Finset.Icc ( log p n + 1 ) ( log p ( 2 * n ) ) from ?_ ] ; simp +arith +decide [ Nat.card_Icc ] ; omega;
      ext; simp [Finset.inter_filter, Finset.mem_Icc];
      exact ⟨ fun h => ⟨ h.2.2, h.1.2 ⟩, fun h => ⟨ ⟨ Nat.pos_of_ne_zero ( by aesop ), h.2 ⟩, h.2, h.1 ⟩ ⟩;
    exact h_kummer_sum.symm ▸ h_kummer_sum_ge.trans ( Finset.sum_le_sum fun i hi => h_kummer_step i <| Finset.mem_Icc.mp hi |>.2 );
  grind +qlia

/-
lcm(1,...,2m+1) divides lcm(1,...,m+1) * C(2m+1, m).
    Key structural lemma: for each prime p,
    v_p(lcm(1,...,2m+1)) ≤ v_p(lcm(1,...,m+1)) + v_p(C(2m+1, m)).
-/
lemma lcmUpTo_odd_dvd (m : ℕ) :
    lcmUpTo (2 * m + 1) ∣ lcmUpTo (m + 1) * (2 * m + 1).choose m := by
  -- For each prime $p$, we need to show that $v_p(lcm(1,...,2m+1)) \leq v_p(lcm(1,...,m+1)) + v_p(C(2m+1, m))$.
  have h_prime_div : ∀ p, Nat.Prime p → Nat.factorization (lcmUpTo (2 * m + 1)) p ≤ Nat.factorization (lcmUpTo (m + 1)) p + Nat.factorization ((2 * m + 1).choose m) p := by
    -- For each prime $p$, $v_p(lcm(1, ..., 2m+1))$ is equal to the maximum power of $p$ dividing any number in the range $1$ to $2m+1$.
    intro p hp
    have h_max_power : (lcmUpTo (2 * m + 1)).factorization p = (Finset.range (2 * m + 1)).sup (fun j => (j + 1).factorization p) := by
      unfold lcmUpTo;
      induction' ( 2 * m + 1 ) with m ih <;> simp_all +decide [ Finset.range_add_one ];
      erw [ Nat.factorization_lcm ] <;> simp_all +decide [ GCDMonoid.lcm ];
    -- Similarly, $v_p(lcm(1, ..., m+1))$ is equal to the maximum power of $p$ dividing any number in the range $1$ to $m+1$.
    have h_max_power_m1 : (lcmUpTo (m + 1)).factorization p = (Finset.range (m + 1)).sup (fun j => (j + 1).factorization p) := by
      unfold lcmUpTo;
      induction' ( m + 1 ) with m ih <;> simp_all +decide [ Nat.factorization_lcm, Finset.range_add_one ];
      erw [ Nat.factorization_lcm ] <;> simp_all +decide [ GCDMonoid.lcm ];
    -- Let $k$ be such that $p^k \leq 2m+1 < p^{k+1}$.
    obtain ⟨k, hk⟩ : ∃ k, p^k ≤ 2 * m + 1 ∧ 2 * m + 1 < p^(k + 1) := by
      exact ⟨ Nat.log p ( 2 * m + 1 ), Nat.pow_le_of_le_log ( by linarith ) ( by linarith ), Nat.lt_pow_of_log_lt hp.one_lt ( by linarith ) ⟩;
    -- If $p^k \leq m+1$, then $v_p(lcm(1, ..., m+1)) \geq k$.
    by_cases h_case : p^k ≤ m + 1;
    · -- If $p^k \leq m+1$, then $v_p(lcm(1, ..., m+1)) \geq k$, so we are done.
      have h_case1 : (Finset.range (2 * m + 1)).sup (fun j => (j + 1).factorization p) ≤ k := by
        simp +zetaDelta at *;
        intro b hb; contrapose! hk;
        exact fun _ => Nat.le_trans ( Nat.pow_le_pow_right hp.pos ( Nat.succ_le_of_lt hk ) ) ( Nat.le_trans ( Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.ordProj_dvd _ _ ) ) ( by linarith ) );
      have h_case1 : (Finset.range (m + 1)).sup (fun j => (j + 1).factorization p) ≥ k := by
        refine' le_trans _ ( Finset.le_sup <| Finset.mem_range.mpr <| show p ^ k - 1 < m + 1 from _ );
        · rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ hp.pos ), Nat.factorization_pow ] ; aesop;
        · exact lt_of_lt_of_le ( Nat.sub_lt ( pow_pos hp.pos _ ) zero_lt_one ) h_case;
      grind;
    · -- If $p^k > m+1$, then $v_p(C(2m+1, m)) \geq 1$.
      have h_case2 : Nat.factorization ((2 * m + 1).choose m) p ≥ 1 := by
        rw [ Nat.factorization_def ];
        · haveI := Fact.mk hp; rw [ padicValNat_choose ];
          any_goals exact Nat.lt_succ_self _;
          · refine' Finset.card_pos.mpr ⟨ k, _ ⟩ ; simp_all +decide [ Nat.log_eq_iff ];
            exact ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_log_of_pow_le hp.one_lt hk.1 ⟩, by rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega ⟩;
          · linarith;
        · assumption;
      -- Since $p^k > m+1$, we have $v_p(lcm(1, ..., 2m+1)) \leq k$.
      have h_case2_le_k : (Finset.range (2 * m + 1)).sup (fun j => (j + 1).factorization p) ≤ k := by
        simp +zetaDelta at *;
        intro b hb; contrapose! hk;
        exact fun _ => Nat.le_trans ( pow_le_pow_right₀ hp.one_lt.le ( Nat.succ_le_of_lt hk ) ) ( Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.ordProj_dvd _ _ ) ) |> le_trans <| by linarith;
      -- Since $p^k > m+1$, we have $v_p(lcm(1, ..., m+1)) \geq k-1$.
      have h_case2_ge_k_minus_1 : (Finset.range (m + 1)).sup (fun j => (j + 1).factorization p) ≥ k - 1 := by
        rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
        refine' le_trans _ ( Finset.le_sup <| Finset.mem_range.mpr <| show p ^ k - 1 < m + 1 from _ );
        · rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ hp.pos ), Nat.factorization_pow ] ; aesop;
        · rw [ tsub_lt_iff_left ] <;> nlinarith only [ hk.1, h_case, hp.two_le ];
      omega;
  rw [ ← Nat.factorization_le_iff_dvd ];
  · rw [ Nat.factorization_mul ];
    · exact fun p => if hp : Nat.Prime p then h_prime_div p hp else by aesop;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
  · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
  · exact mul_ne_zero ( Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) <| Nat.ne_of_gt <| Nat.choose_pos <| by linarith;

/-
Auxiliary: lcmUpTo is positive
-/
lemma lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

/-
**Nair's bound (1982)**: lcm(1, 2, ..., n) ≤ 4^n.
-/
theorem nair_lcm_bound (n : ℕ) : lcmUpTo n ≤ 4 ^ n := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases Nat.even_or_odd' n with ⟨ m, rfl | rfl ⟩;
  · -- By the lemma lcmUpTo_even_dvd, we have lcmUpTo (2 * m) ∣ lcmUpTo m * Nat.choose (2 * m) m.
    have h_div : lcmUpTo (2 * m) ∣ lcmUpTo m * Nat.choose (2 * m) m := by
      exact?;
    -- By the lemma centralBinom_le_four_pow, we have Nat.choose (2 * m) m ≤ 4 ^ m.
    have h_choose : Nat.choose (2 * m) m ≤ 4 ^ m := by
      convert centralBinom_le_four_pow m using 1;
    rcases m with ( _ | m ) <;> simp_all +decide [ pow_mul' ];
    exact le_trans ( Nat.le_of_dvd ( Nat.mul_pos ( lcmUpTo_pos _ ) ( Nat.choose_pos ( by linarith ) ) ) h_div ) ( by rw [ sq ] ; exact Nat.mul_le_mul ( ih _ ( by linarith ) ) h_choose );
  · -- Using the lemma lcmUpTo_odd_dvd, we have lcmUpTo (2 * m + 1) ∣ lcmUpTo (m + 1) * (2 * m + 1).choose m.
    have h_div : lcmUpTo (2 * m + 1) ∣ lcmUpTo (m + 1) * (2 * m + 1).choose m := by
      exact?;
    refine' le_trans ( Nat.le_of_dvd _ h_div ) _;
    · exact mul_pos ( lcmUpTo_pos _ ) ( Nat.choose_pos ( by linarith ) );
    · rcases m with ( _ | m ) <;> simp_all +decide [ Nat.pow_succ', Nat.pow_mul' ];
      refine' le_trans ( Nat.mul_le_mul ( ih _ _ ) ( show Nat.choose ( 2 * ( m + 1 ) + 1 ) ( m + 1 ) ≤ 4 ^ ( m + 1 ) from _ ) ) _ <;> ring <;> norm_num [ pow_succ' ];
      · linarith;
      · convert choose_two_mul_add_one_le ( m + 1 ) using 1 ; ring

end AperyZetaThreeAristotle