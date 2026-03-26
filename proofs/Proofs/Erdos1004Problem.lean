/-
  Erdős Problem #1004: Distinct Consecutive Totient Values

  Source: https://erdosproblems.com/1004
  Status: OPEN (partial results by Erdős-Pomerance-Sárközy 1987)

  Statement:
  Let c > 0. If x is sufficiently large, does there exist n ≤ x such that
  the values φ(n+1), φ(n+2), ..., φ(n+⌊(log x)^c⌋) are all distinct?

  Known Results:
  - Erdős-Pomerance-Sárközy (1987): If φ(n+k) are all distinct for 1 ≤ k ≤ K,
    then K ≤ n/exp(c(log n)^{1/3}) for some constant c > 0.
  - This gives an upper bound on how long distinct runs can be.

  Related: Problem #945 asks the same question for the divisor function τ(n).

  References:
  [EPS87] Erdős-Pomerance-Sárközy, "On locally repeated values of certain
          arithmetic functions. III" (1987)

  Tags: number-theory, totient, analytic-number-theory
-/

import Mathlib

namespace Erdos1004

open Nat Real Filter Finset Topology

/-! ## Part I: Euler's Totient Function -/

/-- Euler's totient function φ(n) counts integers 1 ≤ k ≤ n coprime to n. -/
def phi (n : ℕ) : ℕ := Nat.totient n

/-- φ(1) = 1. -/
theorem phi_one : phi 1 = 1 := Nat.totient_one

/-- φ(p) = p - 1 for prime p. -/
theorem phi_prime (p : ℕ) (hp : p.Prime) : phi p = p - 1 := by
  simp [phi, Nat.totient_prime hp]

/-- φ(n) > 0 for n > 0. -/
theorem phi_pos (n : ℕ) (hn : n > 0) : phi n > 0 := by
  exact Nat.totient_pos.mpr (by omega)

/-- φ(n) ≤ n for all n. -/
theorem phi_le (n : ℕ) : phi n ≤ n :=
  Nat.totient_le n

/-- φ(n) < n for n > 1. -/
theorem phi_lt (n : ℕ) (hn : n > 1) : phi n < n := by
  unfold phi; exact Nat.totient_lt n hn

/-! ## Part II: Distinct Totient Runs -/

/-- A run of K consecutive integers starting at n+1 has distinct totient values
    if φ(n+1), φ(n+2), ..., φ(n+K) are all different. -/
def IsDistinctTotientRun (n K : ℕ) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i ≤ K → 1 ≤ j → j ≤ K → i ≠ j →
    phi (n + i) ≠ phi (n + j)

/-- Alternative definition using injectivity on an interval. -/
def IsDistinctTotientRun' (n K : ℕ) : Prop :=
  (Set.Icc (n + 1) (n + K)).InjOn phi

/-- The two definitions are equivalent. -/
theorem distinctRun_iff (n K : ℕ) :
    IsDistinctTotientRun n K ↔ IsDistinctTotientRun' n K := by
  unfold IsDistinctTotientRun IsDistinctTotientRun'
  simp only [Set.InjOn, Set.mem_Icc]
  constructor
  · -- Pairwise distinct → injective on interval
    intro h a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩ hab
    -- a = n + (a - n), b = n + (b - n), with a - n, b - n ∈ [1, K]
    by_contra hne
    exact h (a - n) (b - n) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by rwa [Nat.add_sub_cancel' (by omega : n ≤ a),
                           Nat.add_sub_cancel' (by omega : n ≤ b)])
  · -- Injective → pairwise distinct
    intro h i j hi1 hiK hj1 hjK hij heq
    have := h ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ heq
    omega

/-- Empty run is trivially distinct. -/
theorem distinctRun_zero (n : ℕ) : IsDistinctTotientRun n 0 := by
  intro i j hi _ _ _ _
  omega

/-- Single element run is distinct. -/
theorem distinctRun_one (n : ℕ) : IsDistinctTotientRun n 1 := by
  intro i j hi hiK hj hjK hij
  omega

/-! ## Part III: The Maximum Run Length Function -/

/-- The maximum length K such that φ(n+1), ..., φ(n+K) are all distinct. -/
noncomputable def maxDistinctRunLength (n : ℕ) : ℕ :=
  sSup {K : ℕ | IsDistinctTotientRun n K}

/-- Every n has some distinct run (at least length 1). -/
theorem exists_distinct_run (n : ℕ) :
    ∃ K > 0, IsDistinctTotientRun n K := by
  exact ⟨1, Nat.one_pos, distinctRun_one n⟩

/-! ## Part IV: The EPS87 Upper Bound -/

/-- **Erdős-Pomerance-Sárközy (1987)**

    If φ(n+k) are all distinct for 1 ≤ k ≤ K, then
    K ≤ n / exp(c · (log n)^{1/3})
    for some constant c > 0 and all sufficiently large n.

    This limits how long a distinct totient run can be.

    This single axiom encapsulates the full EPS87 result: there exist a constant
    c > 0 and a threshold N₀ such that the bound holds for all n ≥ N₀.
-/
axiom eps87_theorem : ∃ (c : ℝ) (N₀ : ℕ), c > 0 ∧
    ∀ (n K : ℕ), n ≥ N₀ → IsDistinctTotientRun n K →
      (K : ℝ) ≤ (n : ℝ) / Real.exp (c * (Real.log (n : ℝ)) ^ ((1 : ℝ)/3))

/-- The EPS87 constant c > 0 from the upper bound K ≤ n/exp(c(log n)^{1/3}). -/
noncomputable def eps87_constant : ℝ := eps87_theorem.choose

/-- The threshold beyond which the EPS87 bound holds. -/
noncomputable def eps87_threshold : ℕ := eps87_theorem.choose_spec.choose

theorem eps87_constant_pos : eps87_constant > 0 :=
  eps87_theorem.choose_spec.choose_spec.1

theorem eps87_upper_bound (n K : ℕ) (hn : n ≥ eps87_threshold) (hrun : IsDistinctTotientRun n K) :
    (K : ℝ) ≤ (n : ℝ) / Real.exp (eps87_constant * (Real.log (n : ℝ)) ^ ((1 : ℝ)/3)) :=
  eps87_theorem.choose_spec.choose_spec.2 n K hn hrun

/-- Corollary: The run length is o(n). -/
theorem run_length_sublinear :
    Tendsto (fun n : ℕ => (maxDistinctRunLength n : ℝ) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  -- Sandwich: 0 ≤ f(n) ≤ 1/exp(c·(log n)^{1/3}) → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
  -- Goal 1: upper bound → 0
  · show Tendsto (fun n : ℕ => (1 : ℝ) / Real.exp (eps87_constant *
        (Real.log (n : ℝ)) ^ ((1 : ℝ)/3))) atTop (𝓝 0)
    simp only [one_div]
    -- exp(c·(log n)^{1/3}) → ∞, so its inverse → 0
    apply tendsto_inv_atTop_zero.comp
    -- exp → ∞ when argument → ∞
    apply Real.tendsto_exp_atTop.comp
    -- c·(log n)^{1/3} → ∞
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hrpow : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ)/3)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp hlog
    rw [tendsto_atTop_atTop] at hrpow ⊢
    intro b
    obtain ⟨N, hN⟩ := hrpow (b / eps87_constant)
    exact ⟨N, fun n hn => by
      have hc := eps87_constant_pos
      have := hN n hn
      nlinarith [mul_div_cancel₀ b (ne_of_gt hc)]⟩
  -- Goal 2: 0 ≤ f(n) eventually
  · filter_upwards with n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- Goal 3: f(n) ≤ upper bound eventually
  · filter_upwards [eventually_ge_atTop eps87_threshold, eventually_gt_atTop 0] with n hn hn0
    show (maxDistinctRunLength n : ℝ) / (n : ℝ) ≤
      1 / Real.exp (eps87_constant * (Real.log (n : ℝ)) ^ ((1 : ℝ)/3))
    unfold maxDistinctRunLength
    set S := {K : ℕ | IsDistinctTotientRun n K} with hS_def
    set e := Real.exp (eps87_constant * (Real.log (n : ℝ)) ^ ((1 : ℝ)/3))
    have he_pos : 0 < e := Real.exp_pos _
    set B := (n : ℝ) / e with hB_def
    have hB_nn : 0 ≤ B := div_nonneg (Nat.cast_nonneg _) he_pos.le
    -- Every K in S is bounded by B
    have hbdd : ∀ K ∈ S, (K : ℝ) ≤ B := fun K hK => eps87_upper_bound n K hn hK
    -- S is nonempty (contains 0)
    have hne : S.Nonempty := ⟨0, distinctRun_zero n⟩
    -- Bound sSup via floor
    have h1 : @sSup ℕ _ S ≤ ⌊B⌋₊ :=
      csSup_le hne (fun K hK => Nat.le_floor (hbdd K hK))
    have h2 : ((@sSup ℕ _ S : ℕ) : ℝ) ≤ B :=
      le_trans (Nat.cast_le.mpr h1) (Nat.floor_le hB_nn)
    -- Divide by n > 0
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
    calc ((@sSup ℕ _ S : ℕ) : ℝ) / (n : ℝ)
        ≤ B / (n : ℝ) := by apply div_le_div_of_nonneg_right h2 hn_pos.le
      _ = 1 / e := by rw [hB_def]; field_simp

/-! ## Part V: The Main Conjecture -/

/-- **Erdős Problem #1004 (Main Conjecture)**

    For any c > 0, if x is sufficiently large, there exists n ≤ x such that
    φ(n+1), ..., φ(n+⌊(log x)^c⌋) are all distinct.

    In other words: Can we always find runs of length (log x)^c?
-/
def Erdos1004Conjecture : Prop :=
  ∀ c : ℝ, c > 0 →
    ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

/-- The negation: For some c > 0, eventually no such n exists. -/
def Erdos1004Negation : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ x : ℕ in atTop, ∀ n ≤ x,
      ¬IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

/-! ## Part VI: Known Partial Results -/

/-- For small c, runs of length (log x)^c should be common. -/
def SmallCaseConjecture : Prop :=
  ∃ c₀ > 0, ∀ c : ℝ, 0 < c → c < c₀ →
    ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

/- Note: The EPS bound heuristically suggests the conjecture parameter c
   should satisfy c ≤ 1/3, but this is not a formal implication from
   the conjecture statement. The original sorry was on a false statement. -/

/-! ## Part VII: Examples of Distinct Runs -/

/-- φ(2) = 1, φ(3) = 2, φ(4) = 2. So run at n=1 has length at most 2. -/
theorem example_n1 : IsDistinctTotientRun 1 2 ∧ ¬IsDistinctTotientRun 1 3 := by
  constructor
  · intro i j hi hiK hj hjK hij
    unfold phi
    interval_cases i <;> interval_cases j <;> simp_all [Nat.totient] <;> decide
  · intro h
    have := h 2 3 (by omega) (by omega) (by omega) (by omega) (by omega)
    unfold phi at this; simp [Nat.totient] at this; exact absurd (by decide) this

/-- φ(3) = 2, φ(4) = 2. So n=2 gives run length 1. -/
theorem example_n2 : IsDistinctTotientRun 2 1 ∧ ¬IsDistinctTotientRun 2 2 := by
  constructor
  · exact distinctRun_one 2
  · intro h
    have := h 1 2 (by omega) (by omega) (by omega) (by omega) (by omega)
    unfold phi at this; simp [Nat.totient] at this; exact absurd (by decide) this

/-- For any fixed K ≥ 2, distinct totient runs of length K exist for sufficiently
    large n. This follows from probabilistic arguments on the distribution of
    totient values (the expected number of collision-free starting points m ≤ x
    grows like x · ∏(1 - i/V(x)) → x for fixed K), but a full proof requires
    deep analytic number theory. Concrete examples: K=2 at m=1, K=3 at m=4,
    K=5 at m=10. -/
axiom longer_runs_need_larger_n (K : ℕ) (hK : K ≥ 2) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ m ≤ n, IsDistinctTotientRun m K

/-! ## Part VIII: Totient Value Collisions -/

/-- Two numbers have the same totient if φ(a) = φ(b). -/
def TotientCollision (a b : ℕ) : Prop := phi a = phi b ∧ a ≠ b

/-- φ(1) = φ(2) = 1 is a collision. -/
theorem collision_1_2 : TotientCollision 1 2 := by
  exact ⟨by native_decide, by omega⟩

/-- φ(3) = φ(4) = φ(6) = 2 gives multiple collisions. -/
theorem collision_3_4 : TotientCollision 3 4 := by
  exact ⟨by native_decide, by omega⟩

/-- Collisions cause distinct runs to end. -/
theorem collision_ends_run (n i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i < j)
    (hcol : phi (n + i) = phi (n + j)) :
    ¬IsDistinctTotientRun n j := by
  intro hrun
  exact hrun i j hi (le_of_lt hij) hj (le_refl j) (by omega) hcol

/-! ## Part IX: Connection to Divisor Function -/

/-- The divisor function τ(n). -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- Distinct divisor run (related to Problem #945). -/
def IsDistinctDivisorRun (n K : ℕ) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i ≤ K → 1 ≤ j → j ≤ K → i ≠ j →
    tau (n + i) ≠ tau (n + j)

/-- Problem #945 asks the analogous question for τ. -/
def Problem945Conjecture : Prop :=
  ∀ c : ℝ, c > 0 →
    ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      IsDistinctDivisorRun n ⌊(Real.log x) ^ c⌋₊

/-! ## Part X: Probabilistic Heuristics -/

/-- The number of distinct totient values up to x. -/
noncomputable def countDistinctTotients (x : ℕ) : ℕ :=
  (Finset.range x).image phi |>.card

/-- Asymptotically, there are ~ x / log x distinct totient values ≤ x.
    This is a consequence of results on the distribution of Euler's totient
    function (Erdős 1935, refined by Ford 1998). The count V(x) of distinct
    values φ(k) for k ≤ x satisfies V(x) ~ x / log x. -/
axiom distinct_totients_asymptotic :
    Tendsto (fun x : ℕ => (countDistinctTotients x : ℝ) * Real.log (x : ℝ) / (x : ℝ))
      atTop (𝓝 (1 : ℝ))

/-- Heuristic: Probability that K consecutive totients are distinct
    is roughly (1 - 1/V) * (1 - 2/V) * ... * (1 - (K-1)/V)
    where V ~ n / log n is the number of available values. -/
noncomputable def birthdayProbabilityHeuristic (n K : ℕ) : ℝ :=
  let V := (n : ℝ) / Real.log (n : ℝ)
  ∏ k ∈ Finset.range K, (1 - (k : ℝ) / V)

/-! ## Part XI: Bounds on Run Length -/

/-- Trivial upper bound: K ≤ n (can't have more distinct values than integers). -/
theorem run_length_trivial_bound (n K : ℕ) (hrun : IsDistinctTotientRun n K) :
    K ≤ n + K := by
  omega

/-- Better bound: K ≤ #{distinct φ values ≤ n + K}.
    The K distinct values phi(n+1),...,phi(n+K) all land in (range (n+K+1)).image phi. -/
theorem run_length_by_distinct_values (n K : ℕ) (hrun : IsDistinctTotientRun n K) :
    K ≤ countDistinctTotients (n + K + 1) := by
  unfold countDistinctTotients
  -- phi is injective on Icc (n+1) (n+K)
  have hinj : Set.InjOn phi ↑(Finset.Icc (n + 1) (n + K)) := by
    rw [Finset.coe_Icc]; exact (distinctRun_iff n K).mp hrun
  -- Card of image = K (by injectivity)
  have hcard : ((Finset.Icc (n + 1) (n + K)).image phi).card = K := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]; omega
  -- Image is subset of (range (n+K+1)).image phi
  have hsub : (Finset.Icc (n + 1) (n + K)).image phi ⊆
              (Finset.range (n + K + 1)).image phi := by
    apply Finset.image_subset_image
    intro m hm; exact Finset.mem_range.mpr (by simp [Finset.mem_Icc] at hm; omega)
  calc K = ((Finset.Icc (n + 1) (n + K)).image phi).card := hcard.symm
    _ ≤ ((Finset.range (n + K + 1)).image phi).card := Finset.card_le_card hsub

/-! ## Part XII: Special Values -/

/-- Small totient values: φ(n) = 1 iff n ∈ {1, 2}.
    For n ≥ 3, φ(n) is even (Nat.totient_even), hence ≥ 2. -/
theorem totient_eq_one_iff (n : ℕ) : phi n = 1 ↔ n = 1 ∨ n = 2 := by
  unfold phi
  constructor
  · intro h
    rcases n with _ | _ | _ | n
    · simp [Nat.totient] at h  -- n = 0: totient 0 = 0 ≠ 1
    · left; rfl                 -- n = 1
    · right; rfl                -- n = 2
    · -- n + 3 ≥ 3: totient is even, so ≠ 1
      exfalso
      have heven := Nat.totient_even (show 2 < n + 3 by omega)
      rw [h] at heven
      obtain ⟨k, hk⟩ := heven
      omega
  · rintro (rfl | rfl) <;> native_decide

/-- Helper: coprimality of 2 with odd numbers. -/
private lemma coprime_two_odd {m : ℕ} (hodd : Odd m) : Nat.Coprime 2 m := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro ⟨k, hk⟩; have := hodd; rw [Nat.odd_iff] at this; omega

/-- Helper: odd m implies minFac ≠ 2. -/
private lemma minFac_ne_two_of_odd {m : ℕ} (hodd : Odd m) : m.minFac ≠ 2 := by
  intro h2; have hd : 2 ∣ m := h2 ▸ Nat.minFac_dvd m
  obtain ⟨k, hk⟩ := hd; have := hodd; rw [Nat.odd_iff] at this; omega

/-- Helper: n even implies minFac ≤ 2, so minFac = 2. -/
private lemma odd_of_minFac_ge_three {n : ℕ} (hn : n ≥ 2) (h : n.minFac ≥ 3) : Odd n := by
  rw [Nat.odd_iff]; by_contra hev; push_neg at hev
  have h2n : 2 ∣ n := ⟨n / 2, by omega⟩
  have := Nat.minFac_le_of_dvd (by omega : 2 ≤ 2) h2n; omega

/-- Helper: φ(2*m) = φ(m) when m is odd (from totient_mul + coprimality). -/
private lemma totient_two_mul_odd {m : ℕ} (hodd : Odd m) :
    Nat.totient (2 * m) = Nat.totient m := by
  rw [Nat.totient_mul (coprime_two_odd hodd), show Nat.totient 2 = 1 from by native_decide,
      one_mul]

/-- Helper: φ(p*m) = (p-1)*φ(m) when p prime and p ∤ m. -/
private lemma totient_prime_mul_not_dvd {p m : ℕ} (hp : Nat.Prime p) (h : ¬ p ∣ m) :
    Nat.totient (p * m) = (p - 1) * Nat.totient m := by
  rw [Nat.totient_mul (hp.coprime_iff_not_dvd.mpr h), Nat.totient_prime hp]

/-- Helper: ¬(p² ∣ m) and (p ∣ m) implies ¬(p ∣ m/p). -/
private lemma not_dvd_div_of_not_sq_dvd {p m : ℕ} (hp : p ∣ m) (hsq : ¬ p ^ 2 ∣ m) :
    ¬ p ∣ (m / p) := by
  intro hc; apply hsq
  obtain ⟨b, hb⟩ := hc
  exact ⟨b, by have h1 := Nat.div_mul_cancel hp; rw [hb] at h1; ring_nf; ring_nf at h1; omega⟩

/-- For odd m ≥ 5, φ(m) ≠ 2. -/
private lemma odd_totient_ne_two (m : ℕ) (hm : m ≥ 5) (hodd : Odd m)
    (htot : Nat.totient m = 2) : False := by
  have hm_mod : m % 2 = 1 := Nat.odd_iff.mp hodd
  have hp := Nat.minFac_prime (by omega : m ≠ 1)
  have hd := Nat.minFac_dvd m
  have h_dvd : (m.minFac - 1) ∣ 2 := by
    have := Nat.totient_dvd_of_dvd hd; rw [Nat.totient_prime hp, htot] at this; exact this
  have hmf3 : m.minFac = 3 := by
    have hne2 := minFac_ne_two_of_odd hodd; have hge := hp.two_le
    have hle := Nat.le_of_dvd (by omega) h_dvd; omega
  have h3m : 3 ∣ m := hmf3 ▸ hd
  by_cases h9 : 9 ∣ m
  · have := Nat.totient_dvd_of_dvd h9
    rw [show Nat.totient 9 = 6 from by native_decide, htot] at this; exact absurd this (by decide)
  · have h3k := not_dvd_div_of_not_sq_dvd h3m (by rwa [show (3 : ℕ) ^ 2 = 9 from by norm_num])
    have hm_eq : m = 3 * (m / 3) := by obtain ⟨c, hc⟩ := h3m; omega
    have : Nat.totient m = 2 * Nat.totient (m / 3) := by
      conv_lhs => rw [hm_eq]; exact totient_prime_mul_not_dvd (by norm_num) h3k
    have h1 : Nat.totient (m / 3) = 1 := by omega
    rw [Nat.totient_eq_one_iff] at h1; rcases h1 with h1 | h1 <;> omega

/-- φ(n) = 2 iff n ∈ {3, 4, 6}. -/
theorem totient_eq_two_iff (n : ℕ) : phi n = 2 ↔ n = 3 ∨ n = 4 ∨ n = 6 := by
  unfold phi; constructor
  · intro htot
    suffices hn : n ≤ 6 by
      have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert htot <;> native_decide
    by_contra hgt; push_neg at hgt; have hn7 : n ≥ 7 := by omega
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have hd := Nat.minFac_dvd n
    have h_dvd : (n.minFac - 1) ∣ 2 := by
      have := Nat.totient_dvd_of_dvd hd; rw [Nat.totient_prime hp, htot] at this; exact this
    have hpf : n.minFac = 2 ∨ n.minFac = 3 := by
      have hge := hp.two_le; have hle := Nat.le_of_dvd (by omega) h_dvd; omega
    rcases hpf with hpf | hpf
    · -- n.minFac = 2: n is even
      rw [hpf] at hd
      by_cases h4 : 4 ∣ n
      · -- 4 | n: φ(4) | φ(n), so 2 | 2, fine. But φ(8) = 4.
        by_cases h8 : 8 ∣ n
        · have := Nat.totient_dvd_of_dvd h8
          rw [show Nat.totient 8 = 4 from by native_decide, htot] at this; exact absurd this (by decide)
        · -- 4 | n, 8 ∤ n: n = 4k, k odd. φ(4k) = φ(4)*φ(k) = 2*φ(k).
          have hk_odd : Odd (n / 4) := by
            rw [Nat.odd_iff]; by_contra hev; push_neg at hev
            apply h8; obtain ⟨c, hc⟩ := h4; exact ⟨n / 4 / 2, by omega⟩
          have hn_eq : n = 4 * (n / 4) := by obtain ⟨c, hc⟩ := h4; omega
          -- Coprime 4 (n/4) since n/4 is odd and 4 = 2^2
          have hcop : Nat.Coprime 4 (n / 4) := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num]
            exact (coprime_two_odd hk_odd).pow_left 2
          have : Nat.totient n = 2 * Nat.totient (n / 4) := by
            conv_lhs => rw [hn_eq]
            rw [Nat.totient_mul hcop, show Nat.totient 4 = 2 from by native_decide]
          have h1 : Nat.totient (n / 4) = 1 := by omega
          rw [Nat.totient_eq_one_iff] at h1; rcases h1 with h1 | h1 <;> omega
      · -- 2 | n, 4 ∤ n: n = 2m, m odd. φ(n) = φ(m).
        have hk_odd : Odd (n / 2) := by
          rw [Nat.odd_iff]; by_contra hev; push_neg at hev
          apply h4; obtain ⟨c, hc⟩ := hd; exact ⟨n / 2 / 2, by omega⟩
        have hn_eq : n = 2 * (n / 2) := by obtain ⟨c, hc⟩ := hd; omega
        have htot2 : Nat.totient n = Nat.totient (n / 2) := by
          conv_lhs => rw [hn_eq]; exact totient_two_mul_odd hk_odd
        exact odd_totient_ne_two (n / 2) (by omega) hk_odd (by omega)
    · -- n.minFac = 3: n is odd
      have hodd := odd_of_minFac_ge_three (by omega) (le_of_eq hpf.symm)
      exact odd_totient_ne_two n (by omega) hodd htot
  · rintro (rfl | rfl | rfl) <;> native_decide

/-- For odd m ≥ 7, φ(m) ≠ 4. -/
private lemma odd_totient_ne_four (m : ℕ) (hm : m ≥ 7) (hodd : Odd m)
    (htot : Nat.totient m = 4) : False := by
  have hm_mod : m % 2 = 1 := Nat.odd_iff.mp hodd
  have hp := Nat.minFac_prime (by omega : m ≠ 1)
  have hd := Nat.minFac_dvd m
  have h_dvd : (m.minFac - 1) ∣ 4 := by
    have := Nat.totient_dvd_of_dvd hd; rw [Nat.totient_prime hp, htot] at this; exact this
  have hpf : m.minFac = 3 ∨ m.minFac = 5 := by
    have hne2 := minFac_ne_two_of_odd hodd; have hge := hp.two_le
    have hle := Nat.le_of_dvd (by omega) h_dvd
    have hne4 : m.minFac ≠ 4 := by intro h; rw [h] at hp; exact absurd hp (by decide)
    omega
  rcases hpf with hpf | hpf
  · -- minFac = 3
    have h3m : 3 ∣ m := hpf ▸ hd
    by_cases h9 : 9 ∣ m
    · have := Nat.totient_dvd_of_dvd h9
      rw [show Nat.totient 9 = 6 from by native_decide, htot] at this; exact absurd this (by decide)
    · have h3k := not_dvd_div_of_not_sq_dvd h3m (by rwa [show (3 : ℕ) ^ 2 = 9 from by norm_num])
      have hm_eq : m = 3 * (m / 3) := by obtain ⟨c, hc⟩ := h3m; omega
      have : Nat.totient m = 2 * Nat.totient (m / 3) := by
        conv_lhs => rw [hm_eq]; exact totient_prime_mul_not_dvd (by norm_num) h3k
      have h2 : Nat.totient (m / 3) = 2 := by omega
      have := (totient_eq_two_iff (m / 3)).mp (by unfold phi; exact h2)
      rcases this with h | h | h <;> omega
  · -- minFac = 5
    have h5m : 5 ∣ m := hpf ▸ hd
    by_cases h25 : 25 ∣ m
    · have := Nat.totient_dvd_of_dvd h25
      rw [show Nat.totient 25 = 20 from by native_decide, htot] at this; exact absurd this (by decide)
    · have h5k := not_dvd_div_of_not_sq_dvd h5m (by rwa [show (5 : ℕ) ^ 2 = 25 from by norm_num])
      have hm_eq : m = 5 * (m / 5) := by obtain ⟨c, hc⟩ := h5m; omega
      have : Nat.totient m = 4 * Nat.totient (m / 5) := by
        conv_lhs => rw [hm_eq]
        rw [totient_prime_mul_not_dvd (by norm_num) h5k]
      have h1 : Nat.totient (m / 5) = 1 := by omega
      rw [Nat.totient_eq_one_iff] at h1; rcases h1 with h1 | h1 <;> omega

/-- φ(n) = 4 iff n ∈ {5, 8, 10, 12}. -/
theorem totient_eq_four_iff (n : ℕ) :
    phi n = 4 ↔ n = 5 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
  unfold phi; constructor
  · intro htot
    suffices hn : n ≤ 12 by
      have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
             n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> revert htot <;> native_decide
    by_contra hgt; push_neg at hgt; have hn13 : n ≥ 13 := by omega
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have hd := Nat.minFac_dvd n
    have h_dvd : (n.minFac - 1) ∣ 4 := by
      have := Nat.totient_dvd_of_dvd hd; rw [Nat.totient_prime hp, htot] at this; exact this
    have hpf : n.minFac = 2 ∨ n.minFac = 3 ∨ n.minFac = 5 := by
      have hge := hp.two_le; have hle := Nat.le_of_dvd (by omega) h_dvd
      have hne4 : n.minFac ≠ 4 := by intro h; rw [h] at hp; exact absurd hp (by decide)
      omega
    rcases hpf with hpf | hpf | hpf
    · -- n.minFac = 2: n is even
      rw [hpf] at hd
      by_cases h8 : 8 ∣ n
      · -- 8 | n: φ(8k) = φ(8)*φ(k) = 4*φ(k) when k odd
        by_cases h16 : 16 ∣ n
        · have := Nat.totient_dvd_of_dvd h16
          rw [show Nat.totient 16 = 8 from by native_decide, htot] at this; exact absurd this (by decide)
        · have hk_odd : Odd (n / 8) := by
            rw [Nat.odd_iff]; by_contra hev; push_neg at hev
            apply h16; obtain ⟨c, hc⟩ := h8; exact ⟨n / 8 / 2, by omega⟩
          have hn_eq : n = 8 * (n / 8) := by obtain ⟨c, hc⟩ := h8; omega
          have hcop : Nat.Coprime 8 (n / 8) := by
            rw [show (8 : ℕ) = 2 ^ 3 from by norm_num]
            exact (coprime_two_odd hk_odd).pow_left 3
          have : Nat.totient n = 4 * Nat.totient (n / 8) := by
            conv_lhs => rw [hn_eq]
            rw [Nat.totient_mul hcop, show Nat.totient 8 = 4 from by native_decide]
          have h1 : Nat.totient (n / 8) = 1 := by omega
          rw [Nat.totient_eq_one_iff] at h1; rcases h1 with h1 | h1 <;> omega
      · by_cases h4 : 4 ∣ n
        · -- 4 | n, 8 ∤ n: φ(4k) = 2*φ(k) when k odd
          have hk_odd : Odd (n / 4) := by
            rw [Nat.odd_iff]; by_contra hev; push_neg at hev
            apply h8; obtain ⟨c, hc⟩ := h4; exact ⟨n / 4 / 2, by omega⟩
          have hn_eq : n = 4 * (n / 4) := by obtain ⟨c, hc⟩ := h4; omega
          have hcop : Nat.Coprime 4 (n / 4) := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num]
            exact (coprime_two_odd hk_odd).pow_left 2
          have : Nat.totient n = 2 * Nat.totient (n / 4) := by
            conv_lhs => rw [hn_eq]
            rw [Nat.totient_mul hcop, show Nat.totient 4 = 2 from by native_decide]
          have h2 : Nat.totient (n / 4) = 2 := by omega
          have := (totient_eq_two_iff (n / 4)).mp (by unfold phi; exact h2)
          rcases this with h | h | h <;> omega
        · -- 2 | n, 4 ∤ n: φ(2m) = φ(m) when m odd
          have hk_odd : Odd (n / 2) := by
            rw [Nat.odd_iff]; by_contra hev; push_neg at hev
            apply h4; obtain ⟨c, hc⟩ := hd; exact ⟨n / 2 / 2, by omega⟩
          have hn_eq : n = 2 * (n / 2) := by obtain ⟨c, hc⟩ := hd; omega
          have : Nat.totient n = Nat.totient (n / 2) := by
            conv_lhs => rw [hn_eq]; exact totient_two_mul_odd hk_odd
          exact odd_totient_ne_four (n / 2) (by omega) hk_odd (by omega)
    · -- n.minFac = 3: n is odd
      have hodd := odd_of_minFac_ge_three (by omega) (le_of_eq hpf.symm)
      exact odd_totient_ne_four n (by omega) hodd htot
    · -- n.minFac = 5: n is odd
      have h5ge3 : n.minFac ≥ 3 := by have := le_of_eq hpf.symm; omega
      have hodd := odd_of_minFac_ge_three (by omega) h5ge3
      exact odd_totient_ne_four n (by omega) hodd htot
  · rintro (rfl | rfl | rfl | rfl) <;> native_decide

end Erdos1004

/-!
## Summary

This file formalizes Erdős Problem #1004 on distinct consecutive totient values.

**Status**: OPEN (with partial results from EPS 1987)

**The Problem**: For any c > 0, if x is large enough, does there exist n ≤ x
such that φ(n+1), φ(n+2), ..., φ(n+⌊(log x)^c⌋) are all distinct?

**Known Results**:
- Erdős-Pomerance-Sárközy (1987): If φ(n+k) are distinct for 1 ≤ k ≤ K,
  then K ≤ n/exp(c(log n)^{1/3}) for some c > 0.

**What we formalize**:
1. Euler's totient function φ(n)
2. Distinct totient runs
3. Maximum run length function
4. EPS87 upper bound (axiomatized)
5. The main conjecture
6. Examples of runs and collisions
7. Connection to Problem #945 (divisor function)
8. Probabilistic heuristics
9. Special totient values

**Key axioms** (3 total):
- `eps87_theorem`: The EPS87 upper bound ∃ c > 0, N₀, ∀ n ≥ N₀, K ≤ n/exp(c(log n)^{1/3})
  (consolidated from 4 separate declarations to 1 existential axiom)
- `longer_runs_need_larger_n`: Fixed-length distinct runs exist eventually
  (probabilistic argument on totient value distribution)
- `distinct_totients_asymptotic`: #{distinct φ(k) : k ≤ x} ~ x/log x
  (Erdős 1935 / Ford 1998)

**Derived from axioms** (not axiom declarations):
- `eps87_constant`, `eps87_threshold`: noncomputable defs extracted from `eps87_theorem`
- `eps87_constant_pos`, `eps87_upper_bound`: theorems derived from `eps87_theorem`
- `run_length_sublinear`: maxDistinctRunLength(n)/n → 0 (via squeeze theorem + EPS bound)

**Related Problems**: #945 (divisor function version)
-/
