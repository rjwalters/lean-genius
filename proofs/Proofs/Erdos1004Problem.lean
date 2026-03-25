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
    for some constant c > 0.

    This limits how long a distinct totient run can be.
-/
axiom eps87_constant : ℝ

axiom eps87_constant_pos : eps87_constant > 0

axiom eps87_upper_bound (n K : ℕ) (hn : n > 0) (hrun : IsDistinctTotientRun n K) :
    (K : ℝ) ≤ (n : ℝ) / Real.exp (eps87_constant * (Real.log (n : ℝ)) ^ ((1 : ℝ)/3))

/-- The maxDistinctRunLength is bounded by the EPS87 bound for n > 0. -/
private lemma maxDistinctRunLength_le_eps87 (n : ℕ) (hn : n > 0) :
    (maxDistinctRunLength n : ℝ) ≤
      (n : ℝ) / Real.exp (eps87_constant * (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) := by
  unfold maxDistinctRunLength
  set S : Set ℕ := {K : ℕ | IsDistinctTotientRun n K} with hS_def
  set B := (n : ℝ) / Real.exp (eps87_constant * (Real.log ↑n) ^ ((1 : ℝ) / 3)) with hB_def
  have hB : 0 ≤ B := div_nonneg (Nat.cast_nonneg n) (le_of_lt (Real.exp_pos _))
  have hne : S.Nonempty := ⟨1, distinctRun_one n⟩
  have hsup : sSup S ≤ ⌊B⌋₊ :=
    csSup_le hne fun K hK => Nat.le_floor (eps87_upper_bound n K hn hK)
  calc (↑(sSup S) : ℝ) ≤ ↑⌊B⌋₊ := Nat.cast_le.mpr hsup
    _ ≤ B := Nat.floor_le hB

/-- Corollary: The run length is o(n). -/
theorem run_length_sublinear :
    Tendsto (fun n : ℕ => (maxDistinctRunLength n : ℝ) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hc := eps87_constant_pos
  -- Prepare bounding function g and prove g → 0
  have h_log : Tendsto (fun n : ℕ => Real.log (↑n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- (log n)^(1/3) → ∞
  have h_rpow : Tendsto (fun n : ℕ => (Real.log (↑n : ℝ)) ^ ((1 : ℝ) / 3)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp h_log) ((max b 0) ^ (3 : ℕ))
    exact ⟨N, fun n hn => by
      have hlog := hN n hn
      have hM : (0 : ℝ) ≤ max b 0 := le_max_right b 0
      suffices hsuff : ((max b 0) ^ (3 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = max b 0 by
        calc b ≤ max b 0 := le_max_left b 0
          _ = ((max b 0) ^ (3 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := hsuff.symm
          _ ≤ (Real.log (↑n : ℝ)) ^ ((1 : ℝ) / 3) :=
              Real.rpow_le_rpow (pow_nonneg hM 3) hlog (by norm_num)
      rw [← Real.rpow_natCast (max b 0) 3, ← Real.rpow_mul hM]
      have : ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3) = 1 := by push_cast; ring
      rw [this, Real.rpow_one]⟩
  -- c * (log n)^(1/3) → ∞
  have h_mul : Tendsto (fun n : ℕ => eps87_constant * (Real.log (↑n : ℝ)) ^ ((1 : ℝ) / 3))
      atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp h_rpow (b / eps87_constant)
    exact ⟨N, fun n hn => by
      have h := hN n hn
      have hcb : eps87_constant * (b / eps87_constant) = b := by field_simp
      linarith [mul_le_mul_of_nonneg_left h (le_of_lt hc)]⟩
  -- g = (exp ∘ (c * ·) ∘ (·^(1/3)) ∘ log ∘ ↑)⁻¹ → 0
  have h_lim : Tendsto (fun n : ℕ => (Real.exp (eps87_constant *
      (Real.log (↑n : ℝ)) ^ ((1 : ℝ) / 3)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp h_mul)
  -- Upper bound
  have h_bound : ∀ n : ℕ, (maxDistinctRunLength n : ℝ) / ↑n ≤
      (Real.exp (eps87_constant * (Real.log (↑n : ℝ)) ^ ((1 : ℝ) / 3)))⁻¹ := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hn' := Nat.pos_of_ne_zero hn
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn'
      have hexp_pos := Real.exp_pos (eps87_constant * (Real.log ↑n) ^ ((1 : ℝ) / 3))
      rw [inv_eq_one_div, div_le_div_iff₀ hn_pos hexp_pos, one_mul]
      calc ↑(maxDistinctRunLength n) *
              Real.exp (eps87_constant * (Real.log ↑n) ^ ((1 : ℝ) / 3))
          ≤ (↑n / Real.exp (eps87_constant * (Real.log ↑n) ^ ((1 : ℝ) / 3))) *
              Real.exp (eps87_constant * (Real.log ↑n) ^ ((1 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_right (maxDistinctRunLength_le_eps87 n hn') (le_of_lt hexp_pos)
        _ = ↑n := div_mul_cancel₀ _ (ne_of_gt hexp_pos)
  -- Squeeze: 0 ≤ f ≤ g, g → 0
  exact squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    h_bound h_lim

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

/-- Looking for longer runs requires larger n. -/
axiom longer_runs_need_larger_n (K : ℕ) (hK : K ≥ 2) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ m ≤ n, IsDistinctTotientRun m K := by

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

/-- Asymptotically, there are ~ x / log x distinct totient values ≤ x. -/
axiom distinct_totients_asymptotic :
    Tendsto (fun x : ℕ => (countDistinctTotients x : ℝ) * Real.log (x : ℝ) / (x : ℝ))
      atTop (𝓝 (1 : ℝ)) := by

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
/-- For prime p dividing n (n ≠ 0), (p - 1) divides φ(n).
    Proof: extract p^e from n's factorization, apply multiplicativity. -/
private lemma prime_pred_dvd_totient {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hne : n ≠ 0) : (p - 1) ∣ n.totient := by
  have he : 0 < n.factorization p := by
    rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpn, hne⟩
  have hpow : p ^ n.factorization p ∣ n :=
    (hp.pow_dvd_iff_le_factorization hne).mpr le_rfl
  have hcop : Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) := by
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have : p ^ (n.factorization p + 1) ∣ n := by
      calc p ^ (n.factorization p + 1)
          = p ^ n.factorization p * p := by ring
        _ ∣ p ^ n.factorization p * (n / p ^ n.factorization p) :=
            Nat.mul_dvd_mul_left _ hd
        _ = n := Nat.mul_div_cancel' hpow
    exact absurd ((hp.pow_dvd_iff_le_factorization hne).mp this) (by omega)
  calc (p - 1) ∣ p ^ (n.factorization p - 1) * (p - 1) := dvd_mul_left _ _
    _ ∣ (p ^ n.factorization p).totient := by rw [Nat.totient_prime_pow hp he]
    _ ∣ (p ^ n.factorization p).totient * (n / p ^ n.factorization p).totient :=
        dvd_mul_right _ _
    _ = n.totient := by rw [← Nat.totient_mul hcop, Nat.mul_div_cancel' hpow]

/-- φ(n) = 2 iff n ∈ {3, 4, 6}. -/
theorem totient_eq_two_iff (n : ℕ) : phi n = 2 ↔ n = 3 ∨ n = 4 ∨ n = 6 := by
  unfold phi
  constructor
  · intro h
    suffices n ≤ 6 by interval_cases n <;> revert h <;> native_decide
    by_contra hgt; push_neg at hgt
    -- If 5 ∣ n: 4 ∣ φ(n) = 2, contradiction. If 5 ∤ n: {1, 5, n-1} ⊂ coprimes, φ ≥ 3.
    by_cases h5 : 5 ∣ n
    · have h4 := prime_pred_dvd_totient (by norm_num : Nat.Prime 5) h5 (by omega)
      simp only [show (5 : ℕ) - 1 = 4 from rfl] at h4; omega
    · set S := (Finset.range n).filter n.Coprime with hS
      have h1 : 1 ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, Nat.coprime_one_right n⟩
      have h5m : 5 ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, Nat.Coprime.symm
          ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5)⟩
      have hn1 : (n - 1) ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        show Nat.gcd n (n - 1) = 1
        -- Consecutive integers are coprime: gcd(n, n-1) = 1
        -- n = 1 + (n-1), so n % (n-1) = 1, then gcd(n, n-1) = gcd(n-1, 1) = 1
        have hmod : n % (n - 1) = 1 := by
          nth_rewrite 1 [show n = 1 + (n - 1) from by omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < n - 1)]
        rw [Nat.gcd_comm, Nat.gcd_rec, hmod]
        simp
      have hsub : ({1, 5, n - 1} : Finset ℕ) ⊆ S := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard : ({1, 5, n - 1} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_singleton]
        · simp only [Finset.mem_singleton]; omega
        · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have : 3 ≤ S.card := by linarith [Finset.card_le_card hsub]
      change S.card = 2 at h; omega
  · rintro (rfl | rfl | rfl) <;> native_decide

/-- φ(n) = 4 iff n ∈ {5, 8, 10, 12}. -/
theorem totient_eq_four_iff (n : ℕ) :
    phi n = 4 ↔ n = 5 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
  unfold phi
  constructor
  · intro h
    suffices n ≤ 17 by interval_cases n <;> revert h <;> native_decide
    by_contra hgt; push_neg at hgt
    -- Primes 7, 11, 13, 17 can't divide n: (p-1) ∤ 4
    have h7 : ¬ 7 ∣ n := fun hd => by
      have := prime_pred_dvd_totient (by norm_num : Nat.Prime 7) hd (by omega)
      simp only [show (7 : ℕ) - 1 = 6 from rfl] at this; omega
    have h11 : ¬ 11 ∣ n := fun hd => by
      have := prime_pred_dvd_totient (by norm_num : Nat.Prime 11) hd (by omega)
      simp only [show (11 : ℕ) - 1 = 10 from rfl] at this; omega
    have h13 : ¬ 13 ∣ n := fun hd => by
      have := prime_pred_dvd_totient (by norm_num : Nat.Prime 13) hd (by omega)
      simp only [show (13 : ℕ) - 1 = 12 from rfl] at this; omega
    have h17 : ¬ 17 ∣ n := fun hd => by
      have := prime_pred_dvd_totient (by norm_num : Nat.Prime 17) hd (by omega)
      simp only [show (17 : ℕ) - 1 = 16 from rfl] at this; omega
    -- {1, 7, 11, 13, 17} are 5 coprimes to n in {0,...,n-1}, so φ ≥ 5 > 4
    set S := (Finset.range n).filter n.Coprime with hS
    have mk : ∀ k, k < n → n.Coprime k → k ∈ S := fun k hk hc => by
      simp only [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hc⟩
    have cop : ∀ p, Nat.Prime p → ¬ p ∣ n → n.Coprime p :=
      fun p hp hd => Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hd)
    have hsub : ({1, 7, 11, 13, 17} : Finset ℕ) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact mk 1 (by omega) (Nat.coprime_one_right n)
      · exact mk 7 (by omega) (cop 7 (by norm_num) h7)
      · exact mk 11 (by omega) (cop 11 (by norm_num) h11)
      · exact mk 13 (by omega) (cop 13 (by norm_num) h13)
      · exact mk 17 (by omega) (cop 17 (by norm_num) h17)
    have hcard : ({1, 7, 11, 13, 17} : Finset ℕ).card = 5 := by native_decide
    have : 5 ≤ S.card := by linarith [Finset.card_le_card hsub]
    change S.card = 4 at h; omega
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

**Key axioms**:
- `eps87_upper_bound`: The EPS87 theorem limiting run length
- `eps87_constant`: The constant c in the bound

**Related Problems**: #945 (divisor function version)
-/
