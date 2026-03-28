/-
# Erdős Problem 488: Divisibility Density in Multiples of Finite Sets

Let `A` be a finite set of positive integers and
`B = {n ≥ 1 : a | n for some a ∈ A}` (the set of multiples of
elements of `A`).

Is it true that for every `m > n ≥ max(A)`,
`|B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n`?

The constant 2 is optimal: `A = {a}`, `n = 2a-1`, `m = 2a`.

Originally posed in Erdős (1961). The 1961 version had `a ∤ n`
(likely a typo), corrected to `a | n` in 1966.

*Reference:* [erdosproblems.com/488](https://www.erdosproblems.com/488)
-/

import Mathlib

/- ## Multiples set -/

/-- `B(A)`: the set of positive integers divisible by some element
of `A`. -/
def multiplesSet (A : Finset ℕ) : Set ℕ :=
    { n : ℕ | 1 ≤ n ∧ ∃ a ∈ A, a ∣ n }

/- ## Counting function -/

/-- Count of elements of `B(A)` in `[1, N]`. -/
noncomputable def multiplesCount (A : Finset ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter (fun n => ∃ a ∈ A, a ∣ n)).card

/-- The density ratio `|B ∩ [1,N]| / N`. -/
noncomputable def multiplesRatio (A : Finset ℕ) (N : ℕ) : ℚ :=
    (multiplesCount A N : ℚ) / (N : ℚ)

/- ## Main conjecture -/

/-- Erdős Problem 488: For every finite set `A` of integers ≥ 2, and
every `m > n ≥ max(A)`, we have
`|B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n`. -/
def ErdosProblem488 : Prop :=
    ∀ (A : Finset ℕ) (hA : A.Nonempty),
      (∀ a ∈ A, 2 ≤ a) →
        ∀ (n m : ℕ),
          A.max' hA ≤ n →
          n < m →
            multiplesRatio A m < 2 * multiplesRatio A n

/- ## Inclusion–exclusion for multiples -/

/-- For a singleton `A = {a}`, `|B ∩ [1,N]| = ⌊N/a⌋`.
Proved via a bijection between `Finset.range (N/a)` and the multiples of `a`
in `[1, N]`, sending `k ↦ (k+1)*a`. -/
theorem singleton_multiplesCount (a N : ℕ) (ha : 1 ≤ a) :
    multiplesCount ({a} : Finset ℕ) N = N / a := by
  unfold multiplesCount
  -- Simplify singleton existential to plain divisibility
  have hfilt : ((Finset.Icc 1 N).filter (fun n => ∃ a' ∈ ({a} : Finset ℕ), a' ∣ n)) =
               ((Finset.Icc 1 N).filter (fun n => a ∣ n)) := by
    apply Finset.filter_congr
    intro x _
    simp only [Finset.mem_singleton, exists_eq_left]
  rw [hfilt, ← Finset.card_range (N / a)]
  -- Bijection: range (N/a) → (Icc 1 N).filter (a ∣ ·) via k ↦ (k+1)*a
  symm
  apply Finset.card_bij (fun k _ => (k + 1) * a)
  · -- Forward: (k+1)*a ∈ filtered set
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_left a (k + 1)⟩
    · -- 1 ≤ (k + 1) * a
      exact le_trans ha (le_mul_of_one_le_left (Nat.zero_le a) (by omega))
    · -- (k + 1) * a ≤ N
      exact le_trans (Nat.mul_le_mul_right a (by omega : k + 1 ≤ N / a))
                     (Nat.div_mul_le_self N a)
  · -- Injectivity
    intro k₁ _ k₂ _ h
    have := mul_right_cancel₀ (show (a : ℕ) ≠ 0 by omega) h
    omega
  · -- Surjectivity: every multiple a*m in [1,N] has m-1 ∈ range (N/a)
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    obtain ⟨m, rfl⟩ := hdvd
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp at hn1
      · omega
    refine ⟨m - 1, Finset.mem_range.mpr ?_, ?_⟩
    · -- m - 1 < N / a
      have : m ≤ N / a := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < a)]
        rwa [mul_comm]
      omega
    · -- (m - 1 + 1) * a = a * m
      have : m - 1 + 1 = m := by omega
      rw [this, mul_comm]

/-- Monotonicity: `|B ∩ [1,M]| ≤ |B ∩ [1,N]|` when `M ≤ N`. -/
theorem multiplesCount_mono (A : Finset ℕ) (M N : ℕ) (h : M ≤ N) :
    multiplesCount A M ≤ multiplesCount A N := by
  unfold multiplesCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at *
  exact ⟨⟨hn.1.1, le_trans hn.1.2 h⟩, hn.2⟩

/-- Adding elements to `A` can only increase the multiples count. -/
theorem multiplesCount_subset (A B : Finset ℕ) (h : A ⊆ B) (N : ℕ) :
    multiplesCount A N ≤ multiplesCount B N := by
  unfold multiplesCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at *
  exact ⟨hn.1, let ⟨a, haA, hdvd⟩ := hn.2; ⟨a, h haA, hdvd⟩⟩

/- ## Optimality of constant 2 -/

/-- The constant 2 is optimal: for `A = {a}`, `n = 2a-1`, `m = 2a`,
the ratio approaches 2 as `a → ∞`.

For singleton `{a}`: `multiplesCount {a} (2a) = 2` and
`multiplesCount {a} (2a-1) = 1`, so the ratio is
`(2/(2a)) / (1/(2a-1)) = (2a-1)/a = 2 - 1/a → 2`. -/
theorem constant_2_optimal :
    ∀ (ε : ℚ), 0 < ε →
      ∃ a : ℕ, 2 ≤ a ∧
        let A := ({a} : Finset ℕ)
        let n := 2 * a - 1
        let m := 2 * a
        2 - ε < multiplesRatio A m / multiplesRatio A n := by
  intro ε hε
  -- Choose a > 1/ε with a ≥ 2
  obtain ⟨a₀, ha₀⟩ := exists_nat_gt (1 / ε)
  refine ⟨max a₀ 2, le_max_right _ _, ?_⟩
  set a := max a₀ 2
  have ha2 : 2 ≤ a := le_max_right _ _
  have ha_pos : (0 : ℚ) < ↑a := by exact_mod_cast (show 0 < a by omega)
  -- Compute multiplesCount values
  show 2 - ε < multiplesRatio ({a} : Finset ℕ) (2 * a) /
               multiplesRatio ({a} : Finset ℕ) (2 * a - 1)
  have ha1 : 1 ≤ a := by omega
  have ha0 : 0 < a := by omega
  simp only [multiplesRatio]
  rw [singleton_multiplesCount a (2 * a) ha1,
      singleton_multiplesCount a (2 * a - 1) ha1,
      show 2 * a / a = 2 from Nat.mul_div_cancel 2 ha0,
      show (2 * a - 1) / a = 1 from
        Nat.div_eq_of_lt_le (by omega) (by omega)]
  -- Goal: 2 - ε < ((2 : ℚ) / ↑(2 * a)) / ((1 : ℚ) / ↑(2 * a - 1))
  -- Suffices to show 2 - ε < (2*a-1)/a = 2 - 1/a
  suffices h : 2 - ε < (2 * (↑a : ℚ) - 1) / ↑a by
    have h2a_ne : (↑(2 * a) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2a1_ne : (↑(2 * a - 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ha_ne : (↑a : ℚ) ≠ 0 := ne_of_gt ha_pos
    convert h using 1
    field_simp
    rw [Nat.cast_sub (show 1 ≤ 2 * a by omega), Nat.cast_mul, Nat.cast_ofNat]
    ring
  -- Prove: 2 - ε < (2*↑a - 1) / ↑a = 2 - 1/↑a
  have heq : (2 * (↑a : ℚ) - 1) / ↑a = 2 - 1 / ↑a := by field_simp
  rw [heq]
  -- Goal: 2 - ε < 2 - 1 / ↑a
  -- Key: 1/↑a < ε follows from 1/ε < a
  have h_inv : (1 : ℚ) / ↑a < ε := by
    have h : 1 / ε < ↑a := lt_of_lt_of_le ha₀ (Nat.cast_le.mpr (le_max_left _ _))
    have h1 : 1 < ↑a * ε := by rwa [div_lt_iff₀ hε] at h
    exact (div_lt_iff₀ ha_pos).mpr (by linarith [mul_comm (↑a : ℚ) ε])
  linarith

/- ## Davenport's density -/

/-- Divisibility is periodic: `a ∣ n ↔ a ∣ (n + P)` when `a ∣ P`. -/
private lemma dvd_add_period_iff {a P n : ℕ} (haP : a ∣ P) :
    a ∣ n ↔ a ∣ (n + P) :=
  ⟨fun h => dvd_add h haP, fun h => by
    have := Nat.dvd_sub' h haP; rwa [Nat.add_sub_cancel] at this⟩

/-- `lcm(A) > 0` when all elements of `A` are positive. -/
private lemma lcm_pos_of_pos (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) : 0 < A.lcm id := by
  apply Nat.pos_of_ne_zero; intro h
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨a, ha, ha0⟩ := h
  simp only [id_eq] at ha0
  exact absurd (hA a ha) (by omega)

/-- Membership in `B(A)` is periodic with period `lcm(A)`. -/
private lemma inB_periodic (A : Finset ℕ) (n : ℕ) :
    (∃ a ∈ A, a ∣ n) ↔ (∃ a ∈ A, a ∣ (n + A.lcm id)) := by
  constructor
  · rintro ⟨a, ha, hd⟩; exact ⟨a, ha, (dvd_add_period_iff (Finset.dvd_lcm ha)).mp hd⟩
  · rintro ⟨a, ha, hd⟩; exact ⟨a, ha, (dvd_add_period_iff (Finset.dvd_lcm ha)).mpr hd⟩

/-- Step recurrence: adding `N+1` to the range increments the count by 0 or 1. -/
private lemma multiplesCount_succ' (A : Finset ℕ) (N : ℕ) :
    multiplesCount A (N + 1) = multiplesCount A N +
      if ∃ a ∈ A, a ∣ (N + 1) then 1 else 0 := by
  unfold multiplesCount
  have hset : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hmem : N + 1 ∉ (Finset.Icc 1 N).filter (fun n => ∃ a ∈ A, a ∣ n) := by
    simp only [Finset.mem_filter, Finset.mem_Icc, not_and]; omega
  rw [hset, Finset.filter_insert]
  split
  · exact Finset.card_insert_of_not_mem hmem
  · rfl

/-- Periodicity of the counting function:
`|B(A) ∩ [1, N+P]| = |B(A) ∩ [1, N]| + |B(A) ∩ [1, P]|`. -/
private theorem multiplesCount_add_period (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (N : ℕ) :
    multiplesCount A (N + A.lcm id) = multiplesCount A N + multiplesCount A (A.lcm id) := by
  induction N with
  | zero =>
    have : multiplesCount A 0 = 0 := by
      unfold multiplesCount; simp [Finset.Icc_eq_empty (by omega : ¬(1 ≤ 0))]
    omega
  | succ n ih =>
    rw [show n + 1 + A.lcm id = (n + A.lcm id) + 1 from by omega]
    rw [multiplesCount_succ' A (n + A.lcm id), ih, multiplesCount_succ' A n]
    have hper : (∃ a ∈ A, a ∣ (n + A.lcm id + 1)) ↔ (∃ a ∈ A, a ∣ (n + 1)) := by
      rw [show n + A.lcm id + 1 = (n + 1) + A.lcm id from by omega]
      exact (inB_periodic A (n + 1)).symm
    simp only [hper]; omega

/-- Decomposition via division: `count(qP + r) = q · count(P) + count(r)`. -/
private theorem multiplesCount_div_mod (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (N : ℕ) :
    multiplesCount A N =
      (N / A.lcm id) * multiplesCount A (A.lcm id) + multiplesCount A (N % A.lcm id) := by
  set P := A.lcm id
  have hP : 0 < P := lcm_pos_of_pos A hA
  have hN : N = N / P * P + N % P := (Nat.div_add_mod N P).symm
  conv_lhs => rw [hN]
  induction (N / P) with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * P + N % P = (q * P + N % P) + P from by ring]
    rw [multiplesCount_add_period A hA, ih]; ring

/-- `multiplesCount A N ≤ N` (we filter a subset of `[1, N]`). -/
private lemma multiplesCount_le (A : Finset ℕ) (N : ℕ) : multiplesCount A N ≤ N := by
  unfold multiplesCount
  calc ((Finset.Icc 1 N).filter _).card ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ = N := by simp [Finset.card_Icc]; omega

/-- The asymptotic density of `B(A)` exists and equals `count(P)/P` where `P = lcm(A)`.

Proved via periodicity: `B(A)` has period `P = lcm(A)`, so the ratio
`|B(A) ∩ [1,N]| / N` converges to `|B(A) ∩ [1,P]| / P` with error `O(P/N)`. -/
theorem multiplesSet_density_exists (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a)
    (hAne : A.Nonempty) :
    ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ ε : ℚ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          |multiplesRatio A N - δ| < ε := by
  set P := A.lcm id with hP_def
  set c := multiplesCount A P with hc_def
  have hP_pos : (0 : ℕ) < P := lcm_pos_of_pos A hA
  have hP_ne : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- δ = c / P
  refine ⟨(c : ℚ) / (P : ℚ), ?_, ?_, ?_⟩
  · -- 0 < c/P: A nonempty implies c ≥ 1
    apply div_pos (by exact_mod_cast show 0 < c from ?_) (by exact_mod_cast hP_pos)
    -- Show c > 0: pick a ∈ A, then a ∈ [1,P] and a ∣ a
    obtain ⟨a, haA⟩ := hAne
    have ha1 : 1 ≤ a := hA a haA
    have haP : a ≤ P := Nat.le_of_dvd (by omega) (Finset.dvd_lcm haA)
    have : 0 < ((Finset.Icc 1 P).filter (fun n => ∃ b ∈ A, b ∣ n)).card := by
      apply Finset.card_pos.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haP⟩, ⟨a, haA, dvd_refl a⟩⟩⟩
    exact this
  · -- c/P ≤ 1
    rw [div_le_one (by exact_mod_cast hP_pos)]
    exact_mod_cast multiplesCount_le A P
  · -- Convergence: |multiplesRatio A N - c/P| < ε for large N
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((P : ℚ) / ε)
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hN_pos : 0 < N := by omega
    have hN_ne : (↑N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    -- Decomposition
    have hdecomp := multiplesCount_div_mod A hA N
    set q := N / P; set r := N % P; set d := multiplesCount A r
    have hr_lt : r < P := Nat.mod_lt N hP_pos
    have hN_eq : N = q * P + r := by
      have := (Nat.div_add_mod N P).symm; linarith [mul_comm P q]
    have hN_cast : (↑N : ℚ) = ↑q * ↑P + ↑r := by exact_mod_cast hN_eq
    have hd_le : d ≤ r := multiplesCount_le A r
    have hc_le : c ≤ P := multiplesCount_le A P
    -- Key inequality: P < ε * N
    have hPN : (↑P : ℚ) < ε * ↑N := by
      have h1 : (↑P : ℚ) / ε < ↑N :=
        lt_of_lt_of_le hN₀ (Nat.cast_le.mpr (le_trans (le_max_left _ _) hN))
      rw [div_lt_iff₀ hε] at h1; linarith
    -- Main proof
    show |multiplesRatio A N - ↑c / ↑P| < ε
    unfold multiplesRatio; rw [hdecomp]
    -- Rewrite as single fraction: (q*c+d)/N - c/P = (d*P - r*c) / (N*P)
    have h_eq : (↑(q * c + d) : ℚ) / ↑N - ↑c / ↑P =
        (↑d * ↑P - ↑r * ↑c) / (↑N * ↑P) := by
      rw [div_sub_div _ _ hN_ne hP_ne]; congr 1
      · rw [hN_cast]; push_cast; ring
      · ring
    rw [h_eq, abs_div, abs_of_pos (by positivity : (0 : ℚ) < ↑N * ↑P),
        div_lt_iff₀ (by positivity : (0 : ℚ) < ↑N * ↑P)]
    -- Bound: |d*P - r*c| ≤ P*r < P² < ε*N*P
    have habs : |(↑d * ↑P - ↑r * ↑c : ℚ)| ≤ ↑P * ↑r := by
      rw [abs_le]; constructor <;>
        nlinarith [Nat.cast_nonneg d, Nat.cast_nonneg c,
          Nat.cast_nonneg r, Nat.cast_nonneg P,
          Nat.cast_le.mpr hd_le, Nat.cast_le.mpr hc_le]
    calc |(↑d * ↑P - ↑r * ↑c : ℚ)|
        ≤ ↑P * ↑r := habs
      _ < ↑P * ↑P := by
          exact mul_lt_mul_of_pos_left
            (by exact_mod_cast hr_lt) (by exact_mod_cast hP_pos)
      _ < ε * ↑N * ↑P := by
          exact mul_lt_mul_of_pos_right hPN (by exact_mod_cast hP_pos)
      _ = ε * (↑N * ↑P) := by ring

