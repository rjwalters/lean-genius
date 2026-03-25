/-
# Erdős Problem #273: Covering Systems with Prime-Minus-One Moduli

Is there a covering system all of whose moduli are of the form p - 1
for some primes p ≥ 5?

## Status: OPEN

## References
- Erdős–Graham, "Old and New Problems and Results in Combinatorial Number Theory" (1980), p.24
- Selfridge: covering system with moduli dividing 360 when p = 3 is allowed
-/

import Mathlib

set_option maxRecDepth 1024

/-
## Section I: Covering Systems
-/

/-- A covering system is a finite collection of residue classes
a_i (mod m_i) whose union is all of ℤ. -/
structure CoveringSystem where
  /-- The index type for the residue classes. -/
  n : ℕ
  /-- The moduli (all ≥ 2). -/
  moduli : Fin n → ℕ
  /-- The residues. -/
  residues : Fin n → ℤ
  /-- Every modulus is at least 2. -/
  moduli_ge_two : ∀ i, moduli i ≥ 2
  /-- Every integer is covered by at least one residue class. -/
  covers : ∀ z : ℤ, ∃ i, z % (moduli i : ℤ) = residues i % (moduli i : ℤ)

/-
## Section II: Prime-Minus-One Moduli
-/

/-- A modulus has the p-1 form for primes ≥ k if m = p - 1 for some prime p ≥ k. -/
def IsPrimeMinusOne (k : ℕ) (m : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ m = p - 1

/-- All moduli in a covering system have the p-1 form for primes ≥ k. -/
def AllModuliPrimeMinusOne (k : ℕ) (cs : CoveringSystem) : Prop :=
  ∀ i, IsPrimeMinusOne k (cs.moduli i)

/-
## Section III: The Main Problem
-/

/-- **Erdős Problem #273**: Is there a covering system all of whose moduli
are of the form p - 1 for some primes p ≥ 5?

Since 5 - 1 = 4, 7 - 1 = 6, 11 - 1 = 10, 13 - 1 = 12, etc.,
the allowed moduli are {4, 6, 10, 12, 16, 18, 22, 28, 30, ...}. -/
def ErdosProblem273 : Prop :=
  ∃ cs : CoveringSystem, AllModuliPrimeMinusOne 5 cs

/-
## Section IV: The Selfridge Example (p ≥ 3)
-/

/-- When p ≥ 3 is allowed, a covering system exists.
The construction uses moduli 2 = 3-1 and 4 = 5-1:
the classes {0 mod 2, 1 mod 4, 3 mod 4} cover all of ℤ. -/
theorem selfridge_example :
    ∃ cs : CoveringSystem, AllModuliPrimeMinusOne 3 cs := by
  -- Define moduli and residues as explicit functions
  let m : Fin 3 → ℕ := ![2, 4, 4]
  let a : Fin 3 → ℤ := ![0, 1, 3]
  refine ⟨⟨3, m, a, ?_, ?_⟩, ?_⟩
  · -- moduli_ge_two
    intro i; fin_cases i <;> simp [m]
  · -- covers
    intro z
    have h4 : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · exact ⟨0, by simp [m, a]; omega⟩
    · exact ⟨1, by simp [m, a]; omega⟩
    · exact ⟨0, by simp [m, a]; omega⟩
    · exact ⟨2, by simp [m, a]; omega⟩
  · -- AllModuliPrimeMinusOne 3
    intro i
    fin_cases i
    · change IsPrimeMinusOne 3 2
      exact ⟨3, by norm_num, le_refl _, by norm_num⟩
    · change IsPrimeMinusOne 3 4
      exact ⟨5, by norm_num, by norm_num, by norm_num⟩
    · change IsPrimeMinusOne 3 4
      exact ⟨5, by norm_num, by norm_num, by norm_num⟩

/-
## Section V: Covering System Basics
-/

/-- The LCM of all moduli in a covering system. -/
noncomputable def CoveringSystem.lcm (cs : CoveringSystem) : ℕ :=
  (Finset.univ : Finset (Fin cs.n)).lcm cs.moduli

/-- Count of elements in {0,...,N-1} with z % m = r, when m ∣ N.
These are exactly {r, r+m, r+2m, ..., r+(N/m-1)·m}, so there are N/m of them. -/
private theorem card_residue_class_nat (m N r : ℕ) (hm : 0 < m)
    (hd : m ∣ N) (hr : r < m) :
    ((Finset.range N).filter (fun z => z % m = r)).card = N / m := by
  -- Bijection: {z ∈ [0,N) : z%m = r} ↔ [0, N/m) via j ↦ r + j*m
  have hinj : Function.Injective (fun j : ℕ => r + j * m) := by
    intro a b h
    exact mul_right_cancel₀ hm.ne' (add_left_cancel h)
  have h_eq : (Finset.range N).filter (fun z => z % m = r) =
      (Finset.range (N / m)).image (fun j => r + j * m) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hz_lt, hz_mod⟩
      refine ⟨z / m, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hm]
        calc z < N := hz_lt
          _ = N / m * m := (Nat.div_mul_cancel hd).symm
      · have h1 := Nat.div_add_mod z m
        have h2 : z / m * m = m * (z / m) := mul_comm _ _
        omega
    · rintro ⟨j, hj, rfl⟩
      constructor
      · calc r + j * m < m + j * m := by omega
          _ = (j + 1) * m := by ring
          _ ≤ (N / m) * m := Nat.mul_le_mul_right m (by omega)
          _ = N := Nat.div_mul_cancel hd
      · rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hr
  rw [h_eq, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- A covering system has n ≥ 1 (since it must cover all integers). -/
private theorem CoveringSystem.n_pos (cs : CoveringSystem) : 0 < cs.n := by
  by_contra h
  push_neg at h
  obtain ⟨i, _⟩ := cs.covers 0
  exact absurd i.isLt (by omega)

/-- In any covering system, the sum of reciprocals of moduli is ≥ 1.
Proof: Let N = ∏ mᵢ. In {0,...,N-1}, each class aᵢ mod mᵢ has exactly
N/mᵢ elements (since mᵢ | N). The covering property ensures every element
is in some class. By union bound: N ≤ ∑ N/mᵢ, giving 1 ≤ ∑ 1/mᵢ. -/
theorem covering_reciprocal_sum (cs : CoveringSystem) :
    (Finset.univ : Finset (Fin cs.n)).sum
      (fun i => (1 : ℚ) / (cs.moduli i : ℚ)) ≥ 1 := by
  -- Use N = product of all moduli (simpler positivity than LCM)
  set N := (Finset.univ : Finset (Fin cs.n)).prod cs.moduli with hN_def
  have hn_pos := cs.n_pos
  have hm_pos : ∀ i : Fin cs.n, 0 < cs.moduli i := fun i => by
    have := cs.moduli_ge_two i; omega
  have hN_pos : 0 < N := Finset.prod_pos (fun i _ => hm_pos i)
  have hdvd : ∀ i : Fin cs.n, cs.moduli i ∣ N := fun i =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  -- ℕ residue for each class: rᵢ = (aᵢ % mᵢ).toNat
  set ri : Fin cs.n → ℕ := fun i =>
    ((cs.residues i) % (cs.moduli i : ℤ)).toNat
  have hri_lt : ∀ i, ri i < cs.moduli i := by
    intro i; simp only [ri]
    have hmi : (0 : ℤ) < ↑(cs.moduli i) := by exact_mod_cast hm_pos i
    have h_lt := Int.emod_lt_of_pos (cs.residues i) hmi
    have h_nn := Int.emod_nonneg (cs.residues i) (ne_of_gt hmi)
    have key : (↑((cs.residues i % ↑(cs.moduli i)).toNat) : ℤ) =
               cs.residues i % ↑(cs.moduli i) :=
      (Int.ofNat_toNat _).trans (max_eq_left h_nn)
    suffices h : (↑((cs.residues i % ↑(cs.moduli i)).toNat) : ℤ) < ↑(cs.moduli i) by
      exact_mod_cast h
    rw [key]; exact h_lt
  -- Bridge ℤ covering to ℕ modular arithmetic
  have hbridge : ∀ (z : ℕ) (i : Fin cs.n),
      ((z : ℤ) % (cs.moduli i : ℤ) = cs.residues i % (cs.moduli i : ℤ)) →
      (z % cs.moduli i = ri i) := by
    intro z i h
    have hmi : (0 : ℤ) < ↑(cs.moduli i) := by exact_mod_cast hm_pos i
    have h_nn := Int.emod_nonneg (cs.residues i) (ne_of_gt hmi)
    have key : (↑(ri i) : ℤ) = cs.residues i % ↑(cs.moduli i) :=
      (Int.ofNat_toNat _).trans (max_eq_left h_nn)
    -- At ℤ level: ↑z % ↑m = a % ↑m (from h), and a % ↑m = ↑(ri i) (from key)
    have h_int : (↑z : ℤ) % ↑(cs.moduli i) = ↑(ri i) := by rw [h]; exact key.symm
    exact_mod_cast h_int
  -- Define ℕ residue class filter for each i
  set S := fun i : Fin cs.n =>
    (Finset.range N).filter (fun z => z % cs.moduli i = ri i)
  -- Covering: range N ⊆ ⋃ Sᵢ
  have hcover : Finset.range N ⊆ Finset.univ.biUnion S := by
    intro z hz
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, S]
    obtain ⟨i, hi⟩ := cs.covers (z : ℤ)
    exact ⟨i, Finset.mem_filter.mpr ⟨hz, hbridge z i hi⟩⟩
  -- Card of each class = N / mᵢ
  have hcard : ∀ i : Fin cs.n, (S i).card = N / cs.moduli i :=
    fun i => card_residue_class_nat _ _ _ (hm_pos i) (hdvd i) (hri_lt i)
  -- Union bound: N ≤ ∑ N/mᵢ
  have hunion : N ≤ ∑ i : Fin cs.n, N / cs.moduli i :=
    calc N = (Finset.range N).card := (Finset.card_range N).symm
      _ ≤ (Finset.univ.biUnion S).card := Finset.card_le_card hcover
      _ ≤ ∑ i, (S i).card := Finset.card_biUnion_le
      _ = ∑ i, N / cs.moduli i := Finset.sum_congr rfl (fun i _ => hcard i)
  -- Cast to ℚ and conclude
  have hN_Q : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN_pos
  -- ∑ 1/m_i = (∑ (N:ℚ)/(m_i:ℚ)) / (N:ℚ)
  have h_eq : ∑ i, (1 : ℚ) / (cs.moduli i : ℚ) =
      (∑ i, (N : ℚ) / (cs.moduli i : ℚ)) / (N : ℚ) := by
    rw [Finset.sum_div]; congr 1; ext i; field_simp
  -- (N:ℚ) ≤ ∑ (N:ℚ)/(m_i:ℚ) (from hunion + exact division)
  have h_cast : (N : ℚ) ≤ ∑ i, (N : ℚ) / (cs.moduli i : ℚ) := by
    calc (N : ℚ) ≤ ∑ i, (↑(N / cs.moduli i) : ℚ) := by exact_mod_cast hunion
      _ = ∑ i, (N : ℚ) / (cs.moduli i : ℚ) := by
          congr 1; ext i
          exact Nat.cast_div (hdvd i) (by exact_mod_cast (hm_pos i).ne')
  rw [ge_iff_le, h_eq, le_div_iff₀ hN_Q, one_mul]
  exact h_cast

/-- A distinct covering system has all moduli different.
Erdős conjectured (and Hough proved) that distinct covering systems
must have a modulus ≡ 0 (mod 2). -/
def IsDistinct (cs : CoveringSystem) : Prop :=
  Function.Injective cs.moduli

/-
## Section VI: Connection to Other Problems
-/

/-- The set of primes p ≥ 5 such that p - 1 divides 360.
These are the "easy" primes for constructing covering systems.
360 = 2³ · 3² · 5, and p - 1 | 360 for p ∈ {5, 7, 13, 19, 37, 61, 181}. -/
def easyPrimes : Finset ℕ :=
  {5, 7, 13, 19, 37, 61, 181}

/-- For p ≥ 5, the allowed moduli (p - 1 values) all have
smallest prime factor ≥ 2. The difficulty is that 2 = 3 - 1
is excluded, making it hard to cover all even integers. -/
theorem difficulty_even_coverage :
    ∀ cs : CoveringSystem, AllModuliPrimeMinusOne 5 cs →
      ∀ i, 2 < cs.moduli i := by
  intro cs h i
  obtain ⟨p, _, h5, hm⟩ := h i; omega

/-- The key obstacle: without modulus 2 (since 3 is excluded),
every modulus is ≥ 4. This severely constrains the covering. -/
theorem min_modulus_ge_4 :
    ∀ cs : CoveringSystem, AllModuliPrimeMinusOne 5 cs →
      ∀ i, cs.moduli i ≥ 4 := by
  intro cs h i
  obtain ⟨p, _, h5, hm⟩ := h i; omega

/-- All moduli in a p-1 covering (p ≥ 5) are even.
    Since p ≥ 5 implies p is odd, p - 1 is even. -/
theorem moduli_even :
    ∀ cs : CoveringSystem, AllModuliPrimeMinusOne 5 cs →
      ∀ i, Even (cs.moduli i) := by
  intro cs h i
  obtain ⟨p, hp, h5, hm⟩ := h i
  rw [hm]
  have hp_odd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp with h2 | hodd
    · omega
    · exact hodd
  exact ⟨(p - 1) / 2, by omega⟩

/-
## Section VII: Verified Properties of Easy Primes
-/

/-- Every element of easyPrimes is prime. -/
theorem easyPrimes_all_prime : ∀ p ∈ easyPrimes, Nat.Prime p := by decide

/-- Every element of easyPrimes is ≥ 5. -/
theorem easyPrimes_ge_five : ∀ p ∈ easyPrimes, 5 ≤ p := by decide

/-- For each p in easyPrimes, (p - 1) divides 360. -/
theorem easyPrimes_mod_divides_360 : ∀ p ∈ easyPrimes, (p - 1) ∣ 360 := by decide

/-
## Section IX: Reciprocal Sum Obstruction
-/

/-- The sum of reciprocals 1/(p-1) for the easy primes is 109/180,
    which is strictly less than 1. Since a covering system needs
    ∑ 1/m_i ≥ 1, the easy primes alone cannot form a covering system. -/
theorem easyPrimes_reciprocal_sum_lt_one :
    (1 : ℚ) / 4 + (1 : ℚ) / 6 + (1 : ℚ) / 12 + (1 : ℚ) / 18 +
    (1 : ℚ) / 36 + (1 : ℚ) / 60 + (1 : ℚ) / 180 < 1 := by
  norm_num

/-- The covering reciprocal sum for a system using only these moduli
    (4, 6, 12, 18, 36, 60, 180) equals 109/180.
    Even using each modulus with multiplicity, the sum must reach ≥ 1.
    So at least ⌈180/109⌉ = 2 copies of the full set, or additional
    moduli, are needed. -/
theorem reciprocal_sum_109_over_180 :
    (1 : ℚ) / 4 + (1 : ℚ) / 6 + (1 : ℚ) / 12 + (1 : ℚ) / 18 +
    (1 : ℚ) / 36 + (1 : ℚ) / 60 + (1 : ℚ) / 180 = 109 / 180 := by
  norm_num

/-- No single p-1 modulus (p ≥ 5) can cover more than 1/4 of the integers.
    The densest residue class has modulus 4 (from p = 5). -/
theorem max_single_density :
    ∀ p : ℕ, p.Prime → 5 ≤ p → (1 : ℚ) / ((p : ℚ) - 1) ≤ 1 / 4 := by
  intro p _ h5
  have h4 : (4 : ℚ) ≤ (p : ℚ) - 1 := by
    have : (5 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h5
    linarith
  exact one_div_le_one_div_of_le (by norm_num : (0:ℚ) < 4) h4
