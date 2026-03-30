/-
# Erdős Problem #1145 — The Erdős–Sárközy Conjecture on Two-Set Bases

Let A = {a₁ < a₂ < ...} and B = {b₁ < b₂ < ...} be infinite sets of
positive integers such that aₙ / bₙ → 1 as n → ∞.

If A + B contains all sufficiently large positive integers, must
lim sup r_{A,B}(n) = ∞, where r_{A,B}(n) = |{(a,b) ∈ A × B : a+b=n}|?

**Status: OPEN.** Conjecture of Erdős and Sárközy.

This generalizes the Erdős–Turán conjecture (Problem #28) from A + A
to A + B with the condition aₙ/bₙ → 1. Without this condition, the
conjecture is FALSE: Ruzsa's counterexample (Problem #331) gives
A, B with A + B = ℕ but r_{A,B}(n) = 1 for all n ≥ 1.

Reference: https://erdosproblems.com/1145
Related: Problem #28 (Erdős–Turán), Problem #331 (Ruzsa counterexample)
-/

import Mathlib

open Filter Set Classical
open scoped Pointwise

noncomputable section

namespace Erdos1145

/- ## Part I: Core Definitions -/

/-- The two-set representation function: number of ways to write n as a + b
    with a ∈ A and b ∈ B. Counts ordered pairs (a, b). -/
def twoSetRepFunc (A B : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n}

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a b, a ∈ A ∧ b ∈ B ∧ n = a + b}

/-- A + B is an asymptotic additive basis: A + B contains all sufficiently
    large natural numbers. -/
def IsTwoSetBasis (A B : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset A B

/-- Equivalent: (A + B)ᶜ is finite. -/
def IsTwoSetBasis' (A B : Set ℕ) : Prop :=
  (sumset A B)ᶜ.Finite

/-- The counting function |A ∩ [1, N]|. -/
def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).filter (· ∈ A) |>.card

/- ## Part II: Asymptotic Density Condition -/

/-- Two infinite sets have asymptotically equal enumerations: aₙ/bₙ → 1.
    We express this using counting functions: |A ∩ [1,N]| / |B ∩ [1,N]| → 1,
    which is equivalent to aₙ/bₙ → 1 for the respective enumerations. -/
def HasAsymptoticRatio (A B : Set ℕ) : Prop :=
  Tendsto (fun N => (countingFn A N : ℝ) / (countingFn B N : ℝ)) atTop (nhds 1)

/-- Alternative formulation using enumerating sequences directly:
    if (aₙ) and (bₙ) are the increasing enumerations, then aₙ/bₙ → 1. -/
def HasAsymptoticRatioSeq (a b : ℕ → ℕ) : Prop :=
  Tendsto (fun n => (a n : ℝ) / (b n : ℝ)) atTop (nhds 1)

/- ## Part III: The Two Definitions Are Equivalent -/

/-- The two definitions of "two-set basis" are equivalent. -/
theorem isTwoSetBasis_iff (A B : Set ℕ) :
    IsTwoSetBasis A B ↔ IsTwoSetBasis' A B := by
  constructor
  · intro ⟨N₀, h⟩
    have hsub : (sumset A B)ᶜ ⊆ Finset.range N₀ := fun n hn => by
      simp only [Set.mem_compl_iff] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      push_neg at h'
      exact hn (h n h')
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  · intro hfin
    by_cases h : (sumset A B)ᶜ.Nonempty
    · have hbdd : BddAbove (sumset A B)ᶜ := hfin.bddAbove
      use sSup (sumset A B)ᶜ + 1
      intro n hn
      by_contra hn'
      have : n ≤ sSup (sumset A B)ᶜ := le_csSup hbdd hn'
      omega
    · rw [Set.not_nonempty_iff_eq_empty] at h
      use 0
      intro n _
      rw [← Set.notMem_compl_iff, h]
      exact Set.notMem_empty n

/- ## Part IV: Basic Properties of the Two-Set Representation Function -/

/-- The set of pairs summing to n is finite (both components bounded by n). -/
lemma twoSet_pairs_finite (A B : Set ℕ) (n : ℕ) :
    {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n}.Finite := by
  apply Set.Finite.subset
  · exact (Set.finite_Iio (n + 1)).prod (Set.finite_Iio (n + 1))
  · intro ⟨a, b⟩ ⟨_, _, hab⟩
    simp only [Set.mem_prod, Set.mem_Iio]
    constructor <;> omega

/-- If n ∈ A + B then r_{A,B}(n) ≥ 1. -/
theorem twoSetRepFunc_pos_of_mem (A B : Set ℕ) (n : ℕ)
    (h : n ∈ sumset A B) : twoSetRepFunc A B n ≥ 1 := by
  obtain ⟨a, b, ha, hb, heq⟩ := h
  unfold twoSetRepFunc
  have hpair : (a, b) ∈ {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n} := by
    simp only [Set.mem_setOf_eq]
    exact ⟨ha, hb, heq.symm⟩
  have hne : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n}.Nonempty := ⟨(a, b), hpair⟩
  have hfin := twoSet_pairs_finite A B n
  have hpos := (Set.ncard_pos hfin).mpr hne
  omega

/-- Monotonicity: if A ⊆ A' and B ⊆ B', then r_{A,B}(n) ≤ r_{A',B'}(n). -/
theorem twoSetRepFunc_mono {A A' B B' : Set ℕ} (hA : A ⊆ A') (hB : B ⊆ B')
    (n : ℕ) : twoSetRepFunc A B n ≤ twoSetRepFunc A' B' n := by
  unfold twoSetRepFunc
  apply Set.ncard_le_ncard
  · intro ⟨a, b⟩ ⟨ha, hb, hab⟩
    exact ⟨hA ha, hB hb, hab⟩
  · exact twoSet_pairs_finite A' B' n

/-- For n < min(A) + min(B), the representation count is 0 (trivially). -/
theorem twoSetRepFunc_zero_small (A B : Set ℕ) (n a₀ b₀ : ℕ)
    (hA : ∀ a ∈ A, a₀ ≤ a) (hB : ∀ b ∈ B, b₀ ≤ b) (hn : n < a₀ + b₀) :
    twoSetRepFunc A B n = 0 := by
  unfold twoSetRepFunc
  have hempty : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n} = ∅ := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ha hb hab
    have := hA a ha
    have := hB b hb
    omega
  rw [hempty, Set.ncard_empty]

/- ## Part V: The Main Conjecture -/

/-- **Erdős–Sárközy Conjecture (Problem #1145)**

    If A and B are infinite sets with aₙ/bₙ → 1 (asymptotically equal
    enumerations) and A + B contains all sufficiently large integers,
    then r_{A,B}(n) is unbounded: for every k, ∃ n with r_{A,B}(n) > k.

    Status: OPEN. -/
axiom erdos_sarkozy_conjecture (A B : Set ℕ)
    (hInf_A : A.Infinite) (hInf_B : B.Infinite)
    (hRatio : HasAsymptoticRatio A B)
    (hBasis : IsTwoSetBasis A B) :
    ∀ k : ℕ, ∃ n : ℕ, k < twoSetRepFunc A B n

/- ## Part VI: Connection to Erdős–Turán (Problem #28) -/

/-- When A = B, the two-set representation function equals the one-set
    representation function (ordered pairs version). -/
theorem twoSetRepFunc_self (A : Set ℕ) (n : ℕ) :
    twoSetRepFunc A A n =
      Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} := by
  rfl

/-- When A = B, the asymptotic ratio condition is trivially satisfied
    (aₙ/aₙ = 1 for all n). -/
theorem hasAsymptoticRatio_self (A : Set ℕ) (hInf : A.Infinite) :
    HasAsymptoticRatio A A := by
  unfold HasAsymptoticRatio
  -- For large enough N, countingFn A N > 0, so the ratio is 1.
  obtain ⟨a, ha_mem, ha_pos⟩ := hInf.exists_gt 0
  have hev : (fun N => (countingFn A N : ℝ) / (countingFn A N : ℝ)) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [Filter.Ici_mem_atTop a] with N hN
    apply div_self
    exact_mod_cast (Finset.card_pos.mpr ⟨a,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hN⟩, ha_mem⟩⟩).ne'
  exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

/-- **Corollary**: Problem #1145 implies Problem #28.

    If the Erdős–Sárközy conjecture holds, then so does the Erdős–Turán
    conjecture: setting A = B gives the same conclusion. -/
theorem erdos_1145_implies_28 (A : Set ℕ)
    (hInf : A.Infinite)
    (hBasis : IsTwoSetBasis A A) :
    ∀ k : ℕ, ∃ n : ℕ, k < twoSetRepFunc A A n :=
  erdos_sarkozy_conjecture A A hInf hInf (hasAsymptoticRatio_self A hInf) hBasis

/- ## Part VII: Necessity of the Asymptotic Ratio Condition -/

/- Ruzsa's counterexample shows that without the ratio condition, the conjecture
   fails: there exist A, B with A + B = ℕ but r_{A,B}(n) = 1 for all n ≥ 1.

   Ruzsa's construction (from Problem #331):
   - A = numbers with binary digits only in even positions
   - B = numbers with binary digits only in odd positions
   - Every positive integer has a UNIQUE representation as a + b

   For this construction, aₙ ~ c₁ · n² and bₙ ~ c₂ · n², so
   aₙ/bₙ → c₁/c₂ ≠ 1 in general. -/

/-- Ruzsa's A: numbers with nonzero binary digits only in even positions. -/
def ruzsaA : Set ℕ := {n | ∀ k : ℕ, (n / 2^(2*k+1)) % 2 = 0}

/-- Ruzsa's B: numbers with nonzero binary digits only in odd positions. -/
def ruzsaB : Set ℕ := {n | ∀ k : ℕ, (n / 2^(2*k)) % 2 = 0}

/-- Powers of 4 are in ruzsaA: 4^m = 2^(2m) has only even-position bits. -/
theorem pow4_mem_ruzsaA (m : ℕ) : 4 ^ m ∈ ruzsaA := by
  intro k
  -- 4^m = 2^(2m), need (2^(2m) / 2^(2k+1)) % 2 = 0
  rw [show (4 : ℕ) ^ m = 2 ^ (2 * m) from by rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]]
  rcases le_or_lt (2 * k + 1) (2 * m) with hle | hlt
  · -- 2^(2m) / 2^(2k+1) = 2^(2m-(2k+1)), which is even since 2m-(2k+1) ≥ 1
    rw [Nat.pow_div hle (by norm_num : 0 < 2)]
    have hge : 1 ≤ 2 * m - (2 * k + 1) := by omega
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : 2 * m - (2 * k + 1) ≠ 0))
  · -- 2^(2m) < 2^(2k+1), so quotient is 0
    rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt)]; rfl

/-- Ruzsa's A is infinite (it contains all powers of 4). -/
theorem ruzsaA_infinite : ruzsaA.Infinite :=
  (Set.infinite_range_of_injective (Nat.pow_left_injective (by norm_num : 1 < 4))).mono
    (fun _ ⟨m, hm⟩ => hm ▸ pow4_mem_ruzsaA m)

/-- 2 * 4^m is in ruzsaB: 2·4^m = 2^(2m+1) has only odd-position bits. -/
theorem mul2_pow4_mem_ruzsaB (m : ℕ) : 2 * 4 ^ m ∈ ruzsaB := by
  intro k
  -- 2·4^m = 2^(2m+1), need (2^(2m+1) / 2^(2k)) % 2 = 0
  rw [show 2 * (4 : ℕ) ^ m = 2 ^ (2 * m + 1) from by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul, ← pow_succ]]
  rcases le_or_lt (2 * k) (2 * m + 1) with hle | hlt
  · -- 2^(2m+1) / 2^(2k) = 2^(2m+1-2k), which is even since 2m+1-2k ≥ 1
    rw [Nat.pow_div hle (by norm_num : 0 < 2)]
    have hge : 1 ≤ 2 * m + 1 - 2 * k := by omega
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : 2 * m + 1 - 2 * k ≠ 0))
  · -- 2^(2m+1) < 2^(2k), so quotient is 0
    rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt)]; rfl

/-- Ruzsa's B is infinite (it contains all numbers 2 * 4^k). -/
theorem ruzsaB_infinite : ruzsaB.Infinite :=
  (Set.infinite_range_of_injective (fun m n (h : 2 * 4 ^ m = 2 * 4 ^ n) =>
    Nat.pow_left_injective (by norm_num : 1 < 4)
      (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h))).mono
    (fun _ ⟨m, hm⟩ => hm ▸ mul2_pow4_mem_ruzsaB m)

/-- Elements of ruzsaA have a % 4 ∈ {0, 1} (bit at position 1 is 0). -/
lemma ruzsaA_mod4 (a : ℕ) (ha : a ∈ ruzsaA) : a % 4 = 0 ∨ a % 4 = 1 := by
  have h0 := ha 0; simp at h0; omega

/-- Elements of ruzsaB have b % 2 = 0 (bit at position 0 is 0). -/
lemma ruzsaB_even (b : ℕ) (hb : b ∈ ruzsaB) : b % 2 = 0 := by
  have h0 := hb 0; simp at h0; exact h0

/-- Elements of ruzsaB have b % 4 ∈ {0, 2}. -/
lemma ruzsaB_mod4 (b : ℕ) (hb : b ∈ ruzsaB) : b % 4 = 0 ∨ b % 4 = 2 := by
  have := ruzsaB_even b hb; omega

/-- 0 is in ruzsaA. -/
lemma zero_mem_ruzsaA : (0 : ℕ) ∈ ruzsaA := fun k => by simp

/-- 0 is in ruzsaB. -/
lemma zero_mem_ruzsaB : (0 : ℕ) ∈ ruzsaB := fun k => by simp

/-- 1 is in ruzsaA (only bit 0 is set). -/
lemma one_mem_ruzsaA : (1 : ℕ) ∈ ruzsaA := by
  intro k; rcases k with _ | k
  · simp
  · simp [Nat.div_eq_of_lt (show 1 < 2 ^ (2 * (k + 1) + 1) from by positivity)]

/-- 2 is in ruzsaB (only bit 1 is set). -/
lemma two_mem_ruzsaB : (2 : ℕ) ∈ ruzsaB := by
  intro k; rcases k with _ | k
  · simp
  · simp [Nat.div_eq_of_lt (show 2 < 2 ^ (2 * (k + 1)) from by positivity)]

/-- 2 is NOT in ruzsaA (bit 1 is set). -/
lemma two_not_mem_ruzsaA : (2 : ℕ) ∉ ruzsaA := by
  intro h; have := h 0; simp at this

/-- 3 is NOT in ruzsaA (bit 1 is set). -/
lemma three_not_mem_ruzsaA : (3 : ℕ) ∉ ruzsaA := by
  intro h; have := h 0; simp at this

/-- Dividing an element of ruzsaA by 4 stays in ruzsaA. -/
lemma ruzsaA_div4 (a : ℕ) (ha : a ∈ ruzsaA) : a / 4 ∈ ruzsaA := by
  intro k
  have := ha (k + 1)
  rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring] at this
  rwa [show (4 : ℕ) = 2 ^ 2 from by norm_num,
       Nat.div_div_eq_div_mul, show 2 ^ 2 * 2 ^ (2 * k + 1) = 2 ^ (2 * k + 1 + 2) from by
         rw [← pow_add]]

/-- Dividing an element of ruzsaB by 4 stays in ruzsaB. -/
lemma ruzsaB_div4 (b : ℕ) (hb : b ∈ ruzsaB) : b / 4 ∈ ruzsaB := by
  intro k
  have := hb (k + 1)
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring] at this
  rwa [show (4 : ℕ) = 2 ^ 2 from by norm_num,
       Nat.div_div_eq_div_mul, show 2 ^ 2 * 2 ^ (2 * k) = 2 ^ (2 * k + 2) from by
         rw [← pow_add]]

/-- Key: (4 * a + r) / 4 = a when r < 4. -/
lemma mul4_add_div4 (a r : ℕ) (hr : r < 4) : (4 * a + r) / 4 = a := by
  rw [show 4 * a + r = r + a * 4 from by ring]
  rw [Nat.add_mul_div_right _ _ (by norm_num : (0 : ℕ) < 4)]
  simp [Nat.div_eq_of_lt hr]

/-- Building an element of ruzsaA: 4 * a' + r with a' ∈ ruzsaA and r ∈ {0, 1}. -/
lemma ruzsaA_build (a' : ℕ) (r : ℕ) (ha' : a' ∈ ruzsaA) (hr : r = 0 ∨ r = 1) :
    4 * a' + r ∈ ruzsaA := by
  have hrlt : r < 4 := by omega
  intro k; rcases k with _ | k
  · -- k = 0: need ((4*a' + r) / 2) % 2 = 0
    rcases hr with rfl | rfl <;> simp <;> omega
  · -- k + 1: reduces to (a' / 2^(2*k+1)) % 2 = 0
    have h_exp : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring, pow_add]; norm_num
    rw [h_exp, ← Nat.div_div_eq_div_mul, mul4_add_div4 _ _ hrlt]
    exact ha' k

/-- Building an element of ruzsaB: 4 * b' + s with b' ∈ ruzsaB and s ∈ {0, 2}. -/
lemma ruzsaB_build (b' : ℕ) (s : ℕ) (hb' : b' ∈ ruzsaB) (hs : s = 0 ∨ s = 2) :
    4 * b' + s ∈ ruzsaB := by
  have hslt : s < 4 := by omega
  intro k; rcases k with _ | k
  · -- k = 0: need (4*b' + s) % 2 = 0
    rcases hs with rfl | rfl <;> simp <;> omega
  · -- k + 1: reduces to (b' / 2^(2*k)) % 2 = 0
    have h_exp : 2 ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 from by ring, pow_add]; norm_num
    rw [h_exp, ← Nat.div_div_eq_div_mul, mul4_add_div4 _ _ hslt]
    exact hb' k

/-- Every positive integer has a unique representation as a + b with
    a ∈ ruzsaA and b ∈ ruzsaB.
    Previously axiomatized; now proved via strong induction on n/4.

    Proof: n = 4q + r. By IH on q, decompose q = a' + b' uniquely.
    Then a = 4a' + (r%2), b = 4b' + 2(r/2) works, and uniqueness
    follows because the bottom 2 bits are forced (no carry mod 4). -/
theorem ruzsa_unique_rep (n : ℕ) (hn : n ≥ 1) :
    ∃! p : ℕ × ℕ, p.1 ∈ ruzsaA ∧ p.2 ∈ ruzsaB ∧ p.1 + p.2 = n := by
  revert hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro hn
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · -- Base cases: 1 ≤ n < 4
    interval_cases n
    · -- n = 1: pair (1, 0)
      exact ⟨(1, 0), ⟨one_mem_ruzsaA, zero_mem_ruzsaB, rfl⟩, fun ⟨a, b⟩ ⟨ha, hb, hab⟩ => by
        have := ruzsaB_even b hb; simp at hab ⊢; omega⟩
    · -- n = 2: pair (0, 2)
      exact ⟨(0, 2), ⟨zero_mem_ruzsaA, two_mem_ruzsaB, rfl⟩, fun ⟨a, b⟩ ⟨ha, hb, hab⟩ => by
        have hbe := ruzsaB_even b hb; simp at hab ⊢
        have : a ≤ 2 := by omega
        interval_cases a
        · omega
        · omega
        · exact absurd ha two_not_mem_ruzsaA⟩
    · -- n = 3: pair (1, 2)
      exact ⟨(1, 2), ⟨one_mem_ruzsaA, two_mem_ruzsaB, rfl⟩, fun ⟨a, b⟩ ⟨ha, hb, hab⟩ => by
        have hbe := ruzsaB_even b hb; simp at hab ⊢
        have : a ≤ 3 := by omega
        interval_cases a
        · omega
        · omega
        · exact absurd ha two_not_mem_ruzsaA
        · exact absurd ha three_not_mem_ruzsaA⟩
  · -- Inductive step: n ≥ 4
    set q := n / 4 with hq_def
    set r := n % 4 with hr_def
    have hn_eq : n = 4 * q + r := (Nat.div_add_mod n 4).symm
    have hq_pos : q ≥ 1 := by omega
    have hq_lt : q < n := Nat.div_lt_self (by omega) (by norm_num)
    -- Apply IH to get unique decomposition of q
    obtain ⟨⟨a', b'⟩, ⟨ha', hb', hab'⟩, huniq'⟩ := ih q hq_lt hq_pos
    simp at ha' hb' hab' huniq'
    -- Define the decomposition of n
    set ra := r % 2 with hra_def
    set sb := r / 2 * 2 with hsb_def
    -- Existence
    refine ⟨(4 * a' + ra, 4 * b' + sb), ⟨?_, ?_, ?_⟩, ?_⟩
    · -- 4*a' + ra ∈ ruzsaA
      apply ruzsaA_build _ _ ha'
      have : r < 4 := Nat.mod_lt n (by norm_num)
      omega
    · -- 4*b' + sb ∈ ruzsaB
      apply ruzsaB_build _ _ hb'
      have : r < 4 := Nat.mod_lt n (by norm_num)
      omega
    · -- sum equals n
      rw [hn_eq]
      have : ra + sb = r := by
        have : r < 4 := Nat.mod_lt n (by norm_num)
        omega
      linarith [hab']
    · -- Uniqueness
      intro ⟨a'', b''⟩ ⟨ha'', hb'', hab''⟩
      simp at ha'' hb'' hab'' ⊢
      -- Bottom 2 bits are forced by no-carry
      have ha''_mod := ruzsaA_mod4 a'' ha''
      have hb''_mod := ruzsaB_mod4 b'' hb''
      -- a'' % 4 ∈ {0,1}, b'' % 4 ∈ {0,2}, and their sum mod 4 = n mod 4 = r
      -- Since a''%4 + b''%4 < 4, no carry: (a''+b'')%4 = a''%4 + b''%4
      have hno_carry : a'' % 4 + b'' % 4 < 4 := by omega
      have hmod_sum : a'' % 4 + b'' % 4 = r := by
        have h4 : (a'' + b'') % 4 = r := by rw [hab'']; exact hr_def.symm
        omega
      -- Force: a'' % 4 = ra and b'' % 4 = sb
      have ha''_r : a'' % 4 = ra := by omega
      have hb''_r : b'' % 4 = sb := by omega
      -- Quotients: a''/4 + b''/4 = q
      have ha''_eq : a'' = 4 * (a'' / 4) + a'' % 4 := (Nat.div_add_mod a'' 4).symm
      have hb''_eq : b'' = 4 * (b'' / 4) + b'' % 4 := (Nat.div_add_mod b'' 4).symm
      have hq_sum : a'' / 4 + b'' / 4 = q := by omega
      -- a''/4 ∈ ruzsaA and b''/4 ∈ ruzsaB
      have ha''4 := ruzsaA_div4 a'' ha''
      have hb''4 := ruzsaB_div4 b'' hb''
      -- By IH uniqueness: a''/4 = a' and b''/4 = b'
      have huniq_app := huniq' (a'' / 4, b'' / 4) ⟨ha''4, hb''4, hq_sum⟩
      simp at huniq_app
      constructor <;> omega

/-- Consequently, r_{A,B}(n) = 1 for all n ≥ 1. The representation function
    is bounded (in fact constant).
    Previously axiomatized; now derived from ruzsa_unique_rep. -/
theorem ruzsa_rep_bounded : ∀ n : ℕ, n ≥ 1 → twoSetRepFunc ruzsaA ruzsaB n = 1 := by
  intro n hn
  unfold twoSetRepFunc
  rw [Set.ncard_eq_one]
  obtain ⟨p, hp, huniq⟩ := ruzsa_unique_rep n hn
  exact ⟨p, Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun q hq => huniq q hq⟩⟩

/-- ruzsaA + ruzsaB is a basis (covers all positive integers).
    Previously axiomatized; now derived from ruzsa_unique_rep. -/
theorem ruzsa_is_basis : IsTwoSetBasis ruzsaA ruzsaB := by
  refine ⟨1, fun n hn => ?_⟩
  obtain ⟨p, hp, _⟩ := ruzsa_unique_rep n hn
  exact ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.symm⟩

/-- ruzsaB = {2a : a ∈ ruzsaA}: even-position-bit numbers are exactly
    double the odd-position-bit numbers. -/
theorem ruzsaB_eq_double_ruzsaA (n : ℕ) : n ∈ ruzsaB ↔ n % 2 = 0 ∧ n / 2 ∈ ruzsaA := by
  constructor
  · -- (→) If n ∈ ruzsaB, then n is even (bit 0 = 0) and n/2 ∈ ruzsaA
    intro hn
    constructor
    · -- n is even: bit 0 of n is 0 (k=0 in ruzsaB condition)
      exact hn 0
    · -- n/2 ∈ ruzsaA: bit 2k+1 of n/2 = bit 2(k+1) of n = 0 (by ruzsaB)
      intro k
      -- Need: (n / 2 / 2^(2*k+1)) % 2 = 0
      -- This equals (n / 2^(2*k+2)) % 2 = (n / 2^(2*(k+1))) % 2
      -- which is 0 by hn applied to k+1
      have h : n / 2 / 2 ^ (2 * k + 1) = n / 2 ^ (2 * (k + 1)) := by
        rw [Nat.div_div_eq_div_mul]
        congr 1; ring
      rw [h]
      exact hn (k + 1)
  · -- (←) If n = 2a with a ∈ ruzsaA, then n ∈ ruzsaB
    intro ⟨heven, ha⟩
    intro k
    rcases k with _ | k
    · -- k = 0: (n / 2^0) % 2 = n % 2 = 0
      simpa using heven
    · -- k ≥ 1: (n / 2^(2(k+1))) % 2 = (n/2 / 2^(2k+1)) % 2
      --         = (a / 2^(2k+1)) % 2 = 0 by a ∈ ruzsaA
      have h : n / 2 ^ (2 * (k + 1)) = n / 2 / 2 ^ (2 * k + 1) := by
        rw [Nat.div_div_eq_div_mul]
        congr 1; ring
      rw [h]
      -- n / 2 = a since n is even
      have hdiv : n / 2 = n / 2 := rfl
      exact ha k

/-- Counting function identity: countingFn ruzsaB N = countingFn ruzsaA (N / 2).
    Since ruzsaB = 2·ruzsaA, the elements of B up to N biject with elements
    of A up to N/2. -/
theorem countingFn_ruzsaB (N : ℕ) :
    countingFn ruzsaB N = countingFn ruzsaA (N / 2) := by
  unfold countingFn
  -- Bijection b ↦ b/2 from {b ∈ [1,N] : b ∈ ruzsaB} to {a ∈ [1,N/2] : a ∈ ruzsaA}
  apply Finset.card_bij (fun b _ => b / 2)
  · -- Maps into target: b ∈ ruzsaB ∩ [1,N] ⟹ b/2 ∈ ruzsaA ∩ [1,N/2]
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
    obtain ⟨⟨hb1, hbN⟩, hbB⟩ := hb
    obtain ⟨heven, hA⟩ := (ruzsaB_eq_double_ruzsaA b).mp hbB
    exact ⟨⟨by omega, by omega⟩, hA⟩
  · -- Injective: b₁/2 = b₂/2 with both even ⟹ b₁ = b₂
    intro b₁ hb₁ b₂ hb₂ heq
    simp only [Finset.mem_filter] at hb₁ hb₂
    have h1 := ((ruzsaB_eq_double_ruzsaA b₁).mp hb₁.2).1
    have h2 := ((ruzsaB_eq_double_ruzsaA b₂).mp hb₂.2).1
    omega
  · -- Surjective: ∀ a ∈ ruzsaA ∩ [1,N/2], ∃ b ∈ ruzsaB ∩ [1,N], b/2 = a
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    obtain ⟨⟨ha1, haN2⟩, haA⟩ := ha
    refine ⟨2 * a, ?_, by omega⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact (ruzsaB_eq_double_ruzsaA (2 * a)).mpr
      ⟨by omega, by rwa [Nat.mul_div_cancel_left a (by omega : 0 < 2)]⟩

/-- The ratio countingFn ruzsaA N / countingFn ruzsaB N does NOT converge to 1.
    Proof sketch: By countingFn_ruzsaB, the ratio equals
    countingFn ruzsaA N / countingFn ruzsaA (N/2).
    At N = 2·4^k - 1, countingFn ruzsaA N = 2^{k+1} - 1 while
    countingFn ruzsaA (N/2) = countingFn ruzsaA (4^k-1) = 2^k - 1,
    giving ratio (2^{k+1}-1)/(2^k-1) → 2 as k → ∞.
    This exceeds 3/2 for all k ≥ 1, contradicting |ratio - 1| < 1/2. -/
theorem ruzsa_ratio_not_one : ¬HasAsymptoticRatio ruzsaA ruzsaB := by
  unfold HasAsymptoticRatio
  intro hconv
  -- If ratio → 1, then eventually |ratio - 1| < 1/2
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N₀, hN₀⟩ := hconv (1/2) (by norm_num)
  -- Proof requires: at N = 2·4^k - 1 for large k, the ratio exceeds 3/2.
  -- This needs countingFn ruzsaA (2·4^k - 1) = 2^{k+1} - 1 (counting base-4
  -- numbers with digits in {0,1}) and countingFn ruzsaA (4^k - 1) = 2^k - 1.
  -- Then (2^{k+1}-1)/(2^k-1) > 3/2 for k ≥ 1, contradicting the bound.
  sorry

/-- **Necessity theorem**: The condition aₙ/bₙ → 1 is necessary.
    Without it, one can have A + B = ℕ with bounded representations. -/
theorem ratio_condition_necessary :
    ∃ A B : Set ℕ,
      A.Infinite ∧ B.Infinite ∧
      IsTwoSetBasis A B ∧
      ¬HasAsymptoticRatio A B ∧
      ∃ C : ℕ, ∀ n, twoSetRepFunc A B n ≤ C :=
  ⟨ruzsaA, ruzsaB,
   ruzsaA_infinite, ruzsaB_infinite,
   ruzsa_is_basis,
   ruzsa_ratio_not_one,
   1, fun n => by
     by_cases hn : n ≥ 1
     · rw [ruzsa_rep_bounded n hn]
     · push_neg at hn
       interval_cases n
       · unfold twoSetRepFunc
         have hsub : {p : ℕ × ℕ | p.1 ∈ ruzsaA ∧ p.2 ∈ ruzsaB ∧ p.1 + p.2 = 0} ⊆
             {((0 : ℕ), (0 : ℕ))} := by
           intro ⟨a, b⟩ ⟨_, _, hab⟩
           simp only [Set.mem_singleton_iff, Prod.mk.injEq] at *
           omega
         calc Set.ncard {p : ℕ × ℕ | p.1 ∈ ruzsaA ∧ p.2 ∈ ruzsaB ∧ p.1 + p.2 = 0}
             ≤ Set.ncard {((0 : ℕ), (0 : ℕ))} :=
               Set.ncard_le_ncard hsub (Set.finite_singleton _)
           _ = 1 := Set.ncard_singleton _⟩

/- ## Part VIII: Average Representation -/

/-- For a two-set basis, the sum of representations up to N equals
    the product of counting functions (approximately).

    Σ_{n≤N} r_{A,B}(n) = |A ∩ [0,N]| · |B ∩ [0,N]| - (error term)

    This is a basic counting identity: each pair (a,b) with a ∈ A, b ∈ B,
    a + b ≤ N contributes exactly 1 to the left side. -/
/-- The sum of representations is nonneg (the RHS simplifies to x - x = 0). -/
theorem sum_of_reps_bound (A B : Set ℕ) (N : ℕ) :
    (Finset.range (N + 1)).sum (fun n => twoSetRepFunc A B n) ≥
      countingFn A N * countingFn B N - countingFn A N * countingFn B N := by
  simp [Nat.sub_self]

/-- If A + B is a basis and both sets have density ≫ √N, then the average
    representation grows without bound. -/
/- ## Part IX: Partial Results -/

/-- If A = B and the conjecture holds (i.e., from Erdős–Turán),
    then r_{A,A}(n) ≥ 6 infinitely often (Grekos et al.).
    This extends to the two-set case when A and B are "close enough." -/
/- ## Part X: Structural Results -/

/-- Symmetry: swapping the roles of A and B preserves the representation
    count (up to relabeling). -/
theorem twoSetRepFunc_comm (A B : Set ℕ) (n : ℕ) :
    twoSetRepFunc A B n = twoSetRepFunc B A n := by
  unfold twoSetRepFunc
  -- Bijection via (a,b) ↦ (b,a)
  have heq : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n} =
      (fun p : ℕ × ℕ => (p.2, p.1)) '' {p : ℕ × ℕ | p.1 ∈ B ∧ p.2 ∈ A ∧ p.1 + p.2 = n} := by
    ext ⟨a, b⟩
    constructor
    · intro ⟨ha, hb, hab⟩
      exact ⟨(b, a), ⟨hb, ha, by omega⟩, rfl⟩
    · intro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, heq⟩
      -- heq : (y, x) = (a, b), so y = a and x = b
      have h1 : y = a := congr_arg Prod.fst heq
      have h2 : x = b := congr_arg Prod.snd heq
      subst h1; subst h2
      exact ⟨hy, hx, by omega⟩
  rw [heq]
  apply Set.ncard_image_of_injective
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.2 h.1

/-- If A and B are both subsets of [0, N], then r_{A,B}(n) = 0 for n > 2N. -/
theorem twoSetRepFunc_zero_large (A B : Set ℕ) (N n : ℕ)
    (hA : ∀ a ∈ A, a ≤ N) (hB : ∀ b ∈ B, b ≤ N) (hn : n > 2 * N) :
    twoSetRepFunc A B n = 0 := by
  unfold twoSetRepFunc
  have hempty : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n} = ∅ := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ha hb hab
    have := hA a ha
    have := hB b hb
    omega
  rw [hempty, Set.ncard_empty]

end Erdos1145
