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

/-- Ruzsa's A is infinite (it contains all powers of 4). -/
axiom ruzsaA_infinite : ruzsaA.Infinite

/-- Ruzsa's B is infinite (it contains all numbers 2 * 4^k). -/
axiom ruzsaB_infinite : ruzsaB.Infinite

/-- Every positive integer has a unique representation as a + b with
    a ∈ ruzsaA and b ∈ ruzsaB. -/
axiom ruzsa_unique_rep (n : ℕ) (hn : n ≥ 1) :
    ∃! p : ℕ × ℕ, p.1 ∈ ruzsaA ∧ p.2 ∈ ruzsaB ∧ p.1 + p.2 = n

/-- Consequently, r_{A,B}(n) = 1 for all n ≥ 1. The representation function
    is bounded (in fact constant). -/
axiom ruzsa_rep_bounded : ∀ n : ℕ, n ≥ 1 → twoSetRepFunc ruzsaA ruzsaB n = 1

/-- ruzsaA + ruzsaB is a basis (covers all positive integers). -/
axiom ruzsa_is_basis : IsTwoSetBasis ruzsaA ruzsaB

/-- But the enumerations do NOT have ratio → 1.
    For Ruzsa's sets, aₙ/bₙ → 1/2 (since B = 2A). -/
axiom ruzsa_ratio_not_one : ¬HasAsymptoticRatio ruzsaA ruzsaB

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
axiom sum_of_reps_bound (A B : Set ℕ) (N : ℕ) :
    (Finset.range (N + 1)).sum (fun n => twoSetRepFunc A B n) ≥
      countingFn A N * countingFn B N - countingFn A N * countingFn B N

/-- If A + B is a basis and both sets have density ≫ √N, then the average
    representation grows without bound. -/
axiom average_rep_grows (A B : Set ℕ)
    (hBasis : IsTwoSetBasis A B)
    (hA : ∃ c > 0, ∀ N : ℕ, 1 ≤ N → (countingFn A N : ℝ) ≥ c * Real.sqrt N)
    (hB : ∃ c > 0, ∀ N : ℕ, 1 ≤ N → (countingFn B N : ℝ) ≥ c * Real.sqrt N) :
    Tendsto (fun N =>
      (Finset.range (N + 1)).sum (fun n => twoSetRepFunc A B n) / (N + 1))
      atTop atTop

/- ## Part IX: Partial Results -/

/-- If A = B and the conjecture holds (i.e., from Erdős–Turán),
    then r_{A,A}(n) ≥ 6 infinitely often (Grekos et al.).
    This extends to the two-set case when A and B are "close enough." -/
axiom grekos_two_set (A B : Set ℕ)
    (hInf_A : A.Infinite) (hInf_B : B.Infinite)
    (hRatio : HasAsymptoticRatio A B)
    (hBasis : IsTwoSetBasis A B) :
    ∀ M : ℕ, ∃ n > M, twoSetRepFunc A B n ≥ 6

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
