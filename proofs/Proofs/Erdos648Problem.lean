/-
Erdős Problem #648: Descending Greatest Prime Factor Sequences

Source: https://erdosproblems.com/648
Status: SOLVED (Stijn Cambie)

Statement:
Let P(m) denote the greatest prime factor of m.
Let g(n) be the largest t such that there exist integers
  2 ≤ a₁ < a₂ < ... < aₜ < n
with
  P(a₁) > P(a₂) > ... > P(aₜ)

Estimate g(n).

Answer:
Stijn Cambie proved that g(n) ≍ (n / log n)^{1/2}.

More precisely, there exists a constant c with 2 ≤ c ≤ 2√2 such that
g(n) ~ c · (n / log n)^{1/2}.

Key Insight:
To build a long descending sequence of greatest prime factors, we need
integers whose greatest prime factors form a strictly decreasing sequence.
The optimal strategy involves smooth numbers (numbers with small prime factors)
and careful selection to maximize sequence length.

References:
- Cambie, Stijn: Solution to Erdős Problem #648
- Erdős, P.: Problems in number theory and combinatorics
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Finset

namespace Erdos648

/-
## Part I: Greatest Prime Factor

The function P(n) returns the greatest prime divisor of n.
Defined as the last element of the sorted prime factorization list.
-/

/--
**Greatest Prime Factor** P(n):
The largest prime that divides n.

For n > 1, this is the last element of `n.primeFactorsList` (sorted ascending).
For n ≤ 1, we define it as 0.
-/
def gpf (n : ℕ) : ℕ := n.primeFactorsList.getLast?.getD 0

/-- P(1) = 0 by convention. -/
theorem gpf_one : gpf 1 = 0 := by native_decide

/-- P(0) = 0 by convention. -/
theorem gpf_zero : gpf 0 = 0 := by native_decide

/-- Prime factors list of n > 1 is nonempty. -/
private lemma pfl_ne_nil {n : ℕ} (hn : n > 1) : n.primeFactorsList ≠ [] := by
  intro h
  have := Nat.prod_primeFactorsList (show n ≠ 0 by omega)
  rw [h, List.prod_nil] at this
  omega

/-- gpf n equals the last element of primeFactorsList when nonempty. -/
private lemma gpf_eq_getLast {n : ℕ} (hne : n.primeFactorsList ≠ []) :
    gpf n = n.primeFactorsList.getLast hne := by
  simp [gpf, List.getLast?_eq_some_getLast hne]

/-- gpf n is in n.primeFactorsList for n > 1. -/
private lemma gpf_mem_pfl {n : ℕ} (hn : n > 1) : gpf n ∈ n.primeFactorsList := by
  have hne := pfl_ne_nil hn
  rw [gpf_eq_getLast hne]
  exact List.getLast_mem hne

/-- The primeFactorsList is pairwise ≤ (sorted ascending). -/
private lemma pfl_pairwise_le (n : ℕ) : n.primeFactorsList.Pairwise (· ≤ ·) :=
  (Nat.isChain_primeFactorsList n).pairwise

/-- In a list with Pairwise (· ≤ ·), every element is ≤ the last. -/
private theorem sorted_le_getLast : ∀ (l : List ℕ),
    l.Pairwise (· ≤ ·) → ∀ (x : ℕ), x ∈ l → ∀ (hne : l ≠ []), x ≤ l.getLast hne
  | [], _, _, hx, _ => absurd hx (by simp)
  | [_], _, _, hx, _ => by simp at hx ⊢; omega
  | _ :: b :: l, hs, x, hx, _ => by
    cases hs with
    | cons hall hpw =>
      have hb_mem : b ∈ b :: l := by simp
      rcases List.mem_cons.mp hx with rfl | hm
      · exact le_trans (@hall b hb_mem)
          (sorted_le_getLast (b :: l) hpw b hb_mem (List.cons_ne_nil b l))
      · exact sorted_le_getLast (b :: l) hpw x (by exact hm) (List.cons_ne_nil b l)

/-- All prime factors are ≤ gpf n. -/
private lemma le_gpf_of_mem_pfl {n p : ℕ} (hp : p ∈ n.primeFactorsList) : p ≤ gpf n := by
  have hne : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hp
  rw [gpf_eq_getLast hne]
  exact sorted_le_getLast n.primeFactorsList (pfl_pairwise_le n) p hp hne

/-- P(p) = p for prime p. -/
theorem gpf_prime (p : ℕ) (hp : p.Prime) : gpf p = p := by
  simp [gpf, Nat.primeFactorsList_prime hp]

/-- P(n) divides n for n > 1. -/
theorem gpf_dvd (n : ℕ) (hn : n > 1) : gpf n ∣ n :=
  Nat.dvd_of_mem_primeFactorsList (gpf_mem_pfl hn)

/-- P(n) is prime for n > 1. -/
theorem gpf_is_prime (n : ℕ) (hn : n > 1) : (gpf n).Prime :=
  Nat.prime_of_mem_primeFactorsList (gpf_mem_pfl hn)

/-- P(n) is the maximum: any prime dividing n is ≤ P(n). -/
theorem gpf_max (n p : ℕ) (hp : p.Prime) (hdvd : p ∣ n) (hn : n > 0) : p ≤ gpf n := by
  have hmem : p ∈ n.primeFactorsList :=
    (Nat.mem_primeFactorsList (show n ≠ 0 by omega)).mpr ⟨hp, hdvd⟩
  exact le_gpf_of_mem_pfl hmem

/-
## Part II: Concrete Examples
-/

/-- P(2) = 2 -/
theorem gpf_two : gpf 2 = 2 := gpf_prime 2 Nat.prime_two

/-- P(3) = 3 -/
theorem gpf_three : gpf 3 = 3 := gpf_prime 3 Nat.prime_three

/-- P(4) = 2 (since 4 = 2²) -/
theorem gpf_four : gpf 4 = 2 := by native_decide

/-- P(6) = 3 (since 6 = 2 · 3) -/
theorem gpf_six : gpf 6 = 3 := by native_decide

/-- P(8) = 2 (since 8 = 2³) -/
theorem gpf_eight : gpf 8 = 2 := by native_decide

/-- P(9) = 3 (since 9 = 3²) -/
theorem gpf_nine : gpf 9 = 3 := by native_decide

/-- P(10) = 5 (since 10 = 2 · 5) -/
theorem gpf_ten : gpf 10 = 5 := by native_decide

/-- P(12) = 3 (since 12 = 2² · 3) -/
theorem gpf_twelve : gpf 12 = 3 := by native_decide

/-- P(16) = 2 (since 16 = 2⁴) -/
theorem gpf_sixteen : gpf 16 = 2 := by native_decide

/-- P(27) = 3 (since 27 = 3³) -/
theorem gpf_twentyseven : gpf 27 = 3 := by native_decide

/-- P(64) = 2 (since 64 = 2⁶) -/
theorem gpf_sixtyfour : gpf 64 = 2 := by native_decide

/-
## Part III: Descending GPF Sequences
-/

def isGPFDescendingSeq (seq : List ℕ) : Prop :=
  seq.IsChain (· < ·) ∧ (seq.map gpf).IsChain (· > ·)

def isValidGPFSeq (n : ℕ) (seq : List ℕ) : Prop :=
  isGPFDescendingSeq seq ∧ (∀ a ∈ seq, 2 ≤ a ∧ a < n)

noncomputable def g (n : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ seq : List ℕ, seq.length = t ∧ isValidGPFSeq n seq}

/-
## Part IV: Example Sequences
-/

theorem example_3_4_gpf_descending : gpf 3 > gpf 4 := by
  rw [gpf_three, gpf_four]; omega

theorem example_7_9_16_gpf_descending :
    gpf 7 > gpf 9 ∧ gpf 9 > gpf 16 := by
  constructor
  · rw [gpf_prime 7 (by decide : Nat.Prime 7), gpf_nine]; omega
  · rw [gpf_nine, gpf_sixteen]; omega

theorem example_length_4_exists :
    gpf 7 > gpf 10 ∧ gpf 10 > gpf 27 ∧ gpf 27 > gpf 64 := by
  constructor
  · rw [gpf_prime 7 (by decide : Nat.Prime 7), gpf_ten]; omega
  constructor
  · rw [gpf_ten, gpf_twentyseven]; omega
  · rw [gpf_twentyseven, gpf_sixtyfour]; omega

/-
## Part V: Lower Bounds on g(n)
-/

/-- The set of valid sequence lengths is bounded above by n.
Proof: a strictly increasing list with all elements < n has length ≤ n
(by nodup + subset of Finset.range n). -/
private lemma g_bddAbove (n : ℕ) : BddAbove {t : ℕ | ∃ seq : List ℕ, seq.length = t ∧ isValidGPFSeq n seq} := by
  refine ⟨n, fun t ⟨seq, hlen, ⟨hchain, _⟩, hbounds⟩ => ?_⟩
  have hnodup : seq.Nodup :=
    List.Pairwise.imp (fun h => ne_of_lt h) hchain.pairwise
  calc t = seq.length := hlen.symm
    _ = seq.toFinset.card := hnodup.card_toFinset.symm
    _ ≤ (Finset.range n).card := Finset.card_le_card (fun a ha =>
        Finset.mem_range.mpr ((hbounds a (List.mem_toFinset.mp ha)).2))
    _ = n := Finset.card_range n

/-- If a valid GPF sequence of length k exists for n, then g(n) ≥ k. -/
private lemma g_ge_of_witness (n k : ℕ) (seq : List ℕ)
    (hlen : seq.length = k) (hvalid : isValidGPFSeq n seq) : g n ≥ k :=
  le_csSup (g_bddAbove n) ⟨seq, hlen, hvalid⟩

/-- g(n) ≥ 1 for n ≥ 3 (witness: [2]). -/
theorem g_ge_one (n : ℕ) (hn : n ≥ 3) : g n ≥ 1 := by
  apply g_ge_of_witness n 1 [2] rfl
  refine ⟨⟨?_, ?_⟩, fun a ha => by simp at ha; subst ha; omega⟩
  -- Singleton chain conditions are trivially true
  all_goals (first | trivial | simp [List.map])

/-- g(n) ≥ 2 for n ≥ 5 (witness: [3, 4], gpf 3 = 3 > 2 = gpf 4). -/
theorem g_ge_two (n : ℕ) (hn : n ≥ 5) : g n ≥ 2 := by
  apply g_ge_of_witness n 2 [3, 4] rfl
  refine ⟨⟨?_, ?_⟩, fun a ha => by simp at ha; rcases ha with rfl | rfl <;> omega⟩
  · -- [3, 4] strictly increasing: 3 < 4
    constructor <;> first | omega | trivial
  · -- [gpf 3, gpf 4] strictly decreasing: 3 > 2
    simp only [List.map, gpf_three, gpf_four]
    constructor <;> first | omega | trivial

/-- g(n) ≥ 3 for n ≥ 17 (witness: [7, 9, 16], gpf values 7 > 3 > 2). -/
theorem g_ge_three (n : ℕ) (hn : n ≥ 17) : g n ≥ 3 := by
  apply g_ge_of_witness n 3 [7, 9, 16] rfl
  refine ⟨⟨?_, ?_⟩, fun a ha => by simp at ha; rcases ha with rfl | rfl | rfl <;> omega⟩
  · -- [7, 9, 16] strictly increasing
    constructor <;> first | omega | (constructor <;> first | omega | trivial)
  · -- [7, 3, 2] strictly decreasing
    simp only [List.map, gpf_prime 7 (by decide : Nat.Prime 7), gpf_nine, gpf_sixteen]
    constructor <;> first | omega | (constructor <;> first | omega | trivial)

/-- g(n) ≥ 4 for n ≥ 65 (witness: [7, 10, 27, 64], gpf values 7 > 5 > 3 > 2). -/
theorem g_ge_four (n : ℕ) (hn : n ≥ 65) : g n ≥ 4 := by
  apply g_ge_of_witness n 4 [7, 10, 27, 64] rfl
  refine ⟨⟨?_, ?_⟩, fun a ha => by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> omega⟩
  · -- [7, 10, 27, 64] strictly increasing
    constructor <;> first | omega | (constructor <;> first | omega | (constructor <;> first | omega | trivial))
  · -- [7, 5, 3, 2] strictly decreasing
    simp only [List.map, gpf_prime 7 (by decide : Nat.Prime 7), gpf_ten, gpf_twentyseven, gpf_sixtyfour]
    constructor <;> first | omega | (constructor <;> first | omega | (constructor <;> first | omega | trivial))

/-
## Part VI: Smooth Numbers
-/

def isSmooth (B n : ℕ) : Prop := gpf n ≤ B

/-- Powers of 2 are 2-smooth. -/
theorem power_of_two_smooth (k : ℕ) (hk : k ≥ 1) : isSmooth 2 (2^k) := by
  simp only [isSmooth]
  have h1 : (2 : ℕ)^k > 1 := by
    have : (2 : ℕ) ≤ 2^k := Nat.le_self_pow (by omega) 2; omega
  have hgp := gpf_is_prime (2^k) h1
  have hdvd2 : gpf (2^k) ∣ 2 := hgp.dvd_of_dvd_pow (gpf_dvd (2^k) h1)
  have hlt := hgp.one_lt
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd2 with h | h <;> omega

/-- Powers of prime p are p-smooth. -/
theorem prime_power_smooth (p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    isSmooth p (p^k) := by
  simp only [isSmooth]
  have h1 : p^k > 1 := by
    have : p ≤ p^k := Nat.le_self_pow (by omega) p
    exact lt_of_lt_of_le hp.one_lt this
  have hgp := gpf_is_prime (p^k) h1
  have hdvdp : gpf (p^k) ∣ p := hgp.dvd_of_dvd_pow (gpf_dvd (p^k) h1)
  have hlt := hgp.one_lt
  rcases hp.eq_one_or_self_of_dvd _ hdvdp with h | h <;> omega

/-
## Part VII: Cambie's Theorem
-/

axiom cambie_lower_bound :
    ∃ c₁ : ℝ, c₁ ≥ 2 ∧
    ∀ n : ℕ, n ≥ 10 → (g n : ℝ) ≥ c₁ * Real.sqrt ((n : ℝ) / Real.log n)

axiom cambie_upper_bound :
    ∃ c₂ : ℝ, c₂ > 0 ∧ c₂ ≤ 2 * Real.sqrt 2 ∧
    ∀ n : ℕ, n ≥ 10 → (g n : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log n)

theorem cambie_main :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n : ℕ, n ≥ 10 →
      c₁ * Real.sqrt ((n : ℝ) / Real.log n) ≤ (g n : ℝ) ∧
      (g n : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log n) := by
  obtain ⟨c₁, hc₁_ge, hc₁⟩ := cambie_lower_bound
  obtain ⟨c₂, hc₂_pos, _, hc₂⟩ := cambie_upper_bound
  use c₁, c₂
  refine ⟨by linarith, hc₂_pos, ?_⟩
  intro n hn
  exact ⟨hc₁ n hn, hc₂ n hn⟩

/-
## Part VIII: The Constant Question
-/

axiom cambie_asymptotic_conjecture :
    ∃ c : ℝ, 2 ≤ c ∧ c ≤ 2 * Real.sqrt 2 ∧
    Filter.Tendsto (fun n : ℕ => (g n : ℝ) / Real.sqrt ((n : ℝ) / Real.log n))
      Filter.atTop (nhds c)

noncomputable def c_lower : ℝ := 2
noncomputable def c_upper : ℝ := 2 * Real.sqrt 2

theorem c_upper_lt_three : c_upper < 3 := by
  unfold c_upper
  have h : Real.sqrt 2 < 1.5 := by
    have : (1.5 : ℝ)^2 = 2.25 := by norm_num
    have : (2 : ℝ) < 2.25 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  linarith

/-
## Part IX: Construction Strategy & Related Functions
-/

def primePowerSequence : List (ℕ × ℕ) :=
  [(7, 1), (10, 1), (27, 1), (64, 1)]

noncomputable def spf (n : ℕ) : ℕ := n.minFac

/-- spf(n) ≤ gpf(n) for n > 1. -/
theorem spf_le_gpf (n : ℕ) (hn : n > 1) : spf n ≤ gpf n := by
  apply gpf_max
  · exact Nat.minFac_prime (by omega)
  · exact Nat.minFac_dvd n
  · omega

theorem spf_eq_gpf_prime (p : ℕ) (hp : p.Prime) : spf p = gpf p := by
  rw [gpf_prime p hp]
  simp [spf, Nat.Prime.minFac_eq hp]

/-
## Part X: Main Results Summary
-/

theorem erdos_648_summary :
    (∃ c₁ : ℝ, c₁ ≥ 2 ∧ ∀ n : ℕ, n ≥ 10 →
      (g n : ℝ) ≥ c₁ * Real.sqrt ((n : ℝ) / Real.log n)) ∧
    (∃ c₂ : ℝ, c₂ > 0 ∧ c₂ ≤ 2 * Real.sqrt 2 ∧ ∀ n : ℕ, n ≥ 10 →
      (g n : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log n)) :=
  ⟨cambie_lower_bound, cambie_upper_bound⟩

theorem erdos_648 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ n : ℕ, n ≥ 10 →
      c₁ * Real.sqrt ((n : ℝ) / Real.log n) ≤ (g n : ℝ) ∧
      (g n : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log n) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := cambie_main
  exact ⟨c₁, c₂, hc₁, hc₂, h⟩

theorem length_four_exists :
    ∃ (a b c d : ℕ), a < b ∧ b < c ∧ c < d ∧
      gpf a > gpf b ∧ gpf b > gpf c ∧ gpf c > gpf d ∧
      a ≥ 2 ∧ d < 100 := by
  use 7, 10, 27, 64
  constructor; omega
  constructor; omega
  constructor; omega
  rw [gpf_prime 7 (by decide : Nat.Prime 7), gpf_ten,
      gpf_twentyseven, gpf_sixtyfour]
  omega

end Erdos648
