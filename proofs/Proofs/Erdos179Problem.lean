/-
Erdős Problem #179: Arithmetic Progression Supersaturation

Source: https://erdosproblems.com/179
Status: SOLVED (Fox-Pohoata 2020, Leng-Sah-Sawhney 2024)

Statement:
Let 1 ≤ k < ℓ be integers. Define F_k(N, ℓ) as the minimum number such that
every set A ⊆ ℕ of size N containing at least F_k(N, ℓ) many k-term APs
must contain an ℓ-term AP.

Questions:
1. Is F₃(N, 4) = o(N²)?
2. For every ℓ > 3, is lim_{N→∞} log F₃(N, ℓ) / log N = 2?

Answer: YES to both. Fox-Pohoata proved F_k(N, ℓ) = N^{2-o(1)}.

Key Results:
- Fox-Pohoata (2020): F_k(N, ℓ) ≤ N² / (log log N)^{C_ℓ}
- Leng-Sah-Sawhney (2024): F_k(N, ℓ) ≤ N² / exp((log log N)^{c_ℓ})

References:
- Fox & Pohoata (2020): arXiv:1908.09905
- Leng, Sah & Sawhney (2024): arXiv:2402.17995
- Szemerédi (1975): Acta Arithmetica 27, 199–245
- Roth (1953): J. London Math. Soc. 28, 104–109
- Behrend (1946): Proc. Nat. Acad. Sci. 32, 331–332

Tags: additive-combinatorics, arithmetic-progressions, supersaturation, solved
-/

import Mathlib

open scoped Classical

namespace Erdos179

open Finset

/-
## Part I: Arithmetic Progressions

A k-term arithmetic progression is a sequence a, a+d, a+2d, ..., a+(k-1)d.
-/

/-- An arithmetic progression of length k with first term a and common difference d. -/
def arithmeticProgression (a d : ℕ) (k : ℕ) : Finset ℕ :=
  Finset.image (fun i => a + i * d) (Finset.range k)

/-- A set contains a k-term AP if some AP of length k is a subset. -/
def ContainsAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ arithmeticProgression a d k ⊆ A

/-- Count of k-term APs in a set A. -/
noncomputable def countAPs (A : Finset ℕ) (k : ℕ) : ℕ :=
  (A.powerset.filter fun S => ∃ a d, d > 0 ∧ S = arithmeticProgression a d k).card

/-
## Part II: The Supersaturation Function F_k(N, ℓ)

F_k(N, ℓ) is the threshold: having this many k-APs forces an ℓ-AP.
-/

/-- F_k(N, ℓ): minimum number of k-APs that forces an ℓ-AP.
    Every set of size N with ≥ F_k(N, ℓ) many k-APs contains an ℓ-AP. -/
noncomputable def F (k N ℓ : ℕ) : ℕ :=
  Nat.find (supersaturation_exists k N ℓ)
  where
    supersaturation_exists (k N ℓ : ℕ) : ∃ M, ∀ A : Finset ℕ,
        A.card = N → countAPs A k ≥ M → ContainsAP A ℓ := by
      -- Trivial existence: at most `2 ^ N` subsets of `A` exist, so a set of size
      -- `N` can never contain `2 ^ N + 1` many k-APs; the hypothesis is vacuous.
      refine ⟨2 ^ N + 1, ?_⟩
      intro A hN hcount
      exfalso
      have hle : countAPs A k ≤ 2 ^ N := by
        have h1 : countAPs A k ≤ A.powerset.card := by
          unfold countAPs
          exact Finset.card_filter_le _ _
        rwa [Finset.card_powerset, hN] at h1
      omega

/-- The property that F_k(N, ℓ) captures. -/
def SupersaturationProperty (k N ℓ M : ℕ) : Prop :=
  ∀ A : Finset ℕ, A.card = N → countAPs A k ≥ M → ContainsAP A ℓ

/-
## Part III: Trivial Bounds

Basic observations about F_k(N, ℓ).
-/

/-- Lower bound: A set with no ℓ-AP can have many k-APs.
    From Behrend-type constructions, the lower bound is at least N^{1.99}. -/
axiom F_lower_bound (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    ∀ᶠ N in Filter.atTop, (F k N ℓ : ℝ) ≥ N^(1.99 : ℝ)

/-- Upper bound: F_k(N, ℓ) ≤ N² (trivially, since a set of size N has at most N² k-APs). -/
theorem F_upper_trivial (k N ℓ : ℕ) (hk : k ≥ 3) (hℓ : ℓ > k) :
    F k N ℓ ≤ N^2 := by
  sorry

/-
## Part IV: Erdős's Questions

The two specific questions Erdős asked.
-/

/-- Question 1: Is F₃(N, 4) = o(N²)?
    Formalized: for every ε > 0, eventually F₃(N, 4) ≤ ε·N². -/
def Question1 : Prop :=
  ∀ ε > 0, ∀ᶠ N in Filter.atTop, (F 3 N 4 : ℝ) ≤ ε * N^2

/-- Question 2: For ℓ > 3, does log F₃(N, ℓ) / log N → 2?
    Formalized: the log ratio converges to 2 in the Filter.atTop sense. -/
def Question2 : Prop :=
  ∀ ℓ > 3, Filter.Tendsto
    (fun N => Real.log (F 3 N ℓ) / Real.log N)
    Filter.atTop (nhds 2)

/-
## Part V: Fox-Pohoata Theorem (2020)

The breakthrough result solving Erdős's questions.
-/

/-- **Fox-Pohoata Theorem** (2020):
    For all fixed 1 ≤ k < ℓ, F_k(N, ℓ) = N^{2-o(1)}.

    More precisely: F_k(N, ℓ) ≤ N² / (log log N)^{C_ℓ} for some C_ℓ > 0.

    The proof uses the inverse theorem for Gowers uniformity norms: sets with
    many k-APs must have large Gowers norms, which forces structured components
    that contain ℓ-APs. -/
axiom fox_pohoata_theorem (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in Filter.atTop,
      (F k N ℓ : ℝ) ≤ N^2 / (Real.log (Real.log N))^C

/-- Corollary: Question 1 is TRUE.
    Proof sketch: Fox-Pohoata gives F₃(N,4) ≤ N²/(log log N)^C.
    For large N, (log log N)^C → ∞, so F₃(N,4)/N² → 0. -/
theorem question1_solved : Question1 := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := fox_pohoata_theorem 3 4 (by norm_num) (by norm_num)
  filter_upwards [hbound] with N hN
  calc (F 3 N 4 : ℝ) ≤ N^2 / (Real.log (Real.log N))^C := hN
    _ ≤ ε * N^2 := by sorry  -- For large N, (log log N)^C > 1/ε

/-- Corollary: Question 2 is TRUE.
    The log exponent converges to 2 by combining the Fox-Pohoata upper bound
    and the Behrend lower bound. -/
theorem question2_solved : Question2 := by
  intro ℓ hℓ
  sorry  -- Follows from fox_pohoata_theorem and F_lower_bound

/-
## Part VI: Leng-Sah-Sawhney Improvement (2024)

The state-of-the-art bound, significantly stronger than Fox-Pohoata.
-/

/-- **Leng-Sah-Sawhney** (2024): Improved bound with exponential denominator.
    F_k(N, ℓ) ≤ N² / exp((log log N)^{c_ℓ})

    This improves on Fox-Pohoata by replacing the polynomial (log log N)^C
    with the much larger exp((log log N)^c). The proof builds on their
    breakthrough improvements to Szemerédi's theorem. -/
axiom leng_sah_sawhney (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      (F k N ℓ : ℝ) ≤ N^2 / Real.exp ((Real.log (Real.log N))^c)

/-- The Leng-Sah-Sawhney bound strictly dominates Fox-Pohoata for large N:
    exp((log log N)^c) grows faster than any fixed power (log log N)^C. -/
theorem improvement_significant :
    ∀ C c : ℝ, C > 0 → c > 0 → ∀ᶠ N in Filter.atTop,
      Real.exp ((Real.log (Real.log N))^c) > (Real.log (Real.log N))^C := by
  sorry

/-
## Part VII: Connection to Szemerédi's Theorem

The relationship to the celebrated density theorem.
-/

/-- Szemerédi's theorem (1975): Sets with positive upper density contain long APs.
    This is the density version: a set of density ≥ δ in {1,...,N} contains an ℓ-AP
    for all sufficiently large N. -/
axiom szemeredi_theorem (ℓ : ℕ) (hℓ : ℓ ≥ 3) :
    ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A : Finset (Fin N),
      (A.card : ℝ) ≥ δ * N → ContainsAP (A.map (Fin.valEmbedding)) ℓ

/-- F_k(N, ℓ) refines Szemerédi: instead of density, it asks how many short APs
    suffice to force a long AP. -/
def SzemerediImplication : Prop :=
  ∀ ℓ ≥ 3, ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀,
    F 3 N ℓ ≤ (δ * N : ℝ)^2 / 4  -- Rough bound from density

/-
## Part VIII: Roth's Theorem and Behrend's Construction

The k = 3 case and extremal examples.
-/

/-- Roth's theorem (1953): No 3-AP-free set has positive upper density. -/
axiom roth_theorem :
    ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A : Finset (Fin N),
      (A.card : ℝ) ≥ δ * N → ContainsAP (A.map (Fin.valEmbedding)) 3

/-- Behrend's construction (1946): 3-AP-free sets of size N / exp(c√log N) exist.
    These show that the Szemerédi/Roth bounds cannot be much better than logarithmic. -/
axiom behrend_construction :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      ∃ A : Finset (Fin N), ¬ContainsAP (A.map (Fin.valEmbedding)) 3 ∧
        (A.card : ℝ) ≥ N / Real.exp (c * Real.sqrt (Real.log N))

/-- A 2-term AP is just the (unordered) pair of its two entries. -/
theorem arithmeticProgression_two (a d : ℕ) :
    arithmeticProgression a d 2 = {a, a + d} := by
  ext x
  simp only [arithmeticProgression, Finset.mem_image, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · left; ring
    · right; ring
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by ring⟩
    · exact ⟨1, by norm_num, by ring⟩

/-- Every pair of distinct elements forms a 2-AP, so the number of 2-term APs in
    any set is exactly `C(|A|, 2)`. (The 3-AP-free hypothesis is not needed: the
    identity holds for every finite set.) -/
theorem AP_free_has_2APs (A : Finset ℕ) (_hA : ¬ContainsAP A 3) :
    countAPs A 2 = A.card.choose 2 := by
  have key : (A.powerset.filter fun S => ∃ a d, d > 0 ∧ S = arithmeticProgression a d 2)
      = A.powersetCard 2 := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hSA, a, d, hd, rfl⟩
      exact ⟨hSA, by rw [arithmeticProgression_two, Finset.card_pair (by omega)]⟩
    · rintro ⟨hSA, hcard⟩
      refine ⟨hSA, ?_⟩
      rw [Finset.card_eq_two] at hcard
      obtain ⟨x, y, hxy, rfl⟩ := hcard
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · refine ⟨x, y - x, by omega, ?_⟩
        rw [arithmeticProgression_two]
        have : x + (y - x) = y := by omega
        rw [this]
      · refine ⟨y, x - y, by omega, ?_⟩
        rw [arithmeticProgression_two]
        have : y + (x - y) = x := by omega
        rw [this, Finset.pair_comm]
  have hcard : countAPs A 2 = (A.powersetCard 2).card := by
    unfold countAPs
    rw [key]
  rw [hcard, Finset.card_powersetCard]

/-
## Part IX: Special Cases and Asymptotics
-/

/-- For k = 2, every set of size N has exactly C(N,2) 2-APs (every pair is a 2-AP),
    so F₂(N, ℓ) is at most C(N, 2). -/
theorem F_2_well_defined (N ℓ : ℕ) (hℓ : ℓ ≥ 3) (hN : N ≥ ℓ) :
    F 2 N ℓ ≤ N.choose 2 := by
  sorry

/-- The exponent of F_k(N, ℓ) is exactly 2 in logarithmic scale.
    Combining Fox-Pohoata (upper) and F_lower_bound (lower), the log ratio → 2. -/
theorem exponent_is_2 (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    Filter.Tendsto (fun N => Real.log (F k N ℓ) / Real.log N)
      Filter.atTop (nhds 2) := by
  sorry

/-
## Part X: Main Results

Erdős Problem #179 is SOLVED.
-/

/-- **Erdős Problem #179: SOLVED**

    Both questions are answered affirmatively:
    1. F₃(N, 4) = o(N²) ✓
    2. lim log F₃(N, ℓ) / log N = 2 for all ℓ > 3 ✓

    Best known bound (Leng-Sah-Sawhney 2024):
    F_k(N, ℓ) ≤ N² / exp((log log N)^c). -/
theorem erdos_179 : Question1 ∧ Question2 :=
  ⟨question1_solved, question2_solved⟩

/-- Summary: both of Erdős's questions about AP supersaturation have affirmative answers. -/
def erdos_179_answer : String :=
  "YES to both: F₃(N,4) = o(N²) and lim log F₃(N,ℓ)/log N = 2"

#check erdos_179
#check fox_pohoata_theorem
#check leng_sah_sawhney

end Erdos179
