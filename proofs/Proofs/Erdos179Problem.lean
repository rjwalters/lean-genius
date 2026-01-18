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

  Tags: additive-combinatorics, arithmetic-progressions, supersaturation
-/

import Mathlib

namespace Erdos179

open Finset

/-!
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

/-!
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
      use N^2 + 1  -- Trivial upper bound
      intro A hN hcount
      sorry

/-- The property that F_k(N, ℓ) captures. -/
def SupersaturationProperty (k N ℓ M : ℕ) : Prop :=
  ∀ A : Finset ℕ, A.card = N → countAPs A k ≥ M → ContainsAP A ℓ

/-!
## Part III: Trivial Bounds

Basic observations about F_k(N, ℓ).
-/

/-- Lower bound: A set with no ℓ-AP can have many k-APs. -/
axiom F_lower_bound (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    ∀ᶠ N in Filter.atTop, (F k N ℓ : ℝ) ≥ N^(1.99 : ℝ)

/-- Upper bound: F_k(N, ℓ) ≤ N² (trivially). -/
theorem F_upper_trivial (k N ℓ : ℕ) (hk : k ≥ 3) (hℓ : ℓ > k) :
    F k N ℓ ≤ N^2 := by
  sorry

/-- A random set perspective: expected k-APs in random subset of [N]. -/
axiom random_set_APs (k N : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    sorry -- Expected number of k-APs is Θ(p^k · N²)

/-!
## Part IV: Erdős's Questions

The two specific questions Erdős asked.
-/

/-- Question 1: Is F₃(N, 4) = o(N²)? -/
def Question1 : Prop :=
  ∀ ε > 0, ∀ᶠ N in Filter.atTop, (F 3 N 4 : ℝ) ≤ ε * N^2

/-- Question 2: For ℓ > 3, does log F₃(N, ℓ) / log N → 2? -/
def Question2 : Prop :=
  ∀ ℓ > 3, Filter.Tendsto
    (fun N => Real.log (F 3 N ℓ) / Real.log N)
    Filter.atTop (nhds 2)

/-!
## Part V: Fox-Pohoata Theorem (2020)

The breakthrough result solving Erdős's questions.
-/

/-- **Fox-Pohoata Theorem** (2020):
    For all fixed 1 ≤ k < ℓ, F_k(N, ℓ) = N^{2-o(1)}.

    More precisely: F_k(N, ℓ) ≤ N² / (log log N)^{C_ℓ} for some C_ℓ > 0. -/
axiom fox_pohoata_theorem (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in Filter.atTop,
      (F k N ℓ : ℝ) ≤ N^2 / (Real.log (Real.log N))^C

/-- Corollary: Question 1 is TRUE. -/
theorem question1_solved : Question1 := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := fox_pohoata_theorem 3 4 (by norm_num) (by norm_num)
  filter_upwards [hbound] with N hN
  calc (F 3 N 4 : ℝ) ≤ N^2 / (Real.log (Real.log N))^C := hN
    _ ≤ ε * N^2 := by sorry  -- For large N, (log log N)^C > 1/ε

/-- Corollary: Question 2 is TRUE. -/
theorem question2_solved : Question2 := by
  intro ℓ hℓ
  sorry  -- Follows from fox_pohoata_theorem

/-!
## Part VI: Leng-Sah-Sawhney Improvement (2024)

The state-of-the-art bound.
-/

/-- **Leng-Sah-Sawhney** (2024): Improved bound with exp factor.
    F_k(N, ℓ) ≤ N² / exp((log log N)^{c_ℓ}) -/
axiom leng_sah_sawhney (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      (F k N ℓ : ℝ) ≤ N^2 / Real.exp ((Real.log (Real.log N))^c)

/-- This is a significant improvement over Fox-Pohoata. -/
theorem improvement_significant :
    ∀ C c : ℝ, C > 0 → c > 0 → ∀ᶠ N in Filter.atTop,
      Real.exp ((Real.log (Real.log N))^c) > (Real.log (Real.log N))^C := by
  sorry

/-!
## Part VII: Connection to Szemerédi's Theorem

The relationship to the famous density theorem.
-/

/-- Szemerédi's theorem: Sets with positive density contain long APs. -/
axiom szemeredi_theorem (ℓ : ℕ) (hℓ : ℓ ≥ 3) :
    ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A : Finset (Fin N),
      (A.card : ℝ) ≥ δ * N → ContainsAP (A.map (Fin.valEmbedding)) ℓ

/-- F_k(N, ℓ) measures supersaturation beyond Szemerédi. -/
def SzemerediImplication : Prop :=
  ∀ ℓ ≥ 3, ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀,
    F 3 N ℓ ≤ (δ * N : ℝ)^2 / 4  -- Rough bound from density

/-- Dense sets have many 3-APs by counting. -/
axiom dense_sets_many_3APs (A : Finset ℕ) (N : ℕ) (hN : A.card = N) :
    (countAPs A 3 : ℝ) ≥ sorry -- Lower bound in terms of density

/-!
## Part VIII: Roth's Theorem Connection

The k = 3 case relates to Roth's theorem.
-/

/-- Roth's theorem: No 3-AP-free set has positive density. -/
axiom roth_theorem :
    ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A : Finset (Fin N),
      (A.card : ℝ) ≥ δ * N → ContainsAP (A.map (Fin.valEmbedding)) 3

/-- Behrend's construction: 3-AP-free sets of size N / exp(c√log N). -/
axiom behrend_construction :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      ∃ A : Finset (Fin N), ¬ContainsAP (A.map (Fin.valEmbedding)) 3 ∧
        (A.card : ℝ) ≥ N / Real.exp (c * Real.sqrt (Real.log N))

/-- AP-free sets can still have many 2-APs (trivially, all pairs). -/
theorem AP_free_has_2APs (A : Finset ℕ) (hA : ¬ContainsAP A 3) :
    countAPs A 2 = A.card.choose 2 := by
  sorry  -- Every pair is a 2-AP

/-!
## Part IX: Special Cases

Specific values and asymptotics.
-/

/-- For k = 2, every set has k-APs, so F₂(N, ℓ) is well-defined. -/
theorem F_2_well_defined (N ℓ : ℕ) (hℓ : ℓ ≥ 3) (hN : N ≥ ℓ) :
    F 2 N ℓ ≤ N.choose 2 := by
  sorry

/-- The exponent 2 is correct: F_k(N, ℓ) = Θ(N²) in log scale. -/
theorem exponent_is_2 (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ > k) :
    Filter.Tendsto (fun N => Real.log (F k N ℓ) / Real.log N)
      Filter.atTop (nhds 2) := by
  sorry

/-!
## Part X: Main Results

Erdős Problem #179 is SOLVED.
-/

/-- **Erdős Problem #179: SOLVED**

    Both questions are answered affirmatively:
    1. F₃(N, 4) = o(N²) ✓
    2. lim log F₃(N, ℓ) / log N = 2 for all ℓ > 3 ✓

    The supersaturation function F_k(N, ℓ) = N^{2-o(1)}.
    Best known: F_k(N, ℓ) ≤ N² / exp((log log N)^c). -/
theorem erdos_179 : Question1 ∧ Question2 :=
  ⟨question1_solved, question2_solved⟩

/-- The answer: both questions have affirmative answers. -/
def erdos_179_answer : String :=
  "YES to both: F₃(N,4) = o(N²) and lim log F₃(N,ℓ)/log N = 2"

#check erdos_179
#check fox_pohoata_theorem
#check leng_sah_sawhney

end Erdos179
