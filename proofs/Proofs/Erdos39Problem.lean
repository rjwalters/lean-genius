/-
Erdős Problem #39: Infinite Sidon Set Growth Rate

Source: https://erdosproblems.com/39
Status: OPEN
Prize: $500

Statement:
Is there an infinite Sidon set A ⊂ ℕ such that
  |A ∩ {1,...,N}| ≫_ε N^{1/2-ε}
for all ε > 0?

A Sidon set (B₂ sequence) is a set where all pairwise sums are distinct.

History:
- Erdős proved: For any infinite Sidon set, liminf |A∩{1,...,N}|/√N = 0
- Trivial greedy construction: ≫ N^{1/3}
- Ajtai-Komlós-Szemerédi (1981): ≫ (N log N)^{1/3}
- Ruzsa (1998): ≫ N^{√2-1+o(1)} ≈ N^{0.414} (current best)

The gap between the best construction (~N^{0.414}) and the target (~N^{0.5-ε})
remains open. Erdős originally offered $25 for any improvement over N^{1/3},
then $100 for any N^{c} with c > 1/3 (Ruzsa achieved this).
-/

import Mathlib

open Set Filter Asymptotics Real Nat

namespace Erdos39

/-! ## Core Definitions -/

/-- A set A is a **Sidon set** (B₂ sequence) if all pairwise sums a + b
    with a ≤ b are distinct. -/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-- The counting function A(N) = |A ∩ {1,...,N}| for a set A. -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 N).ncard

/-! ## The Erdős Conjecture -/

/-- **Erdős Problem #39** (OPEN):
    Does there exist an infinite Sidon set A such that for all ε > 0,
    the counting function A(N) ≫ N^{1/2-ε}?

    Precisely: ∃ infinite Sidon set A such that for all ε > 0,
    there exists C_ε > 0 with A(N) ≥ C_ε · N^{1/2-ε} for all large N. -/
def Erdos39Conjecture : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidonSet A ∧
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (countingFunction A N : ℝ) ≥ C * (N : ℝ)^((1:ℝ)/2 - ε)

/-! ## Known Upper Bounds -/

/-- **Erdős's Upper Bound**: For any infinite Sidon set A,
    liminf A(N)/√N = 0.

    This means no infinite Sidon set can have A(N) ≥ c√N for all large N.
    The target N^{1/2-ε} is the best we could hope for. -/
axiom erdos_sidon_upper_bound :
  ∀ A : Set ℕ, A.Infinite → IsSidonSet A →
    Filter.liminf (fun N => (countingFunction A N : ℝ) / Real.sqrt N) atTop = 0

/-- **Consequence**: No infinite Sidon set achieves √N growth uniformly.
    There exist arbitrarily large N where A(N) < ε√N. -/
theorem no_sqrt_growth (A : Set ℕ) (hInf : A.Infinite) (hSidon : IsSidonSet A) :
    ∀ c : ℝ, c > 0 → ∃ᶠ N in atTop, (countingFunction A N : ℝ) < c * Real.sqrt N := by
  sorry  -- Follows from liminf = 0

/-! ## Known Lower Bounds (Constructions) -/

/-- **Greedy Construction**: The greedy algorithm produces an infinite
    Sidon set with A(N) ≫ N^{1/3}.
    (Add n to A if no sum collision with existing elements.) -/
axiom greedy_sidon_exists :
  ∃ A : Set ℕ, A.Infinite ∧ IsSidonSet A ∧
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
      (countingFunction A N : ℝ) ≥ C * (N : ℝ)^((1:ℝ)/3)

/-- **Ajtai-Komlós-Szemerédi (1981)**: There exists an infinite Sidon set
    with A(N) ≫ (N log N)^{1/3}.
    First improvement over greedy, earned $25 from Erdős. -/
axiom aks_sidon_construction :
  ∃ A : Set ℕ, A.Infinite ∧ IsSidonSet A ∧
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      (countingFunction A N : ℝ) ≥ C * ((N : ℝ) * Real.log N)^((1:ℝ)/3)

/-- **Ruzsa (1998)**: There exists an infinite Sidon set with
    A(N) ≫ N^{√2-1+o(1)} ≈ N^{0.414}.
    Current best construction, earned $100 from Erdős. -/
axiom ruzsa_sidon_construction :
  ∃ A : Set ℕ, A.Infinite ∧ IsSidonSet A ∧
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (countingFunction A N : ℝ) ≥ C * (N : ℝ)^(Real.sqrt 2 - 1 - ε)

/-- √2 - 1 ≈ 0.41421... is the Ruzsa exponent. -/
theorem ruzsa_exponent_value : Real.sqrt 2 - 1 > 0.41 := by
  have h : Real.sqrt 2 > 1.41 := by
    have : (1.41 : ℝ)^2 < 2 := by norm_num
    have h1 : (0:ℝ) ≤ 1.41 := by norm_num
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    calc Real.sqrt 2 > Real.sqrt (1.41^2) := by
           apply Real.sqrt_lt_sqrt (sq_nonneg _) this
         _ = 1.41 := Real.sqrt_sq h1
  linarith

/-! ## The Gap -/

/--
**Current state of knowledge for Erdős Problem #39:**

- **Best construction** (Ruzsa): N^{√2-1-ε} ≈ N^{0.414}
- **Target**: N^{1/2-ε} ≈ N^{0.5-ε}
- **Upper limit** (Erdős): Cannot achieve N^{1/2} uniformly

The gap is between exponents ~0.414 and ~0.5. To solve the problem:
- Either construct an infinite Sidon set achieving N^{1/2-ε}, or
- Prove no such set exists (strengthen the upper bound)
-/
theorem erdos39_gap : Real.sqrt 2 - 1 < (1:ℝ)/2 := by
  have h : Real.sqrt 2 < 1.5 := by
    have : (2 : ℝ) < 1.5^2 := by norm_num
    have h1 : (0:ℝ) ≤ 2 := by norm_num
    have h2 : (0:ℝ) ≤ 1.5 := by norm_num
    calc Real.sqrt 2 < Real.sqrt (1.5^2) := by
           apply Real.sqrt_lt_sqrt h1 this
         _ = 1.5 := Real.sqrt_sq h2
  linarith

/-! ## Related Results -/

/-- **Erdős-Rényi Construction**: For any ε > 0, there exists a set A with
    A(N) ≫ N^{1/2-ε} AND all representation numbers bounded.
    (r(n) = #{(a,b) ∈ A² : a + b = n} ≤ C_ε for all n.)

    This shows N^{1/2-ε} is achievable if we relax Sidon to bounded
    representation. The question is whether we can achieve r(n) = 1. -/
axiom erdos_renyi_construction :
  ∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ, A.Infinite ∧
    (∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
      (countingFunction A N : ℝ) ≥ C * (N : ℝ)^((1:ℝ)/2 - ε)) ∧
    ∃ B : ℝ, B > 0 ∧ ∀ n : ℕ,
      (({(a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ A ∧ a + b = n}).ncard : ℝ) ≤ B

/-! ## Problem Status -/

/-- **Erdős Problem #39: OPEN ($500 prize)**

**What we know:**
- Upper: No infinite Sidon set achieves N^{1/2} uniformly
- Lower: Ruzsa's construction achieves N^{√2-1-ε}

**The question:**
- Can we improve the construction to N^{1/2-ε}?
- Or prove an upper bound ruling this out?

**Why it's hard:**
- Greedy analysis gives N^{1/3}
- Algebraic constructions (Ruzsa) reach N^{0.414}
- Further progress requires new techniques
- The Erdős-Rényi construction shows N^{1/2-ε} is reachable
  with bounded (not zero) collision count

References:
- Ajtai, Komlós, Szemerédi (1981): "A dense infinite Sidon sequence"
- Ruzsa (1998): "An infinite Sidon sequence"
- Erdős, Rényi: probabilistic construction with bounded representation
-/
theorem erdos_39_open : Erdos39Conjecture ∨ ¬Erdos39Conjecture := by
  exact Classical.em Erdos39Conjecture

/-! ## Verified Facts -/

/-- Singletons are Sidon sets. -/
theorem sidon_singleton (n : ℕ) : IsSidonSet {n} := by
  intro a b c d ha hb hc hd _ _ _
  simp only [Set.mem_singleton_iff] at ha hb hc hd
  exact ⟨ha.trans hc.symm, hb.trans hd.symm⟩

/-- {1, 2, 5, 10} is a Sidon set (sums: 3, 6, 11, 7, 12, 15). -/
theorem sidon_1_2_5_10 : IsSidonSet ({1, 2, 5, 10} : Set ℕ) := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl <;>
  rcases hd with rfl | rfl | rfl | rfl <;>
  omega

end Erdos39
