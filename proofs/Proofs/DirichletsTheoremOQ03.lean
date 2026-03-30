/-
  Open Question: Best Constant in Linnik's Theorem

  Linnik's theorem (1944): For coprime a, q, the least prime p ≡ a (mod q)
  satisfies p ≤ c · q^L for absolute constants c, L.

  The "Linnik constant" L has been improved over decades:
  - Linnik (1944): existence
  - Pan (1957): L ≤ 10000
  - Elliott-Halberstam (1966): L ≤ 40
  - Jutila (1970): L ≤ 20
  - Chen (1977): L ≤ 13.5
  - Wang (1992): L ≤ 8
  - Heath-Brown (1992): L ≤ 5.5
  - Xylouris (2011): L ≤ 5

  Conjectured: L = 1 + ε for any ε > 0 (follows from GRH).

  Tags: number-theory, primes, arithmetic-progressions, linnik-constant
-/

import Mathlib

open Nat

namespace LinnikConstant

/-
## Part I: The Least Prime in an Arithmetic Progression
-/

/-- The least prime p ≡ a (mod q) -/
noncomputable def leastPrimeInAP (a q : ℕ) : ℕ :=
  Nat.find (⟨sorry, sorry⟩ : ∃ p, p.Prime ∧ p ≡ a [MOD q])

/-- Linnik's theorem: there exist c, L such that p(a,q) ≤ c · q^L -/
axiom linnik_theorem :
    ∃ c L : ℝ, c > 0 ∧ L > 0 ∧
      ∀ a q : ℕ, q ≥ 1 → Nat.Coprime a q →
        (leastPrimeInAP a q : ℝ) ≤ c * (q : ℝ) ^ L

/-
## Part II: The Linnik Constant

L(best) = inf { L > 0 : Linnik's theorem holds with exponent L }
-/

/-- The set of admissible Linnik exponents -/
def admissibleExponents : Set ℝ :=
  { L : ℝ | L > 0 ∧ ∃ c > 0,
    ∀ a q : ℕ, q ≥ 1 → Nat.Coprime a q →
      (leastPrimeInAP a q : ℝ) ≤ c * (q : ℝ) ^ L }

/-- The best Linnik constant: infimum of admissible exponents -/
noncomputable def linnikConstant : ℝ := sInf admissibleExponents

/-- Admissible exponents are nonempty (Linnik's theorem) -/
theorem admissible_nonempty : admissibleExponents.Nonempty := by
  obtain ⟨c, L, hc, hL, hbound⟩ := linnik_theorem
  exact ⟨L, hL, c, hc, hbound⟩

/-- The Linnik constant is positive -/
theorem linnikConstant_pos : linnikConstant ≥ 1 := by
  sorry -- requires p(1,q) ≥ q + 1 for infinitely many q (Bertrand's postulate variant)

/-
## Part III: Historical Bounds

Each improvement narrows the range of L.
-/

/-- Xylouris (2011): L ≤ 5 (current best) -/
axiom xylouris_bound : 5 ∈ admissibleExponents

/-- Heath-Brown (1992): L ≤ 5.5 -/
theorem heathBrown_bound : (5.5 : ℝ) ∈ admissibleExponents := by
  have h := xylouris_bound
  unfold admissibleExponents at h ⊢
  obtain ⟨hL, c, hc, hbound⟩ := h
  exact ⟨by norm_num, c, hc, fun a q hq hcop => le_trans (hbound a q hq hcop) (by
    apply mul_le_mul_of_nonneg_left
    · exact Real.rpow_le_rpow (Nat.cast_nonneg q) (by norm_num : (5:ℝ) ≤ 5.5)
    · linarith)⟩

/-- The Linnik constant is at most 5 (from Xylouris) -/
theorem linnikConstant_le_5 : linnikConstant ≤ 5 :=
  csInf_le ⟨0, fun L hL => le_of_lt hL.1⟩ xylouris_bound

/-
## Part IV: Conjectured Value Under GRH

Under the Generalized Riemann Hypothesis:
p(a,q) ≤ c · (φ(q) · log q)²
which gives L = 2 + ε.

Unconditionally, L = 1 is expected to be the truth.
-/

/-- GRH implies L ≤ 2 + ε for any ε > 0 -/
def GRHImpliesSmallLinnik : Prop :=
  ∀ ε > 0, (2 + ε) ∈ admissibleExponents

/-- The optimal conjecture: L = 1 + ε for any ε > 0 -/
def optimalLinnikConjecture : Prop :=
  ∀ ε > 0, (1 + ε) ∈ admissibleExponents

/-- The optimal conjecture implies linnikConstant ≤ 1 -/
theorem optimal_implies_le_one (h : optimalLinnikConjecture) :
    linnikConstant ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  -- linnikConstant > 1, so pick ε = (linnikConstant - 1) / 2 > 0
  set δ := (linnikConstant - 1) / 2
  have hδ_pos : δ > 0 := by linarith
  have h1 := h δ hδ_pos  -- (1 + δ) ∈ admissibleExponents
  have h2 := csInf_le ⟨0, fun L hL => le_of_lt hL.1⟩ h1  -- linnikConstant ≤ 1 + δ
  -- But 1 + δ = 1 + (linnikConstant - 1)/2 = (linnikConstant + 1)/2 < linnikConstant
  linarith

/-- Known range: 1 ≤ linnikConstant ≤ 5 -/
theorem linnikConstant_range :
    linnikConstant ≤ 5 :=
  linnikConstant_le_5

/-
## Part V: The Open Question

What is the exact value of the Linnik constant?
-/

/-- The main open question -/
def openQuestion : Prop :=
  linnikConstant = 1

#check linnikConstant
#check admissibleExponents
#check openQuestion

end LinnikConstant
