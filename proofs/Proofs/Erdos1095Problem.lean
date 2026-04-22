/-
# Erdős Problem #1095: The Erdős-Selfridge Function

Let g(k) > k+1 be the smallest n such that all prime factors of C(n,k)
are greater than k. Estimate g(k).

**Known bounds**:
- Lower: g(k) ≫ exp(c·(log k)²) — Konyagin (1999)
- Upper: g(k) ≤ exp((1+o(1))·k) — Ecklund-Erdős-Selfridge (1974)

**Conjectured**: log g(k) ~ k/log k (Erdős-Lacampagne-Selfridge 1993)

**Concrete values**: g(2)=6, g(3)=7, g(4)=7, g(5)=23.

**References**:
- Ecklund, Erdős, Selfridge (1974): Math. Comp. 28(126), 647–649
- Erdős, Lacampagne, Selfridge (1993): Math. Comp. 61(203), 215–224
- Konyagin (1999): Bull. London Math. Soc. 31(3), 271–277
- https://erdosproblems.com/1095
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Nat Finset Filter Real
open scoped Topology

namespace Erdos1095

/- ## Core Definitions -/

/-- A natural number is **k-rough** if all its prime factors exceed k. -/
def isKRough (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p > k

/-- C(n, k) is **k-rough**: every prime factor of the binomial coefficient exceeds k. -/
def binomIsKRough (n k : ℕ) : Prop :=
  isKRough (Nat.choose n k) k

/- ## The Erdős-Selfridge Function g(k) -/

/-- The **Erdős-Selfridge function** g(k): the smallest n > k+1 such that
C(n,k) is k-rough (all prime factors exceed k).

Axiomatized because existence follows from deep analytic bounds (EES 1974)
and the explicit form of g is determined only by the minimality condition. -/
axiom g : ℕ → ℕ

/-- g(k) > k + 1 by definition. -/
axiom g_gt : ∀ k, g k > k + 1

/-- C(g(k), k) is k-rough. -/
axiom g_spec : ∀ k, binomIsKRough (g k) k

/-- g(k) is minimal: no smaller n > k+1 satisfies k-roughness. -/
axiom g_minimal : ∀ k n, n > k + 1 → binomIsKRough n k → g k ≤ n

/-- g(k) ≥ k + 2, immediate from minimality. -/
theorem g_ge_k_plus_two (k : ℕ) : g k ≥ k + 2 := by
  have := g_gt k; omega

/- ## Concrete Values (Machine-Checked) -/

/-- **g(2) = 6**: C(6,2) = 15 = 3·5 is 2-rough. C(4,2) = 6 has factor 2;
C(5,2) = 10 has factor 2. -/
theorem g_two : g 2 = 6 := by
  apply le_antisymm
  · apply g_minimal 2 6 (by omega)
    intro p hp hpdvd
    by_contra h; push_neg at h
    have : p = 2 := le_antisymm h hp.two_le
    subst this; exact absurd hpdvd (by decide)
  · have hgt := g_gt 2
    suffices gFunc_2_ne : g 2 ≠ 4 ∧ g 2 ≠ 5 by omega
    constructor
    · intro h4; exact absurd (h4 ▸ g_spec 2)
        (fun h => absurd (h 2 (by decide) (by decide)) (by omega))
    · intro h5; exact absurd (h5 ▸ g_spec 2)
        (fun h => absurd (h 2 (by decide) (by decide)) (by omega))

/-- **g(3) = 7**: C(7,3) = 35 = 5·7 is 3-rough. -/
theorem g_three : g 3 = 7 := by
  apply le_antisymm
  · apply g_minimal 3 7 (by omega)
    intro p hp hpdvd
    by_contra h; push_neg at h
    have : p = 2 ∨ p = 3 := by have := hp.two_le; omega
    rcases this with rfl | rfl <;> exact absurd hpdvd (by decide)
  · have hgt := g_gt 3
    suffices g 3 ≠ 5 ∧ g 3 ≠ 6 by omega
    exact ⟨fun h => absurd (h ▸ g_spec 3)
              (fun h => absurd (h 2 (by decide) (by decide)) (by omega)),
           fun h => absurd (h ▸ g_spec 3)
              (fun h => absurd (h 2 (by decide) (by decide)) (by omega))⟩

/-- **g(4) = 7**: C(7,4) = 35 = 5·7 is 4-rough. C(6,4) = 15 has factor 3. -/
theorem g_four : g 4 = 7 := by
  apply le_antisymm
  · apply g_minimal 4 7 (by omega)
    intro p hp hpdvd
    by_contra h; push_neg at h
    have : p = 2 ∨ p = 3 ∨ p = 4 := by have := hp.two_le; omega
    rcases this with rfl | rfl | rfl
    · exact absurd hpdvd (by decide)
    · exact absurd hpdvd (by decide)
    · exact absurd hp (by decide)
  · have hgt := g_gt 4
    suffices g 4 ≠ 6 by omega
    intro h; exact absurd (h ▸ g_spec 4)
      (fun h => absurd (h 3 (by decide) (by decide)) (by omega))

/-- C(23, 5) = 33649 = 7·11·19·23 is 5-rough. -/
private theorem binomIsKRough_23_5 : binomIsKRough 23 5 := by
  intro p hp hpdvd
  by_contra h; push_neg at h
  have : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by have := hp.two_le; omega
  rcases this with rfl | rfl | rfl | rfl
  · exact absurd hpdvd (by decide)
  · exact absurd hpdvd (by decide)
  · exact absurd hp (by decide)
  · exact absurd hpdvd (by decide)

/-- **g(5) = 23**: For n = 7,…,22, some prime ≤ 5 divides C(n,5).
C(23,5) = 33649 = 7·11·19·23 is 5-rough. -/
theorem g_five : g 5 = 23 := by
  apply le_antisymm
  · exact g_minimal 5 23 (by omega) binomIsKRough_23_5
  · have hgt := g_gt 5
    suffices h : ∀ n, 7 ≤ n → n ≤ 22 → ¬binomIsKRough n 5 by
      by_contra hlt; push_neg at hlt
      exact h (g 5) (by omega) (by omega) (g_spec 5)
    intro n hn1 hn2 hk
    interval_cases n <;> first
      | exact absurd (hk 2 (by decide) (by decide)) (by omega)
      | exact absurd (hk 3 (by decide) (by decide)) (by omega)

/- ## Known Bounds (Axiomatized — Deep Analytic Results) -/

/-- **EES (1974) lower bound**: g(k) > k^(1+c) for some constant c > 0. -/
axiom ees_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ k ≥ 2, (g k : ℝ) > (k : ℝ) ^ (1 + c)

/-- **EES (1974) upper bound**: g(k) ≤ exp((1+ε)k) for all ε > 0 and large k. -/
axiom ees_upper_bound :
  ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (g k : ℝ) ≤ Real.exp ((1 + ε) * k)

/-- **Konyagin (1999) lower bound**: g(k) ≥ exp(c·(log k)²) for some c > 0 and large k.
The current best known lower bound; proved via smooth number estimates. -/
axiom konyagin_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (g k : ℝ) ≥ Real.exp (c * (Real.log k) ^ 2)

/- ## Conjectures and Open Problems -/

/-- The LCM: lcm(1, 2, …, k). By PNT, log L_k ~ k as k → ∞. -/
noncomputable def lcmUpTo (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

/-- **LCM conjecture (EES 1974)**: g(k) < lcm(1,…,k) for all large k. -/
def lcmConjecture : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, g k < lcmUpTo k

/-- **ELS "right-thinking person" lower conjecture**: g(k) ≥ exp(c·k/log k).
Open — the gap between this and Konyagin's bound exp(c·(log k)²) is significant. -/
def elsLowerConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (g k : ℝ) ≥ Real.exp (c * k / Real.log k)

/-- **Heuristic asymptotic**: log g(k) ~ c·k/log k for some constant c > 0.
Supported by Mertens' theorem: the "probability" C(n,k) is k-rough is
∏_{p ≤ k} (1 - 1/p) ≈ e^{-k/log k}, predicting g(k) ≈ exp(k/log k). -/
def heuristicConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Tendsto (fun k : ℕ => Real.log (g k) / ((k : ℝ) / Real.log k))
      atTop (𝓝 c)

end Erdos1095
