/-
Erdős Problem #1105: Anti-Ramsey Numbers

**Statement**: The anti-Ramsey number AR(n,G) is the maximum number of colors
in which K_n can be edge-colored without creating a rainbow copy of G.

Questions:
1. For cycles: AR(n,C_k) = ((k-2)/2 + 1/(k-1))n + O(1)?
2. For paths: explicit formula for AR(n,P_k)?

**Status**: OPEN for cycles, announced proof for paths (Yuan 2021)

Reference: https://erdosproblems.com/1105
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

open Nat

namespace Erdos1105

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part I: Basic Definitions
-/

/-- An edge coloring of a graph assigns a color (natural number) to each edge. -/
def EdgeColoring (G : SimpleGraph V) : Type := G.edgeSet → ℕ

/-- The number of colors used in a coloring. -/
noncomputable def numColors {G : SimpleGraph V} (c : EdgeColoring G) : ℕ :=
  (Set.range c).ncard

/-- A subgraph is rainbow under a coloring if all its edges have different colors. -/
def IsRainbow {G : SimpleGraph V} (c : EdgeColoring G) (H : SimpleGraph V)
    (hH : H ≤ G) : Prop :=
  ∀ e₁ e₂ : H.edgeSet, e₁ ≠ e₂ → c ⟨e₁.val, hH e₁.prop⟩ ≠ c ⟨e₂.val, hH e₂.prop⟩

/-- A coloring avoids rainbow H if no copy of H is rainbow. -/
def AvoidsRainbow {G : SimpleGraph V} (c : EdgeColoring G) (H : SimpleGraph W) : Prop :=
  ∀ (f : W → V) (hf : Function.Injective f),
    ¬IsRainbow c (H.map ⟨f, hf⟩) sorry

/-
## Part II: Anti-Ramsey Numbers
-/

/-- AR(n,H): max colors for K_n coloring avoiding rainbow H. -/
noncomputable def AR (n : ℕ) (H : SimpleGraph (Fin k)) : ℕ :=
  sSup {m : ℕ | ∃ c : EdgeColoring (⊤ : SimpleGraph (Fin n)),
         numColors c = m ∧ AvoidsRainbow c H}

/-
## Part III: Specific Graphs
-/

/-- The cycle graph C_k. -/
def cycle (k : ℕ) (hk : k ≥ 3) : SimpleGraph (Fin k) where
  Adj i j := (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val
  symm := by intro i j; simp [or_comm]
  loopless := by intro i; simp

/-- The path graph P_k (k vertices, k-1 edges). -/
def path (k : ℕ) (hk : k ≥ 2) : SimpleGraph (Fin k) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by intro i j; simp [or_comm]
  loopless := by intro i; omega

/-
## Part IV: Known Results
-/

/-- AR(n, C_3) = n - 1 (proved by ESS75). -/
axiom ar_triangle (n : ℕ) (hn : n ≥ 3) :
    AR n (cycle 3 (by omega)) = n - 1

/-- Verification: coloring with n-1 colors exists, n colors forces rainbow triangle. -/
theorem ar_triangle_upper (n : ℕ) (hn : n ≥ 3) :
    AR n (cycle 3 (by omega)) ≤ n - 1 := by sorry

theorem ar_triangle_lower (n : ℕ) (hn : n ≥ 3) :
    AR n (cycle 3 (by omega)) ≥ n - 1 := by sorry

/-
## Part V: The Main Conjectures
-/

/-- Conjecture for cycles: AR(n, C_k) = ((k-2)/2 + 1/(k-1))n + O(1). -/
def cycleConjecture (k : ℕ) (hk : k ≥ 3) : Prop :=
  ∃ C : ℝ, ∀ n ≥ k,
    |((AR n (cycle k hk) : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)| ≤ C

/-- The formula for paths.
    ℓ = ⌊(k-1)/2⌋
    AR(n, P_k) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
    where ε = 1 if k odd, ε = 2 if k even. -/
def pathFormula (n k : ℕ) (hk : k ≥ 5) (hn : n ≥ k) : ℕ :=
  let ell := (k - 1) / 2
  let eps := if k % 2 = 1 then 1 else 2
  max ((k - 2).choose 2 + 1) ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + eps)

/-- Yuan's announced result (2021): AR(n, P_k) = pathFormula for n ≥ k ≥ 5. -/
axiom yuan_path_formula (n k : ℕ) (hk : k ≥ 5) (hn : n ≥ k) :
    AR n (path k (by omega)) = pathFormula n k hk hn

/-
## Part VI: Partial Results
-/

/-- Simonovits-Sós (1984): Formula holds for n ≥ c·k². -/
axiom simonovits_sos_partial (k : ℕ) (hk : k ≥ 5) :
    ∃ c : ℕ, c > 0 ∧ ∀ n ≥ c * k^2,
      AR n (path k (by omega)) = pathFormula n k hk (by omega)

/-
## Part VII: Small Examples
-/

/-- AR(4, C_3) = 3. K_4 with 3 colors can avoid rainbow triangle. -/
example : AR 4 (cycle 3 (by omega)) = 3 := by
  have := ar_triangle 4 (by omega)
  simp at this ⊢
  exact this

/-- AR(5, C_3) = 4. -/
example : AR 5 (cycle 3 (by omega)) = 4 := by
  have := ar_triangle 5 (by omega)
  simp at this ⊢
  exact this

/-
## Part VIII: Summary
-/

/-- Erdős Problem #1105: Summary

    **Definition**: AR(n,G) = max colors for K_n without rainbow G

    **Cycles**:
    - AR(n, C_3) = n - 1 (proved)
    - Conjecture: AR(n, C_k) = ((k-2)/2 + 1/(k-1))n + O(1)

    **Paths**:
    - Formula: max(C(k-2,2)+1, C(ℓ-1,2)+(ℓ-1)(n-ℓ+1)+ε) where ℓ=⌊(k-1)/2⌋
    - Yuan 2021: announced proof for all n ≥ k ≥ 5
    - Simonovits-Sós 1984: proved for n ≥ c·k²

    **Key**: Rainbow = all edges have different colors. -/
theorem erdos_1105_summary :
    -- Triangle case is known
    (∀ n ≥ 3, AR n (cycle 3 (by omega)) = n - 1) ∧
    -- Path formula announced
    (∀ n k, k ≥ 5 → n ≥ k → AR n (path k (by omega)) = pathFormula n k (by omega) (by omega)) := by
  exact ⟨ar_triangle, yuan_path_formula⟩

end Erdos1105
