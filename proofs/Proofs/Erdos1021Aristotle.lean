/-
  Aristotle targets for Erdős Problem #1021
  Routine supporting lemmas for automated proof search.
  See Erdos1021Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, asymptotics, bounds)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

open Finset Nat

namespace Erdos1021Aristotle

/-
## Binomial coefficient identities
Supporting lemmas for the telescoping argument in upper_bound_tight_construction2.
-/

/-- Pascal's rule in subtraction form: C(n+1, k+1) - C(n, k+1) = C(n, k). -/
theorem choose_succ_sub (n k : ℕ) :
    Nat.choose (n + 1) (k + 1) - Nat.choose n (k + 1) = Nat.choose n k := by
  rw [Nat.choose_succ_succ n k]; simp

/-- Monotonicity of binomial coefficients in the top argument. -/
theorem choose_le_choose_of_le (r : ℕ) {a b : ℕ} (h : a ≤ b) :
    Nat.choose a r ≤ Nat.choose b r :=
  Nat.choose_le_choose r h

/-- Natural number subtraction split: a - c = (a - b) + (b - c) when c ≤ b ≤ a. -/
theorem nat_sub_split {a b c : ℕ} (hcb : c ≤ b) (hba : b ≤ a) :
    a - c = (a - b) + (b - c) := by omega

/-
PROBLEM
## Asymptotic lemmas
Supporting lemmas for strong_implies_weak.

For c > 0, n^{3/2-c} / n^{3/2} → 0 as n → ∞.
    Equivalently: for any C, ε > 0, eventually C · n^{3/2-c} ≤ ε · n^{3/2}.

PROVIDED SOLUTION
We need C * n^(3/2 - c) ≤ ε * n^(3/2). For n = 0 this is trivially true (both sides are 0 or the LHS is ≤ 0). For n ≥ 1, rewrite as C ≤ ε * n^(3/2) / n^(3/2 - c) = ε * n^c. So we need n^c ≥ C/ε. Since n^c → ∞ as n → ∞ for c > 0, there exists N such that for n ≥ N, n^c ≥ C/ε.
-/
theorem rpow_decay_bound (C : ℝ) (hC : C > 0) (c : ℝ) (hc : c > 0) (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      C * (n : ℝ) ^ (3/2 - c) ≤ ε * (n : ℝ) ^ (3/2 : ℝ) := by
        -- We can divide both sides by $n^{3/2-c}$ to get $C \leq \epsilon \cdot n^c$.
        suffices h_div : ∃ N : ℕ, ∀ n ≥ N, C ≤ ε * (n : ℝ) ^ c by
          obtain ⟨ N, hN ⟩ := h_div; use N + 1; intros n hn; convert mul_le_mul_of_nonneg_right ( hN n ( by linarith ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( 3/2 - c ) ) using 1 ; rw [ mul_assoc, ← Real.rpow_add ( Nat.cast_pos.mpr <| by linarith ) ] ; ring;
        exact ⟨ ⌈ ( C / ε ) ^ ( 1 / c ) ⌉₊ + 1, fun n hn => by rw [ ← div_le_iff₀' hε ] ; exact le_trans ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel hc.ne.symm, Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) ( Nat.le_of_ceil_le <| Nat.le_of_succ_le hn ) <| by positivity ) ⟩

/-
PROBLEM
n^α is eventually larger than any constant for α > 0.
    Aristotle target: needs Filter.Tendsto + rpow API.

PROVIDED SOLUTION
For α > 0, we need to show n^α ≥ M eventually. If M ≤ 0 then any N works since n^α ≥ 0. If M > 0, use that x ↦ x^α is monotone increasing on [0,∞) and unbounded. Take N = max 1 ⌈M^(1/α)⌉₊. For n ≥ N, n ≥ M^(1/α), so n^α ≥ M.
-/
theorem rpow_eventually_large (α : ℝ) (hα : α > 0) (M : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (n : ℝ) ^ α ≥ M := by
      obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℤ, ∀ n : ℤ, n ≥ N₁ → (n : ℝ) ^ α ≥ M := by
        have h_exp : Filter.Tendsto (fun n : ℤ => (n : ℝ) ^ α) Filter.atTop Filter.atTop := by
          exact tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_intCast_atTop_atTop;
        exact Filter.eventually_atTop.mp ( h_exp.eventually_ge_atTop M );
      exact ⟨ Int.toNat N₁, fun n hn => hN₁ n <| by linarith [ Int.self_le_toNat N₁ ] ⟩

/-
## Bipartite graph lemmas
-/

/-- In a bipartite graph on Sum type, inl and inr injections are injective. -/
theorem sum_inl_injective (α β : Type*) : Function.Injective (Sum.inl : α → α ⊕ β) :=
  Sum.inl_injective

theorem sum_inr_injective (α β : Type*) : Function.Injective (Sum.inr : β → α ⊕ β) :=
  Sum.inr_injective

end Erdos1021Aristotle