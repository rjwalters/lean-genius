/-
  Aristotle targets for Erdős Problem #160 (Rainbow-Free 4-AP Colorings)
  Routine consequence lemmas for automated proof search.
  See Erdos160Problem.lean for the main formalization.

  Candidates:
  - h_sublinear: upper_bound_two_thirds + rpow comparison → h(n) = o(n^{1-ε})
  - h_superlog: lower_bound_exp + Real.tendsto_exp_atTop → h(n) → ∞

  Criteria for inclusion:
  - Known results derivable from the given axioms via standard real analysis
  - NOT the main open problem (closing the gap between bounds)
  - NOT the deep number-theoretic bounds themselves (those are axiomatized)
-/
import Mathlib

namespace Erdos160

open Real Filter Topology Finset

/-- A 4-term arithmetic progression a, a+d, a+2d, a+3d in {1,...,n}. -/
def Is4AP (n : ℕ) (a d : ℕ) : Prop :=
  d ≥ 1 ∧ a ≥ 1 ∧ a + 3 * d ≤ n

/-- Count distinct colors used on 4 positions. -/
def colorCount4 {n k : ℕ} (c : Fin n → Fin k)
    (i₀ i₁ i₂ i₃ : Fin n) : ℕ :=
  ({c i₀, c i₁, c i₂, c i₃} : Finset (Fin k)).card

/-- A coloring is 3-diverse on 4-APs: every 4-AP uses ≥ 3 colors. -/
def Is3DiverseOn4AP {n k : ℕ} (c : Fin n → Fin k) : Prop :=
  ∀ a d : ℕ, Is4AP n a d →
    ∀ (ha : a - 1 < n) (ha1 : a + d - 1 < n)
      (ha2 : a + 2 * d - 1 < n) (ha3 : a + 3 * d - 1 < n),
    colorCount4 c ⟨a - 1, ha⟩ ⟨a + d - 1, ha1⟩
      ⟨a + 2 * d - 1, ha2⟩ ⟨a + 3 * d - 1, ha3⟩ ≥ 3

/-- There exists a k-coloring of {1,...,n} that is 3-diverse on 4-APs. -/
def Achievable (n k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, Is3DiverseOn4AP c

/-- The identity coloring uses n colors and is always 3-diverse. -/
theorem achievable_self (n : ℕ) : Achievable n n := by
  use fun i => i
  intro a d ⟨hd, ha, hle⟩ ha' ha1' ha2' ha3'
  unfold colorCount4
  rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega)]
  simp

/-- h(N): minimum colors for a 3-diverse coloring on 4-APs. -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k | Achievable n k}

/-- LeechLattice upper bound: h(N) ≤ C · N^{2/3} for some C > 0. -/
theorem upper_bound_two_thirds :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry

/-- Hunter + Bloom-Sisask/Kelley-Meka lower bound: h(N) ≥ exp(c · (log N)^{1/9}). -/
theorem lower_bound_exp :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ Real.exp (c * (Real.log n) ^ ((1 : ℝ) / 9)) := by
  sorry

-- Routine: h grows sublinearly for ε < 1/3.
-- From upper_bound_two_thirds (h ≤ C·N^{2/3}) and 1-ε > 2/3 when ε < 1/3,
-- for large N: C·N^{2/3} ≤ N^{1-ε} because N^{1/3-ε} → ∞.
-- Uses: Real.rpow_natCast, Real.rpow_le_rpow_left, Filter.Tendsto.
theorem h_sublinear : ∀ ε > (0 : ℝ), ε < 1/3 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (h n : ℝ) ≤ (n : ℝ) ^ (1 - ε) := by
  sorry

-- Routine: h grows to infinity.
-- From lower_bound_exp (h ≥ exp(c·(log n)^{1/9})) and Real.tendsto_exp_atTop,
-- exp(c·(log n)^{1/9}) → ∞, so h(n) → ∞.
-- Uses: Real.tendsto_exp_atTop, Filter.Tendsto.comp, eventually_ge_atTop.
theorem h_superlog : ∀ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (h n : ℝ) ≥ C := by
  sorry

end Erdos160
