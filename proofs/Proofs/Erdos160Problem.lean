/-
Erdős Problem #160 — Rainbow-Free Colorings of Arithmetic Progressions

Let h(N) be the smallest k such that {1, ..., N} can be colored with k
colors so that every 4-term arithmetic progression contains at least 3
distinct colors.

Known bounds:
- Upper: h(N) ≪ N^{2/3} (LeechLattice, MathOverflow)
- Improved upper: h(N) ≪ N^{log 3/log 22 + o(1)} ≈ N^{0.355} (Hunter)
- Lower: h(N) ≫ exp(c(log N)^{1/9}) (Hunter + Bloom-Sisask/Kelley-Meka)

The problem asks to close the gap between upper and lower bounds.

Status: OPEN
Reference: https://erdosproblems.com/160

The function h(N) is constructively defined via sInf (well-ordering of ℕ),
eliminating 3 former axioms (h, h_achievable, h_minimal).

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset

namespace Erdos160

/-
# Part 1: Basic Definitions
-/

/-- A 4-term arithmetic progression a, a+d, a+2d, a+3d in {1,...,n}.
    We require d ≥ 1 and a ≥ 1 and a + 3d ≤ n. -/
def Is4AP (n : ℕ) (a d : ℕ) : Prop :=
  d ≥ 1 ∧ a ≥ 1 ∧ a + 3 * d ≤ n

/-- The number of distinct colors used by a coloring on a 4-AP.
    Given indices into Fin n, count distinct values among the 4 elements. -/
def colorCount4 {n k : ℕ} (c : Fin n → Fin k)
    (i₀ i₁ i₂ i₃ : Fin n) : ℕ :=
  ({c i₀, c i₁, c i₂, c i₃} : Finset (Fin k)).card

/-- A coloring is 3-diverse on 4-APs: every 4-term AP in {1,...,n}
    uses at least 3 distinct colors. -/
def Is3DiverseOn4AP {n k : ℕ} (c : Fin n → Fin k) : Prop :=
  ∀ a d : ℕ, Is4AP n a d →
    ∀ (ha : a - 1 < n) (ha1 : a + d - 1 < n)
      (ha2 : a + 2 * d - 1 < n) (ha3 : a + 3 * d - 1 < n),
    colorCount4 c ⟨a - 1, ha⟩ ⟨a + d - 1, ha1⟩
      ⟨a + 2 * d - 1, ha2⟩ ⟨a + 3 * d - 1, ha3⟩ ≥ 3

/-- There exists a k-coloring of {1,...,n} that is 3-diverse on 4-APs. -/
def Achievable (n k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, Is3DiverseOn4AP c

/-
# Part 2: Structural Properties
-/

/-- If n = 0, any coloring is trivially 3-diverse (no valid 4-APs). -/
theorem achievable_zero (k : ℕ) : Achievable 0 k := by
  use fun i => i.elim0
  intro a d ⟨_, _, hle⟩
  exact absurd hle (by omega)

/-- If n ≤ 3, there are no valid 4-APs, so any coloring works. -/
theorem achievable_small {n k : ℕ} (hn : n ≤ 3) (hk : k ≥ 1) : Achievable n k := by
  obtain ⟨j, hj⟩ : ∃ j : Fin k, True := ⟨⟨0, by omega⟩, trivial⟩
  use fun _ => j
  intro a d ⟨hd, ha, hle⟩
  omega

/-- If k-coloring is achievable, then (k+1)-coloring is also achievable.
    Proof: embed Fin k into Fin (k+1) via Fin.castSucc (injective,
    so distinct colors remain distinct). -/
theorem achievable_mono_colors {n k : ℕ} (hak : Achievable n k) :
    Achievable n (k + 1) := by
  obtain ⟨c, hc⟩ := hak
  refine ⟨Fin.castSucc ∘ c, fun a d hap ha ha1 ha2 ha3 => ?_⟩
  have hcard := hc a d hap ha ha1 ha2 ha3
  unfold colorCount4 at hcard ⊢
  simp only [Function.comp]
  have himg : ({Fin.castSucc (c ⟨a - 1, ha⟩), Fin.castSucc (c ⟨a + d - 1, ha1⟩),
      Fin.castSucc (c ⟨a + 2 * d - 1, ha2⟩),
      Fin.castSucc (c ⟨a + 3 * d - 1, ha3⟩)} : Finset (Fin (k + 1))) =
    ({c ⟨a - 1, ha⟩, c ⟨a + d - 1, ha1⟩, c ⟨a + 2 * d - 1, ha2⟩,
      c ⟨a + 3 * d - 1, ha3⟩} : Finset (Fin k)).image Fin.castSucc := by
    simp [Finset.image_insert, Finset.image_singleton]
  rw [himg, Finset.card_image_of_injective _ (Fin.castSucc_injective k)]
  exact hcard

/-- Monotonicity in n: if achievable for n, achievable for any m ≤ n
    with the same number of colors. -/
theorem achievable_mono_n {n m k : ℕ} (hmn : m ≤ n) (h : Achievable n k) :
    Achievable m k := by
  obtain ⟨c, hc⟩ := h
  use fun i => c ⟨i.val, by omega⟩
  intro a d ⟨hd, ha, hle⟩ ha' ha1' ha2' ha3'
  apply hc a d ⟨hd, ha, by omega⟩ (by omega) (by omega) (by omega) (by omega)

/-
# Part 3: The function h(N)

h(N) is the minimum k such that Achievable N k holds.
Defined via sInf on ℕ (well-ordering principle), no axioms needed.
-/

/-- Every n-element set can be colored with n colors (identity coloring).
    Establishes that {k | Achievable n k} is nonempty for all n. -/
theorem achievable_self (n : ℕ) : Achievable n n := by
  use fun i => i
  intro a d ⟨hd, ha, hle⟩ ha' ha1' ha2' ha3'
  unfold colorCount4
  rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega)]
  simp

/-- h(N): the minimum number of colors for a 3-diverse coloring on 4-APs.
    Defined as the infimum of {k | Achievable n k}, which is well-defined
    since ℕ is well-ordered and the set is nonempty (achievable_self). -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k | Achievable n k}

/-- h(N) is achievable: the minimum is attained (Nat.sInf_mem). -/
theorem h_achievable (n : ℕ) : Achievable n (h n) :=
  Nat.sInf_mem ⟨n, achievable_self n⟩

/-- h(N) is minimal: no smaller k works (Nat.sInf_le). -/
theorem h_minimal (n : ℕ) : ∀ k < h n, ¬Achievable n k := by
  intro k hk hak
  exact absurd (Nat.sInf_le hak) (not_le_of_lt hk)

/-- h(N) ≥ 1 for N ≥ 4 (at least one color needed, and the problem
    is nontrivial once there exist 4-APs). -/
theorem h_pos (n : ℕ) (hn : n ≥ 4) : h n ≥ 1 := by
  by_contra h_lt
  push_neg at h_lt
  have h_eq : h n = 0 := by omega
  have := h_achievable n
  rw [h_eq] at this
  obtain ⟨c, _⟩ := this
  exact Fin.elim0 (c ⟨0, by omega⟩)

/-- h is monotone: if m ≤ n then h(m) ≤ h(n). -/
theorem h_mono {m n : ℕ} (hmn : m ≤ n) : h m ≤ h n := by
  by_contra h_lt
  push_neg at h_lt
  have := h_minimal m (h n) h_lt
  exact this (achievable_mono_n hmn (h_achievable n))

/-- h(0) = 0 (no elements to color). -/
theorem h_zero : h 0 = 0 := by
  by_contra h_ne
  have hpos : h 0 ≥ 1 := Nat.pos_of_ne_zero h_ne
  have := h_minimal 0 0 (by omega)
  exact this (achievable_zero 0)

/-- h(N) ≤ 1 for 1 ≤ N ≤ 3 (no 4-APs exist, one color suffices). -/
theorem h_le_one_small (n : ℕ) (_hn : 1 ≤ n) (hn3 : n ≤ 3) : h n ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  have := h_minimal n 1 (by omega)
  exact this (achievable_small hn3 (by omega))

/-- h(N) ≤ N: using N colors (one per element) always works. -/
theorem h_le_n (n : ℕ) : h n ≤ n :=
  Nat.sInf_le (achievable_self n)

/-
# Part 4: Known Upper Bounds
-/

/-- **LeechLattice upper bound**: h(N) ≪ N^{2/3}.
    Shown on MathOverflow. -/
axiom upper_bound_two_thirds :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (h n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3)

/-- **Hunter improved upper bound**: h(N) ≪ N^{log 3/log 22 + o(1)}.
    This gives h(N) ≪ N^{0.355} approximately. -/
axiom upper_bound_hunter :
  ∃ C : ℝ, C > 0 ∧ ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (h n : ℝ) ≤ C * (n : ℝ) ^ (Real.log 3 / Real.log 22 + ε)

/-
# Part 5: Known Lower Bounds
-/

/-- **Hunter + Bloom-Sisask/Kelley-Meka lower bound**:
    h(N) ≫ exp(c · (log N)^{1/9}) for some c > 0.
    Uses bounds on 3-AP-free sets. -/
axiom lower_bound_exp :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (h n : ℝ) ≥ Real.exp (c * (Real.log n) ^ ((1 : ℝ) / 9))

/-
# Part 6: Consequences
-/

/-- The upper bound implies h grows sublinearly (for ε < 1/3).
    NOTE: as stated this is FALSE for ε > 1/3 since h(n) ≤ C·n^(2/3)
    does NOT imply h(n) ≤ n^(1-ε) when 1-ε < 2/3. The correct
    statement would be h(n) ≤ n^(2/3+ε) for any ε > 0. -/
theorem h_sublinear : ∀ ε > (0 : ℝ), ε < 1/3 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (h n : ℝ) ≤ (n : ℝ) ^ (1 - ε) := by
  sorry -- Follows from upper_bound_two_thirds for ε < 1/3; needs rpow_le_rpow

/-- The lower bound implies h grows without bound: for any C,
    h(n) ≥ C for all sufficiently large n. Proof: the exponential
    lower bound exp(c · (log n)^{1/9}) → ∞ as n → ∞. -/
theorem h_superlog : ∀ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (h n : ℝ) ≥ C := by
  sorry -- Requires showing exp(c · (log n)^{1/9}) → ∞, needs Filter.Tendsto infrastructure

/-- The Hunter upper bound improves on the LeechLattice bound
    (log 3 / log 22 < 2/3). Proof: log 3 < (2/3) · log 22 since
    3^3 = 27 < 22^2 = 484, so log 27 < log 484, i.e., 3·log 3 < 2·log 22.
    Division by 3·log 22 gives the result. -/
theorem hunter_improves_leechlattice :
    Real.log 3 / Real.log 22 < (2 : ℝ) / 3 := by
  have hlog22_pos : (0 : ℝ) < Real.log 22 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff hlog22_pos (by norm_num : (0 : ℝ) < 3)]
  -- Goal: Real.log 3 * 3 < 2 * Real.log 22
  -- Equivalently: log(3^3) < log(22^2), i.e., log 27 < log 484
  rw [show Real.log 3 * 3 = Real.log (3 ^ 3) by rw [Real.log_pow]; ring,
      show (2 : ℝ) * Real.log 22 = Real.log (22 ^ 2) by rw [Real.log_pow]; ring]
  exact Real.log_lt_log (by positivity) (by norm_num)

/-
# Part 7: Open Questions (the actual Erdős problem)
-/

/-- **Erdős Problem 160**: Estimate h(N). The gap between the known
    upper bound (polynomial) and lower bound (superlogarithmic) is vast.
    The central question is to determine the true growth rate. -/
def ErdosProblem160 : Prop :=
  ∃ f : ℕ → ℝ, (∀ n, f n > 0) ∧
    (∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
      ∀ n ≥ 2, C₁ * f n ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ C₂ * f n)

/-- Summary of known bounds -/
theorem summary :
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (h n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3)) ∧
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (h n : ℝ) ≥ Real.exp (c * (Real.log n) ^ ((1 : ℝ) / 9))) :=
  ⟨upper_bound_two_thirds, lower_bound_exp⟩

end Erdos160
