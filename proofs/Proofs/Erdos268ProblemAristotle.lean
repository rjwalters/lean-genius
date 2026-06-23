/-
  Aristotle targets for Erdős Problem #268
  Routine supporting lemmas for automated proof search.
  See Erdos268Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorem (interior nonempty) or deep topological results
  - Known results: summability, comparison tests, positivity, projections
  - Clean theorem statements with no definition sorries

  Excluded (deep/topological results kept in main file):
  - harmonicPointSet_path_connected (non-trivial topological argument)
  - harmonicPointSet_dense_somewhere partial sorry (interior argument)
-/
import Mathlib

namespace Erdos268.Aristotle

open Set Filter Topology

/- Definitions mirrored from main file -/

def HasConvergentHarmonicSubseries (A : Set ℕ) : Prop :=
  Summable (fun n : A => (1 : ℝ) / n)

noncomputable def harmonicSubseriesSum (A : Set ℕ) : ℝ :=
  ∑' n : A, (1 : ℝ) / n

noncomputable def shiftedHarmonicSum (A : Set ℕ) (k : ℕ) : ℝ :=
  ∑' n : A, (1 : ℝ) / (n + k)

noncomputable def harmonicPoint (d : ℕ) (A : Set ℕ) : Fin d → ℝ :=
  fun i => shiftedHarmonicSum A i.val

def harmonicPointSet (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ A : Set ℕ, A.Infinite ∧ HasConvergentHarmonicSubseries A ∧
    x = harmonicPoint d A}

def projectionMap (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) : (Fin d₂ → ℝ) → (Fin d₁ → ℝ) :=
  fun x => fun i => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/- ## Section 1: Summability and Convergence -/

-- Finite sets have convergent harmonic subseries (trivial: finite sum)
theorem finite_has_convergent (A : Set ℕ) (hA : A.Finite) :
    HasConvergentHarmonicSubseries A := by
  unfold HasConvergentHarmonicSubseries
  haveI : Fintype A := hA.fintype
  exact (hasSum_fintype _).summable

-- If Σ 1/n converges for A, then Σ 1/(n+k) converges (comparison test)
theorem shifted_summable (A : Set ℕ) (k : ℕ)
    (h : HasConvergentHarmonicSubseries A) :
    Summable (fun n : A => (1 : ℝ) / (n + k)) := by
  unfold HasConvergentHarmonicSubseries at h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using h
  · have hdecomp : ∀ n : A, (1 : ℝ) / ((n : ℕ) + k) =
        (if (n : ℕ) = 0 then (1 : ℝ) / k else 0) +
        (if (n : ℕ) ≠ 0 then (1 : ℝ) / ((n : ℕ) + k) else 0) := by
      intro ⟨n, _⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [Nat.pos_iff_ne_zero.mp hn]
    simp_rw [show (fun n : A => (1 : ℝ) / (↑↑n + ↑k)) =
        fun n : A => (if (n : ℕ) = 0 then (1 : ℝ) / k else 0) +
                     (if (n : ℕ) ≠ 0 then (1 : ℝ) / (↑↑n + ↑k) else 0) from
        funext hdecomp]
    apply Summable.add
    · by_cases h0 : (0 : ℕ) ∈ A
      · exact (hasSum_single ⟨0, h0⟩ (fun ⟨n, _⟩ hne => by
            have : n ≠ 0 := fun heq => hne (Subtype.ext heq)
            simp [this])).summable
      · have : (fun n : A => if (n : ℕ) = 0 then (1 : ℝ) / k else 0) = 0 := by
          ext ⟨n, hn⟩; simp [show n ≠ 0 from fun heq => h0 (heq ▸ hn)]
        rw [this]; exact summable_zero
    · apply Summable.of_nonneg_of_le
      · intro n; split_ifs <;> positivity
      · intro ⟨n, hn⟩
        by_cases hn0 : n = 0
        · simp [hn0]
        · simp only [show n ≠ 0 from hn0, ne_eq, not_false_eq_true, ↓reduceIte]
          exact one_div_le_one_div_of_le
            (by exact_mod_cast Nat.pos_of_ne_zero hn0)
            (by push_cast; linarith [Nat.cast_nonneg' (n := k)])
      · exact h

/- ## Section 2: Coordinate Properties -/

-- Each coordinate is positive for non-empty A with convergent sum
theorem all_coordinates_positive (d : ℕ) (A : Set ℕ)
    (hA : A.Nonempty) (hconv : HasConvergentHarmonicSubseries A)
    (i : Fin d) :
    (harmonicPoint d A) i > 0 := by
  simp only [harmonicPoint, shiftedHarmonicSum]
  obtain ⟨n, hn⟩ := hA
  apply tsum_pos (shifted_summable A i.val hconv)
    (fun m => div_nonneg one_nonneg (Nat.cast_nonneg' _))
  exact ⟨⟨n, hn⟩, div_pos one_pos (Nat.cast_pos.mpr (by omega))⟩

-- Coordinates decrease: 1/(n+j) < 1/(n+i) for i < j, term-by-term
-- Requires 0 ∉ A to avoid the degenerate case (1/(0+k) varies with k for 0 ∈ A)
theorem coordinate_decreasing (A : Set ℕ) (hA : A.Infinite)
    (hconv : HasConvergentHarmonicSubseries A)
    (h0 : (0 : ℕ) ∉ A)
    (i j : ℕ) (hij : i < j) :
    shiftedHarmonicSum A j < shiftedHarmonicSum A i := by
  unfold shiftedHarmonicSum
  obtain ⟨n₀, hn₀⟩ := hA.nonempty
  have hn₀_pos : 0 < n₀ := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hn₀))
  apply (shifted_summable A j hconv).tsum_lt_tsum (i := ⟨n₀, hn₀⟩)
  · intro ⟨n, hn⟩
    have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hn))
    apply one_div_le_one_div_of_le
    · exact_mod_cast Nat.add_pos_left hn_pos i
    · exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt hij) n
  · apply one_div_lt_one_div_of_lt
    · exact_mod_cast Nat.add_pos_left hn₀_pos i
    · exact_mod_cast Nat.add_lt_add_left hij n₀
  · exact shifted_summable A i hconv

-- The first coordinate is the largest (follows from decreasing)
-- Requires 0 ∉ A to use coordinate_decreasing
theorem first_coordinate_largest (d : ℕ) (hd : d ≥ 2) (A : Set ℕ)
    (hA : A.Infinite) (hconv : HasConvergentHarmonicSubseries A)
    (h0 : (0 : ℕ) ∉ A) :
    ∀ i : Fin d, (harmonicPoint d A) 0 ≥ (harmonicPoint d A) i := by
  intro i
  simp only [harmonicPoint]
  rcases Nat.eq_zero_or_pos i.val with h | h
  · simp [h]
  · exact le_of_lt (coordinate_decreasing A hA hconv h0 0 i.val h)

/- ## Section 3: Concrete Examples -/

def squaresSet : Set ℕ := {n | ∃ k : ℕ, k ≥ 1 ∧ n = k ^ 2}

-- Σ 1/n² converges (Basel problem, in Mathlib)
theorem squares_convergent : HasConvergentHarmonicSubseries squaresSet := by
  unfold HasConvergentHarmonicSubseries
  -- Bijection ℕ ≃ squaresSet via k ↦ (k+1)²
  let e : ℕ → squaresSet := fun k => ⟨(k + 1) ^ 2, k + 1, by omega, rfl⟩
  have hinj : Function.Injective e := by
    intro a b h
    simp only [e, Subtype.ext_iff] at h
    nlinarith [Nat.succ_pos a, Nat.succ_pos b]
  have hsurj : Function.Surjective e := by
    rintro ⟨n, k, hk, hkn⟩
    exact ⟨k - 1, Subtype.ext (by simp only [e]; rw [Nat.sub_add_cancel hk, hkn])⟩
  rw [← (Equiv.ofBijective e ⟨hinj, hsurj⟩).summable_iff]
  -- After bijection: Summable (fun k : ℕ => 1/↑↑(e k)) = Summable (fun k => 1/(k+1)²)
  -- This is the Basel nat-pow series (p=2) shifted by 1
  apply (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2) |>.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => add_right_cancel h)).congr
  intro k
  simp only [Function.comp, Equiv.ofBijective_apply, e]
  push_cast
  rw [one_div]

def powersOf2Set : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

-- Σ 1/2^k converges (geometric series via bijection ℕ ≃ powersOf2Set)
theorem powers_convergent : HasConvergentHarmonicSubseries powersOf2Set := by
  unfold HasConvergentHarmonicSubseries
  -- Define bijection ℕ → powersOf2Set by k ↦ 2^k
  let e : ℕ → powersOf2Set := fun k => ⟨2 ^ k, k, rfl⟩
  have he_inj : Function.Injective e := fun m n h => by
    simp only [e, Subtype.mk.injEq] at h
    exact Nat.pow_right_injective (by norm_num) h
  have he_surj : Function.Surjective e := by
    rintro ⟨n, k, hk⟩
    exact ⟨k, Subtype.ext hk.symm⟩
  rw [← (Equiv.ofBijective e ⟨he_inj, he_surj⟩).summable_iff]
  simp only [Equiv.ofBijective_apply, e]
  have heq : (fun k : ℕ => (1 : ℝ) / ↑(2 ^ k)) = (fun k : ℕ => (1 / 2 : ℝ) ^ k) := by
    ext k; push_cast; ring
  rw [heq]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/- ## Section 4: The Point Set -/

-- X is non-empty: take any infinite set with convergent sum (powers of 2)
theorem harmonicPointSet_nonempty (d : ℕ) :
    (harmonicPointSet d).Nonempty := by
  refine ⟨harmonicPoint d powersOf2Set, powersOf2Set, ?_, powers_convergent, rfl⟩
  have hrange : powersOf2Set = Set.range (fun k : ℕ => 2 ^ k) := by
    ext n; simp [powersOf2Set, Set.mem_range]
  rw [hrange]
  exact Set.infinite_range_of_injective
    (fun m n h => Nat.pow_right_injective (by norm_num) h)

-- Projection of X_{d₂} lands in X_{d₁} for d₁ ≤ d₂
theorem projection_preserves (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) :
    projectionMap d₁ d₂ h '' harmonicPointSet d₂ ⊆ harmonicPointSet d₁ := by
  rintro _ ⟨y, ⟨A, hA_inf, hA_conv, rfl⟩, rfl⟩
  refine ⟨A, hA_inf, hA_conv, ?_⟩
  ext i
  simp [projectionMap, harmonicPoint]

/- ## Section 5: Dimension 2 Point Form -/

-- In dimension 2, the harmonic point is (Σ 1/n, Σ 1/(n+1))
theorem dim2_point_form (A : Set ℕ) (hA : A.Infinite)
    (hconv : HasConvergentHarmonicSubseries A) :
    harmonicPoint 2 A = ![harmonicSubseriesSum A, shiftedHarmonicSum A 1] := by
  have key : shiftedHarmonicSum A 0 = harmonicSubseriesSum A := by
    simp [shiftedHarmonicSum, harmonicSubseriesSum, add_zero]
  funext i
  fin_cases i <;>
    simp [harmonicPoint, key, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end Erdos268.Aristotle
