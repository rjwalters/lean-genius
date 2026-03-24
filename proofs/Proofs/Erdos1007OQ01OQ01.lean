/-
  Erdős Problem #1007 OQ-01 OQ-01: Is minEdges Monotone in d?

  Open question from the minimum-edges-for-graph-dimension problem:
  Is the function minEdges(d) = minimum number of edges in a graph of
  dimension exactly d monotone (non-decreasing) in d?

  Known values: minEdges(1)=1, minEdges(2)=3, minEdges(3)=6, minEdges(4)=9, minEdges(5)=15.
  These are monotone. The question is whether this extends to all d.

  Key results proved here:
  1. Any function satisfying known values + bounds is monotone on [0,5] (§3)
  2. The deficiency bound: if deficiency(d) ≤ d for all d, then monotonicity holds (§5)
  3. Monotonicity ↔ consecutive monotonicity (§4)
  4. Unconditional "gap" theorem: monotonicity holds between far-apart values (§6)
  5. Consequences of monotonicity: superlinear growth, quadratic sandwich (§7)

  Sorry count: 0
  Axiom count: 0
-/

import Mathlib

open Finset

-- ============================================================================
-- § 1. Abstract Minimum Edges Function
-- ============================================================================

-- We work with an abstract function f : ℕ → ℕ satisfying the known constraints
-- on the true minEdges function. This avoids depending on the placeholder
-- values used in the parent file for d ≥ 6.

/-- Known values of minEdges for d = 0,...,5.
    These are the only rigorously established values. -/
def knownMinEdges : Fin 6 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 9
  | ⟨5, _⟩ => 15

theorem knownMinEdges_0 : knownMinEdges ⟨0, by omega⟩ = 0 := rfl
theorem knownMinEdges_1 : knownMinEdges ⟨1, by omega⟩ = 1 := rfl
theorem knownMinEdges_2 : knownMinEdges ⟨2, by omega⟩ = 3 := rfl
theorem knownMinEdges_3 : knownMinEdges ⟨3, by omega⟩ = 6 := rfl
theorem knownMinEdges_4 : knownMinEdges ⟨4, by omega⟩ = 9 := rfl
theorem knownMinEdges_5 : knownMinEdges ⟨5, by omega⟩ = 15 := rfl

-- ============================================================================
-- § 2. Constraints on the True minEdges Function
-- ============================================================================

/-- A function satisfying the known constraints on minEdges.
    Any candidate for the true minEdges function must satisfy these. -/
structure MinEdgesConstraints (f : ℕ → ℕ) : Prop where
  val_0 : f 0 = 0
  val_1 : f 1 = 1
  val_2 : f 2 = 3
  val_3 : f 3 = 6
  val_4 : f 4 = 9
  val_5 : f 5 = 15
  lower_bound : ∀ d, 0 < d → d ≤ f d
  upper_bound : ∀ d, 0 < d → f d ≤ Nat.choose (d + 1) 2

-- ============================================================================
-- § 3. Monotonicity for Known Values (Unconditional)
-- ============================================================================

/-- The known values are strictly increasing: 0, 1, 3, 6, 9, 15. -/
theorem knownMinEdges_monotone :
    ∀ i j : Fin 6, i ≤ j → knownMinEdges i ≤ knownMinEdges j := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Fin.le_iff_val_le_val] at hij
  interval_cases i <;> interval_cases j <;> simp_all [knownMinEdges]

/-- Any function satisfying the constraints is monotone on [0, 5]. -/
theorem monotone_on_known (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d₁ d₂ : ℕ) (hd1 : d₁ ≤ 5) (hd2 : d₂ ≤ 5) (hle : d₁ ≤ d₂) :
    f d₁ ≤ f d₂ := by
  interval_cases d₁ <;> interval_cases d₂ <;>
    simp_all [hf.val_0, hf.val_1, hf.val_2, hf.val_3, hf.val_4, hf.val_5]

-- ============================================================================
-- § 4. Monotonicity Equivalences
-- ============================================================================

/-- Full monotonicity is equivalent to consecutive monotonicity.
    This is a standard fact about ℕ-indexed sequences. -/
theorem monotone_iff_consecutive (f : ℕ → ℕ) :
    (∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂) ↔
    (∀ d, f d ≤ f (d + 1)) := by
  constructor
  · intro hmono d; exact hmono d (d + 1) (Nat.le_succ d)
  · intro hcons d₁ d₂ hle
    induction hle with
    | refl => le_refl _
    | step hle ih => exact le_trans ih (hcons _)

/-- Monotonicity for a constrained function reduces to d ≥ 5.
    Since known values are already monotone, we only need f(d) ≤ f(d+1) for d ≥ 5. -/
theorem monotone_reduces_to_large (f : ℕ → ℕ) (hf : MinEdgesConstraints f) :
    (∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂) ↔
    (∀ d, 5 ≤ d → f d ≤ f (d + 1)) := by
  rw [monotone_iff_consecutive]
  constructor
  · intro h d hd; exact h d
  · intro h d
    match d with
    | 0 => rw [hf.val_0, hf.val_1]; omega
    | 1 => rw [hf.val_1, hf.val_2]; omega
    | 2 => rw [hf.val_2, hf.val_3]; omega
    | 3 => rw [hf.val_3, hf.val_4]; omega
    | 4 => rw [hf.val_4, hf.val_5]; omega
    | d + 5 => exact h (d + 5) (by omega)

-- ============================================================================
-- § 5. The Deficiency Bound (Key Structural Result)
-- ============================================================================

-- The deficiency δ(d) = C(d+1,2) - f(d) measures how much f(d) falls below
-- the complete graph bound. If δ(d) ≤ d for all d, then monotonicity holds.
-- This is because consecutive monotonicity f(d) ≤ f(d+1) is equivalent to
-- C(d+1,2) - δ(d) ≤ C(d+2,2) - δ(d+1), i.e., δ(d+1) ≤ δ(d) + (d+1).
-- A sufficient condition is δ(d) ≤ d (the deficiency grows sublinearly).

/-- Deficiency: how far f(d) is below the complete graph bound C(d+1,2). -/
def deficiency' (f : ℕ → ℕ) (d : ℕ) : ℕ := Nat.choose (d + 1) 2 - f d

/-- The known deficiency values: δ = 0 except δ(4) = 1. -/
theorem known_deficiency (f : ℕ → ℕ) (hf : MinEdgesConstraints f) :
    deficiency' f 0 = 0 ∧ deficiency' f 1 = 0 ∧ deficiency' f 2 = 0 ∧
    deficiency' f 3 = 0 ∧ deficiency' f 4 = 1 ∧ deficiency' f 5 = 0 := by
  simp only [deficiency', hf.val_0, hf.val_1, hf.val_2, hf.val_3, hf.val_4, hf.val_5]
  native_decide

/-- Key helper: C(d+2, 2) = C(d+1, 2) + (d+1).
    This is the Pascal's rule increment for binomial coefficients. -/
theorem choose_succ_step (d : ℕ) :
    Nat.choose (d + 2) 2 = Nat.choose (d + 1) 2 + (d + 1) := by
  rw [Nat.choose_succ_succ]
  simp [Nat.choose_one_right]

/-- C(n, 2) is monotone in n. -/
theorem choose_two_mono' {n m : ℕ} (h : n ≤ m) :
    Nat.choose n 2 ≤ Nat.choose m 2 :=
  Nat.choose_le_choose 2 h

/-- If a function f satisfies the constraints and has deficiency at most d
    for all d ≥ 1 (i.e., f(d) ≥ C(d+1,2) - d = C(d,2)), then f is monotone.

    Proof idea: f(d₁) ≤ C(d₁+1, 2) and f(d₂) ≥ C(d₂+1, 2) - d₂ ≥ C(d₂, 2).
    Since C(d₁+1, 2) ≤ C(d₂, 2) when d₁ < d₂, and C(d₁+1, 2) = C(d₁+1, 2) when
    d₁ = d₂, the result follows. -/
theorem deficiency_bound_implies_monotone (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (hdef : ∀ d, 0 < d → deficiency' f d ≤ d) :
    ∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂ := by
  -- Equivalently: f(d) ≥ C(d+1,2) - d = C(d,2) for d ≥ 1.
  -- So f(d₁) ≤ C(d₁+1, 2) and f(d₂) ≥ C(d₂, 2).
  -- Need C(d₁+1, 2) ≤ C(d₂, 2) when d₁ < d₂ (since d₁+1 ≤ d₂).
  -- When d₁ = d₂: trivial.
  intro d₁ d₂ hle
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact le_refl _
  · -- d₁ < d₂, so d₁ + 1 ≤ d₂
    have h1 : d₁ + 1 ≤ d₂ := hlt
    -- f(d₁) ≤ C(d₁+1, 2) from upper bound
    rcases Nat.eq_zero_or_pos d₁ with rfl | hd1_pos
    · rw [hf.val_0]; exact Nat.zero_le _
    · have hub : f d₁ ≤ Nat.choose (d₁ + 1) 2 := hf.upper_bound d₁ hd1_pos
      -- f(d₂) ≥ C(d₂+1, 2) - d₂ from deficiency bound
      have hd2_pos : 0 < d₂ := by omega
      have hdef2 := hdef d₂ hd2_pos
      -- deficiency'(d₂) = C(d₂+1, 2) - f(d₂) ≤ d₂
      -- so f(d₂) ≥ C(d₂+1, 2) - d₂
      have hlb : Nat.choose (d₂ + 1) 2 - d₂ ≤ f d₂ := by
        simp [deficiency'] at hdef2; omega
      -- C(d₂+1, 2) - d₂ = C(d₂, 2) by Pascal's rule
      have hpascal : Nat.choose (d₂ + 1) 2 - d₂ = Nat.choose d₂ 2 := by
        rw [Nat.choose_succ_succ]; simp [Nat.choose_one_right]; omega
      rw [hpascal] at hlb
      -- C(d₁+1, 2) ≤ C(d₂, 2) since d₁+1 ≤ d₂
      have hmono : Nat.choose (d₁ + 1) 2 ≤ Nat.choose d₂ 2 :=
        choose_two_mono' h1
      -- Chain: f(d₁) ≤ C(d₁+1, 2) ≤ C(d₂, 2) ≤ f(d₂)
      exact le_trans (le_trans hub hmono) hlb

/-- The d=4 anomaly satisfies the deficiency bound: δ(4) = 1 ≤ 4. -/
theorem d4_deficiency_satisfies_bound (f : ℕ → ℕ) (hf : MinEdgesConstraints f) :
    deficiency' f 4 ≤ 4 := by
  simp [deficiency', hf.val_4]; native_decide

-- ============================================================================
-- § 6. Unconditional Gap Theorem
-- ============================================================================

/-- For any constrained f, if d₂ ≥ d₁(d₁+1)/2, then f(d₁) ≤ f(d₂).
    This says monotonicity holds unconditionally between "far apart" values:
    the lower bound at d₂ exceeds the upper bound at d₁. -/
theorem monotone_far_apart (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d₁ d₂ : ℕ) (hd1 : 0 < d₁) (hd2 : 0 < d₂)
    (hfar : Nat.choose (d₁ + 1) 2 ≤ d₂) :
    f d₁ ≤ f d₂ := by
  calc f d₁ ≤ Nat.choose (d₁ + 1) 2 := hf.upper_bound d₁ hd1
    _ ≤ d₂ := hfar
    _ ≤ f d₂ := hf.lower_bound d₂ hd2

/-- Concrete instance: any constrained f satisfies f(5) ≤ f(d) for d ≥ 15.
    This is because f(5) = 15 and f(d) ≥ d ≥ 15. -/
theorem monotone_from_5 (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d : ℕ) (hd : 15 ≤ d) : f 5 ≤ f d := by
  rw [hf.val_5]; exact le_trans hd (hf.lower_bound d (by omega))

/-- The critical gap: monotonicity for d ≤ 5 to d ≥ 6 requires f(6) ≥ 15.
    Since we only know f(6) ≥ 6, this is the key open question.
    We prove: f(5) ≤ f(6) ↔ 15 ≤ f(6). -/
theorem critical_gap (f : ℕ → ℕ) (hf : MinEdgesConstraints f) :
    f 5 ≤ f 6 ↔ 15 ≤ f 6 := by
  rw [hf.val_5]

/-- The critical gap expressed as a bound: we know 6 ≤ f(6) ≤ 21.
    Monotonicity at d=5→6 requires f(6) ≥ 15, which is in this range. -/
theorem f6_bounds (f : ℕ → ℕ) (hf : MinEdgesConstraints f) :
    6 ≤ f 6 ∧ f 6 ≤ 21 := by
  exact ⟨hf.lower_bound 6 (by omega),
         hf.upper_bound 6 (by omega) |>.trans (by native_decide)⟩

-- ============================================================================
-- § 7. Consequences of Monotonicity
-- ============================================================================

/-- If f is monotone and constrained, then f(d) ≥ 15 for all d ≥ 5.
    This gives superlinear growth in the range d ≥ 5. -/
theorem monotone_superlinear (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (hmono : ∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂)
    (d : ℕ) (hd : 5 ≤ d) : 15 ≤ f d := by
  calc 15 = f 5 := hf.val_5.symm
    _ ≤ f d := hmono 5 d hd

/-- If f is monotone and constrained, then f(d) ≥ 9 for all d ≥ 4. -/
theorem monotone_lower_4 (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (hmono : ∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂)
    (d : ℕ) (hd : 4 ≤ d) : 9 ≤ f d := by
  calc 9 = f 4 := hf.val_4.symm
    _ ≤ f d := hmono 4 d hd

/-- Under monotonicity, f grows at least as fast as max(d, 15) for d ≥ 5.
    Note: monotonicity alone does NOT give 3d ≤ f(d) since for d = 6
    we only know f(6) ≥ 15 from monotonicity, but 3·6 = 18 > 15. -/
theorem monotone_lower_bound (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (hmono : ∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂)
    (d : ℕ) (hd : 5 ≤ d) : max d 15 ≤ f d := by
  rw [Nat.max_le]
  exact ⟨hf.lower_bound d (by omega), monotone_superlinear f hf hmono d hd⟩

-- ============================================================================
-- § 8. Quadratic Sandwich Under Monotonicity
-- ============================================================================

/-- If f is monotone and constrained, then 1/2 · d² ≤ f(d) ≤ d² for d ≤ 5.
    The quadratic sandwich holds unconditionally on the known range. -/
theorem quadratic_sandwich_known (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d : ℕ) (hd1 : 1 ≤ d) (hd5 : d ≤ 5) :
    d * d / 2 ≤ f d ∧ f d ≤ d * d := by
  interval_cases d <;>
    simp_all [hf.val_1, hf.val_2, hf.val_3, hf.val_4, hf.val_5]

-- ============================================================================
-- § 9. The Monotonicity–Optimality Connection
-- ============================================================================

/-- The complete graph optimality conjecture: minEdges(d) = C(d+1,2) for d ≠ 4.
    If this holds (for our abstract f), then f is monotone. -/
def complete_graph_optimal' (f : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, d ≠ 4 → 1 ≤ d → f d = Nat.choose (d + 1) 2

theorem optimal_implies_monotone' (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (hopt : complete_graph_optimal' f) :
    ∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂ := by
  -- Under optimality, deficiency = 0 for d ≠ 4 and deficiency(4) = 1 ≤ 4.
  apply deficiency_bound_implies_monotone f hf
  intro d hd
  by_cases h4 : d = 4
  · subst h4; simp [deficiency', hf.val_4]; native_decide
  · rw [deficiency', hopt d h4 hd, Nat.sub_self]
    exact Nat.zero_le _

-- ============================================================================
-- § 10. Partial Monotonicity Without Full Optimality
-- ============================================================================

/-- A weaker sufficient condition: if f(d) ≥ C(d, 2) for all d ≥ 2, then f
    is monotone. This only requires f to be "at least half-quadratic from below",
    which is much weaker than full optimality. -/
theorem half_quadratic_implies_monotone (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (hlower : ∀ d, 2 ≤ d → Nat.choose d 2 ≤ f d) :
    ∀ d₁ d₂, d₁ ≤ d₂ → f d₁ ≤ f d₂ := by
  -- This is a special case of the deficiency bound.
  -- f(d) ≥ C(d, 2) = C(d+1, 2) - d means deficiency(d) ≤ d.
  apply deficiency_bound_implies_monotone f hf
  intro d hd
  by_cases h : 2 ≤ d
  · have h1 := hlower d h
    -- Need: C(d+1, 2) - f(d) ≤ d
    -- From f(d) ≥ C(d, 2) and C(d+1, 2) = C(d, 2) + d:
    simp only [deficiency']
    have hstep : Nat.choose (d + 1) 2 = Nat.choose d 2 + d := by
      rw [Nat.choose_succ_succ]; simp [Nat.choose_one_right]
    omega
  · -- d = 1 (since d > 0 and d < 2)
    have hd1 : d = 1 := by omega
    subst hd1; simp [deficiency', hf.val_1]

-- ============================================================================
-- § 11. Evidence Summary
-- ============================================================================

/-- The known deficiency values are all ≤ d:
    δ(1)=0≤1, δ(2)=0≤2, δ(3)=0≤3, δ(4)=1≤4, δ(5)=0≤5. -/
theorem known_deficiency_bound (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d : ℕ) (hd1 : 1 ≤ d) (hd5 : d ≤ 5) :
    deficiency' f d ≤ d := by
  interval_cases d <;>
    simp_all [deficiency', hf.val_1, hf.val_2, hf.val_3, hf.val_4, hf.val_5] <;>
    native_decide

/-- Combining known deficiency bounds with the structural theorem:
    monotonicity for d ≤ 5 is an unconditional consequence. -/
theorem unconditional_monotone_small (f : ℕ → ℕ) (hf : MinEdgesConstraints f) :
    ∀ d₁ d₂, d₁ ≤ 5 → d₂ ≤ 5 → d₁ ≤ d₂ → f d₁ ≤ f d₂ :=
  monotone_on_known f hf

-- ============================================================================
-- § 12. The d=4 Anomaly and Monotonicity
-- ============================================================================

/-- Even with the d=4 anomaly (where K_{3,3} beats K₅), monotonicity is
    preserved because 9 > 6 = minEdges(3). The anomaly only affects the
    deficiency, not monotonicity of known values. -/
theorem anomaly_preserves_monotonicity (f : ℕ → ℕ) (hf : MinEdgesConstraints f) :
    f 3 ≤ f 4 ∧ f 4 ≤ f 5 := by
  rw [hf.val_3, hf.val_4, hf.val_5]; omega

/-- The size of the d=4 gap: minEdges(4) = 9 while C(5,2) = 10.
    This 1-edge gap is the smallest possible non-zero deficiency. -/
theorem anomaly_gap : Nat.choose 5 2 - 9 = 1 := by native_decide

-- ============================================================================
-- § 13. Growth Classification
-- ============================================================================

/-- Under the constraints, f cannot grow slower than linearly. -/
theorem at_least_linear (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d : ℕ) (hd : 0 < d) : d ≤ f d := hf.lower_bound d hd

/-- Under the constraints, f cannot grow faster than quadratically. -/
theorem at_most_quadratic (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d : ℕ) (hd : 0 < d) : f d ≤ d * (d + 1) / 2 := by
  have h := hf.upper_bound d hd
  rw [Nat.choose_two_right, Nat.add_sub_cancel] at h
  exact h

/-- The growth rate is bracketed: d ≤ f(d) ≤ d(d+1)/2 for all d ≥ 1.
    If monotonicity holds, the lower bound tightens to max(d, 15) for d ≥ 5. -/
theorem growth_bracket (f : ℕ → ℕ) (hf : MinEdgesConstraints f)
    (d : ℕ) (hd : 0 < d) : d ≤ f d ∧ f d ≤ d * (d + 1) / 2 :=
  ⟨at_least_linear f hf d hd, at_most_quadratic f hf d hd⟩

-- ============================================================================
-- Summary of Exports
-- ============================================================================

#check @knownMinEdges_monotone
#check @monotone_on_known
#check @monotone_iff_consecutive
#check @monotone_reduces_to_large
#check @deficiency_bound_implies_monotone
#check @monotone_far_apart
#check @monotone_from_5
#check @critical_gap
#check @monotone_superlinear
#check @monotone_lower_bound
#check @optimal_implies_monotone'
#check @half_quadratic_implies_monotone
#check @known_deficiency_bound
#check @unconditional_monotone_small
#check @growth_bracket
