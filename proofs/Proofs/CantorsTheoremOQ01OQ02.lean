import Proofs.CantorsTheoremOQ01
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic

/-
# |𝒫(𝒫(ℝ))| = ℶ₃: The Iterated Power Set Hierarchy

## Research Question: cantors-theorem-oq-01-oq-02

The parent proof established |𝒫(ℝ)| = ℶ₂. This proof extends the beth tower
one level further:

  |𝒫(𝒫(ℝ))| = 2^|𝒫(ℝ)| = 2^ℶ₂ = ℶ₃

and proves the general inductive pattern: for all n : ℕ,

  |𝒫ⁿ(ℝ)| = ℶ_{n+1}

where 𝒫⁰(ℝ) = ℝ, 𝒫^{n+1}(X) = 𝒫(𝒫ⁿ(X)).

**All results are proved in ZFC (Mathlib), 0 axioms, 0 sorries.**

## The Beth Hierarchy
  ℶ₀ = ℵ₀ = |ℕ|
  ℶ₁ = 2^ℵ₀ = 𝔠 = |ℝ|
  ℶ₂ = 2^𝔠 = |𝒫(ℝ)|
  ℶ₃ = 2^ℶ₂ = |𝒫(𝒫(ℝ))|    ← this file
  ...
  ℶ_{n+1} = 2^ℶₙ = |𝒫ⁿ(ℝ)|  ← general pattern
-/

set_option linter.unusedVariables false

namespace CantorsTheoremOQ01OQ02

open Cardinal

-- ============================================================
-- PART 1: Beth Number Lemmas
-- ============================================================

/-- ℶ₃ = 2^ℶ₂: the third beth number is 2 to the power of the second. -/
private theorem beth_three_eq : (Cardinal.beth 3 : Cardinal.{0}) = 2 ^ Cardinal.beth 2 := by
  have h23 : (3 : Ordinal) = Order.succ 2 := by rw [Order.succ_eq_add_one]; norm_num
  rw [h23, Cardinal.beth_succ]

/-- For n : ℕ, ℶ_{n+1} = 2^ℶₙ. -/
private theorem beth_nat_succ (n : ℕ) :
    (Cardinal.beth (↑(n + 1) : Ordinal) : Cardinal.{0}) =
    2 ^ Cardinal.beth (↑n : Ordinal) := by
  have hsucc : (↑(n + 1) : Ordinal) = Order.succ (↑n : Ordinal) := by
    rw [Order.succ_eq_add_one]
    push_cast
    ring
  rw [hsucc, Cardinal.beth_succ]

-- ============================================================
-- PART 2: The Third Beth Level
-- ============================================================

/-- **|𝒫(𝒫(ℝ))| = ℶ₃**: The doubly-iterated power set of ℝ is the third
    beth number.

    Proof chain:
    - |𝒫(𝒫(ℝ))| = 2^|𝒫(ℝ)|   (power set formula: Cardinal.mk_set)
    - |𝒫(ℝ)|    = ℶ₂           (parent: card_powerSet_real_eq_beth_two)
    - ℶ₃        = 2^ℶ₂         (beth recursion: Cardinal.beth_succ)
    Therefore |𝒫(𝒫(ℝ))| = ℶ₃. -/
theorem card_powerSet_powerSet_real_eq_beth_three :
    (#(Set (Set ℝ)) : Cardinal.{0}) = Cardinal.beth 3 := by
  -- |𝒫(𝒫(ℝ))| = 2^|𝒫(ℝ)| by power set formula
  rw [Cardinal.mk_set]
  -- |𝒫(ℝ)| = ℶ₂
  rw [CantorsTheoremOQ01.card_powerSet_real_eq_beth_two]
  -- 2^ℶ₂ = ℶ₃
  rw [← beth_three_eq]

/-- |𝒫(𝒫(ℝ))| > |𝒫(ℝ)| > |ℝ|: the hierarchy is strictly increasing. -/
theorem powerSet_powerSet_gt_powerSet_real :
    (#(Set ℝ) : Cardinal.{0}) < #(Set (Set ℝ)) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor (#(Set ℝ))

/-- |𝒫(𝒫(ℝ))| > |ℝ|: two levels of power sets strictly exceed ℝ. -/
theorem powerSet_powerSet_gt_real :
    (#ℝ : Cardinal.{0}) < #(Set (Set ℝ)) :=
  lt_trans CantorsTheoremOQ01.card_real_lt_card_powerSet_real
    powerSet_powerSet_gt_powerSet_real

/-- ℶ₃ > ℶ₂ > ℶ₁: the beth tower at levels 1–3 is strictly increasing. -/
theorem beth_two_lt_beth_three :
    (Cardinal.beth 2 : Cardinal.{0}) < Cardinal.beth 3 :=
  Cardinal.beth_strictMono (by exact_mod_cast (show (2 : ℕ) < 3 from by norm_num))

-- ============================================================
-- PART 3: General Iterated Power Set
-- ============================================================

/-- The n-th iterated power set of ℝ.
    - `iteratedPowerSet 0 = ℝ`
    - `iteratedPowerSet (n+1) = Set (iteratedPowerSet n)` -/
noncomputable def iteratedPowerSet : ℕ → Type
  | 0     => ℝ
  | n + 1 => Set (iteratedPowerSet n)

/-- `iteratedPowerSet 0 = ℝ`. -/
theorem iteratedPowerSet_zero : iteratedPowerSet 0 = ℝ := rfl

/-- `iteratedPowerSet 1 = Set ℝ = 𝒫(ℝ)`. -/
theorem iteratedPowerSet_one : iteratedPowerSet 1 = Set ℝ := rfl

/-- `iteratedPowerSet 2 = Set (Set ℝ) = 𝒫(𝒫(ℝ))`. -/
theorem iteratedPowerSet_two : iteratedPowerSet 2 = Set (Set ℝ) := rfl

/-- **General Beth Formula**: The n-th iterated power set of ℝ has cardinality ℶ_{n+1}.

    |𝒫⁰(ℝ)| = |ℝ| = 𝔠 = ℶ₁
    |𝒫¹(ℝ)| = |𝒫(ℝ)| = ℶ₂
    |𝒫²(ℝ)| = |𝒫(𝒫(ℝ))| = ℶ₃
    ...and so on. -/
theorem card_iteratedPowerSet_eq_beth (n : ℕ) :
    (#(iteratedPowerSet n) : Cardinal.{0}) = Cardinal.beth (↑(n + 1) : Ordinal) := by
  induction n with
  | zero =>
    -- |ℝ| = 𝔠 = ℶ₁
    simp only [iteratedPowerSet]
    rw [CantorsTheoremOQ01.card_real_eq_continuum,
        CantorsTheoremOQ01.beth_one_eq_continuum]
  | succ n ih =>
    -- |𝒫(iteratedPowerSet n)| = 2^|iteratedPowerSet n| = 2^ℶ_{n+1} = ℶ_{n+2}
    simp only [iteratedPowerSet]
    rw [Cardinal.mk_set, ih, ← beth_nat_succ (n + 1)]
    push_cast
    ring_nf

-- ============================================================
-- PART 4: Strict Tower Inequality
-- ============================================================

/-- The iterated power set tower is strictly increasing:
    |𝒫ⁿ(ℝ)| < |𝒫^{n+1}(ℝ)| for all n. -/
theorem iteratedPowerSet_strict_mono (n : ℕ) :
    (#(iteratedPowerSet n) : Cardinal.{0}) < #(iteratedPowerSet (n + 1)) := by
  simp only [iteratedPowerSet]
  rw [Cardinal.mk_set]
  exact Cardinal.cantor _

/-- For m < n, |𝒫ᵐ(ℝ)| < |𝒫ⁿ(ℝ)|: strict monotonicity throughout. -/
theorem iteratedPowerSet_lt_of_lt {m n : ℕ} (h : m < n) :
    (#(iteratedPowerSet m) : Cardinal.{0}) < #(iteratedPowerSet n) := by
  induction h with
  | refl => exact iteratedPowerSet_strict_mono m
  | step _ ih => exact lt_trans ih (iteratedPowerSet_strict_mono _)

-- ============================================================
-- PART 5: Beth Tower Summary
-- ============================================================

/-- **The beth tower at levels 0–3**:
    ℶ₀ = ℵ₀ = |ℕ| < ℶ₁ = 𝔠 = |ℝ| < ℶ₂ = |𝒫(ℝ)| < ℶ₃ = |𝒫(𝒫(ℝ))|. -/
theorem beth_tower_0_to_3 :
    (Cardinal.beth 0 : Cardinal.{0}) < Cardinal.beth 1 ∧
    (Cardinal.beth 1 : Cardinal.{0}) < Cardinal.beth 2 ∧
    (Cardinal.beth 2 : Cardinal.{0}) < Cardinal.beth 3 :=
  ⟨Cardinal.beth_strictMono (by exact_mod_cast (show (0 : ℕ) < 1 from by norm_num)),
   Cardinal.beth_strictMono (by exact_mod_cast (show (1 : ℕ) < 2 from by norm_num)),
   beth_two_lt_beth_three⟩

/-- **Main summary theorem**: The iterated power set hierarchy over ℝ.

    1. |𝒫(𝒫(ℝ))| = ℶ₃
    2. General formula: |𝒫ⁿ(ℝ)| = ℶ_{n+1} for all n
    3. The hierarchy is strictly increasing -/
theorem cantors_theorem_oq01oq02_summary :
    ((#(Set (Set ℝ)) : Cardinal.{0}) = Cardinal.beth 3) ∧
    (∀ n : ℕ, (#(iteratedPowerSet n) : Cardinal.{0}) = Cardinal.beth (↑(n + 1) : Ordinal)) ∧
    (∀ n : ℕ, (#(iteratedPowerSet n) : Cardinal.{0}) < #(iteratedPowerSet (n + 1))) :=
  ⟨card_powerSet_powerSet_real_eq_beth_three,
   card_iteratedPowerSet_eq_beth,
   iteratedPowerSet_strict_mono⟩

-- ============================================================
-- PART 6: König's Cofinality Constraint on |𝒫(ℝ)|
-- ============================================================

/-
  König's theorem (1905): For any infinite cardinal κ, cf(2^κ) > κ.
  Applied to κ = 𝔠: cf(2^𝔠) > 𝔠, i.e., cf(ℶ₂) > ℶ₁.

  This is the only ZFC constraint on the aleph-index of ℶ₂:
  If ℶ₂ = ℵ_α, then cf(ℵ_α) > 𝔠 = ℶ₁.

  Mathlib has this as `Cardinal.lt_cof_power`.
-/

/-- **König's Constraint**: The cofinality of |𝒫(ℝ)| = ℶ₂ strictly exceeds
    𝔠 = ℶ₁ = |ℝ|.

    This rules out ℶ₂ being any cardinal with cofinality ≤ 𝔠, for example:
    - ℵ_ω (cofinality ω = ℵ₀ ≤ 𝔠)
    - ℵ_{ω·2} (cofinality ω)
    - ℵ_{ω₁·ω} (cofinality ω)

    Only cardinals with cofinality > 𝔠 are candidates for the aleph-index of ℶ₂. -/
theorem konig_constraint_powerSet_real :
    (𝔠 : Cardinal.{0}) < (#(Set ℝ)).ord.cof := by
  rw [CantorsTheoremOQ01.card_powerSet_real_formula]
  exact Cardinal.lt_cof_power Cardinal.aleph0_le_continuum (by norm_num)

/-- König's Constraint generalized: for all n : ℕ, cf(ℶ_{n+1}) > ℶₙ.
    The cofinality of each beth level strictly exceeds the previous. -/
theorem konig_constraint_beth (n : ℕ) :
    (Cardinal.beth (↑n : Ordinal) : Cardinal.{0}) <
    (2 ^ Cardinal.beth (↑n : Ordinal) : Cardinal.{0}).ord.cof := by
  apply Cardinal.lt_cof_power _ (by norm_num)
  -- ℵ₀ = ℶ₀ ≤ ℶₙ (beth is monotone, 0 ≤ n in Ordinal)
  calc (ℵ₀ : Cardinal.{0}) = Cardinal.beth 0 := Cardinal.beth_zero.symm
    _ ≤ Cardinal.beth (↑n : Ordinal) :=
        Cardinal.beth_strictMono.monotone (Ordinal.zero_le _)

/-- The aleph-index of ℶ₂ (if it equals ℵ_α) must satisfy cf(ℵ_α) > 𝔠.
    Under GCH + CH, ℶ₂ = ℵ₂ which satisfies cf(ℵ₂) = ℵ₂ > 𝔠 = ℵ₁. -/
theorem aleph_index_lower_cofinality_bound
    (α : Ordinal.{0})
    (h : (#(Set ℝ) : Cardinal.{0}) = Cardinal.aleph α) :
    (𝔠 : Cardinal.{0}) < (Cardinal.aleph α).ord.cof := by
  rw [← h]
  exact konig_constraint_powerSet_real

/-
## Conclusion

**Beth hierarchy over ℝ:**
  ℶ₀ = ℵ₀ = |ℕ| < ℶ₁ = 𝔠 = |ℝ| < ℶ₂ = |𝒫(ℝ)| < ℶ₃ = |𝒫(𝒫(ℝ))| < ...

**Provable in ZFC (0 axioms):**
- |𝒫ⁿ(ℝ)| = ℶ_{n+1} for all n (general formula)
- König's constraint: cf(ℶ₂) > 𝔠 (rules out ℵ_ω, ℵ_{ω₁·ω}, etc.)
- The hierarchy is strictly increasing at each level

**Independent of ZFC (Easton's theorem):**
- The exact aleph-index of ℶ₂ = |𝒫(ℝ)|: consistent with any regular cardinal
  having cofinality > 𝔠. ZFC cannot prove ℶ₂ = ℵ₂ or ℶ₂ = ℵ₃ or any specific value.
-/

end CantorsTheoremOQ01OQ02

-- Export key theorems
#check CantorsTheoremOQ01OQ02.card_powerSet_powerSet_real_eq_beth_three
#check CantorsTheoremOQ01OQ02.card_iteratedPowerSet_eq_beth
#check CantorsTheoremOQ01OQ02.iteratedPowerSet_strict_mono
#check CantorsTheoremOQ01OQ02.konig_constraint_powerSet_real
#check CantorsTheoremOQ01OQ02.cantors_theorem_oq01oq02_summary
