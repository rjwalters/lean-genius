/-
  Exact Cardinality of Transcendental Real Numbers

  Open Question (algebraic-numbers-countable-oq-02-oq-03):

  The parent proof (AlgebraicNumbersCountableOQ02.lean) establishes:
    1. ℝ is uncountable (¬Countable ℝ)
    2. The transcendental reals are uncountable (¬Set.Countable transcendentalReals)

  This file answers the follow-up: **what is the EXACT cardinality of the transcendentals?**

  **Answer**: The transcendental reals have exactly 𝔠 = 2^ℵ₀ elements — the same cardinality
  as ℝ itself. In particular, "almost all" real numbers are transcendental in the precise
  cardinality sense: the algebraic reals form a negligible ℵ₀-sized subset.

  **Key Results**:
  1. `card_transcendentalReals_eq_continuum` — #transcendentalReals = 𝔠
  2. `card_transcendentals_eq_card_reals`    — #transcendentalReals = #ℝ
  3. `card_algebraics_lt_card_transcendentals` — #algebraics < #transcendentals
  4. `cardinality_dichotomy`                 — the full cardinality picture

  **Proof Strategy**:
  - Upper bound: transcendentalReals ⊆ ℝ, so #transcendentalReals ≤ #ℝ = 𝔠
  - Lower bound: 𝔠 = #ℝ ≤ #(algebraics ∪ transcendentals) ≤ #algebraics + #transcendentals
                        ≤ ℵ₀ + #transcendentals = #transcendentals
    (The absorption ℵ₀ + κ = κ for κ ≥ ℵ₀ follows from Cardinal.add_eq_self.)

  **Mathematical Note**:
  This result shows the algebraic/transcendental dichotomy is maximally asymmetric:
  the countable algebraics are genuinely negligible compared to the continuum of transcendentals.
  Cantor's 1874 paper established both countability of algebraics and uncountability of ℝ,
  but this sharper cardinality equality for transcendentals is the natural completion.

  Tags: set-theory, cardinality, algebraic-numbers, transcendental-numbers, continuum
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Data.Set.Countable
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable
import Proofs.AlgebraicNumbersCountableOQ02

namespace AlgebraicNumbersCountableOQ02OQ03

open Cardinal AlgebraicNumbersCountable AlgebraicNumbersCountableOQ02

-- ============================================================
-- § 1: Setup — Reuse Definitions from Parent Files
-- ============================================================

-- We use `transcendentalReals := {x : ℝ | ¬IsAlgebraic ℚ x}` from OQ02.
-- We use `algebraic_reals_countable`, `card_algebraic_reals_eq_aleph0` from parent.

-- ============================================================
-- § 2: Partition Lemmas
-- ============================================================

/-- The algebraic and transcendental reals partition ℝ. -/
private theorem algebraic_trans_partition :
    {x : ℝ | IsAlgebraic ℚ x} ∪ (transcendentalReals : Set ℝ) = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, transcendentalReals, Set.mem_univ, iff_true]
  exact Classical.em _

/-- The algebraic and transcendental reals are disjoint. -/
private theorem algebraic_trans_disjoint :
    Disjoint ({x : ℝ | IsAlgebraic ℚ x}) (transcendentalReals : Set ℝ) := by
  rw [Set.disjoint_left]
  intro x hx ht
  exact ht hx

-- ============================================================
-- § 3: Cardinal Bounds on the Algebraic Reals
-- ============================================================

/-- The algebraic reals have cardinality at most ℵ₀ (countable). -/
private theorem card_algebraic_le_aleph0 :
    (#(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) : Cardinal) ≤ ℵ₀ :=
  le_aleph0_iff_set_countable.mpr algebraic_reals_countable

-- ============================================================
-- § 4: Cardinal Bounds on the Transcendental Reals
-- ============================================================

/-- **Upper bound**: transcendentals ⊆ ℝ, so their cardinality is at most 𝔠. -/
theorem card_transcendentals_le_continuum :
    (#(↑transcendentalReals : Set ℝ) : Cardinal) ≤ 𝔠 := by
  calc (#(↑transcendentalReals : Set ℝ) : Cardinal)
      ≤ #ℝ := Cardinal.mk_set_le transcendentalReals
    _ = 𝔠 := Cardinal.mk_real

/-- The transcendentals are at least ℵ₀-many (since they're uncountable). -/
private theorem card_transcendentals_ge_aleph0 :
    ℵ₀ ≤ (#(↑transcendentalReals : Set ℝ) : Cardinal) := by
  by_contra h
  push_neg at h
  exact transcendentals_uncountable (le_aleph0_iff_set_countable.mp h.le)

/-- The absorption lemma: ℵ₀ + κ = κ when ℵ₀ ≤ κ.

    Proof: ℵ₀ + κ ≤ κ + κ = κ (by Cardinal.add_eq_self), and κ ≤ ℵ₀ + κ trivially. -/
private theorem aleph0_add_of_ge {κ : Cardinal} (h : ℵ₀ ≤ κ) : ℵ₀ + κ = κ :=
  le_antisymm
    (calc ℵ₀ + κ ≤ κ + κ := add_le_add_right h κ
              _ = κ := Cardinal.add_eq_self h)
    (le_add_left κ ℵ₀)

/-- **Lower bound**: 𝔠 ≤ #transcendentalReals.

    Key chain:
      𝔠 = #ℝ ≤ #(algebraics ∪ transcendentals) ≤ #algebraics + #transcendentals
          ≤ ℵ₀ + #transcendentals = #transcendentals -/
theorem continuum_le_card_transcendentals :
    𝔠 ≤ (#(↑transcendentalReals : Set ℝ) : Cardinal) := by
  have h_alg := card_algebraic_le_aleph0
  have h_trans_ge := card_transcendentals_ge_aleph0
  have h_absorb : ℵ₀ + #(↑transcendentalReals : Set ℝ) = #(↑transcendentalReals : Set ℝ) :=
    aleph0_add_of_ge h_trans_ge
  -- The union bound: #ℝ ≤ #algebraics + #transcendentals
  have h_union_le : (#ℝ : Cardinal) ≤
      #(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) + #(↑transcendentalReals : Set ℝ) := by
    have h1 : (#(↑({x : ℝ | IsAlgebraic ℚ x} ∪ transcendentalReals) : Set ℝ) : Cardinal) ≤
        #(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) + #(↑transcendentalReals : Set ℝ) :=
      Cardinal.mk_union_le _ _
    rw [algebraic_trans_partition, Cardinal.mk_univ] at h1
    exact h1
  -- Chain: 𝔠 ≤ #algebraics + #transcendentals ≤ ℵ₀ + #transcendentals = #transcendentals
  calc 𝔠
      = #ℝ := Cardinal.mk_real.symm
    _ ≤ #(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) + #(↑transcendentalReals : Set ℝ) :=
          h_union_le
    _ ≤ ℵ₀ + #(↑transcendentalReals : Set ℝ) :=
          add_le_add_right h_alg _
    _ = #(↑transcendentalReals : Set ℝ) := h_absorb

-- ============================================================
-- § 5: Main Theorem — Exact Cardinality
-- ============================================================

/-- **Main Theorem**: The transcendental real numbers have exactly 𝔠 = 2^ℵ₀ elements.

    The transcendental reals are equinumerous with ℝ itself. This is the exact
    cardinality version of the uncountability result from AlgebraicNumbersCountableOQ02. -/
theorem card_transcendentalReals_eq_continuum :
    (#(↑transcendentalReals : Set ℝ) : Cardinal) = 𝔠 :=
  le_antisymm card_transcendentals_le_continuum continuum_le_card_transcendentals

-- ============================================================
-- § 6: Corollaries
-- ============================================================

/-- **Corollary 1**: The transcendental reals are equinumerous with ℝ itself. -/
theorem card_transcendentals_eq_card_reals :
    (#(↑transcendentalReals : Set ℝ) : Cardinal) = #ℝ := by
  rw [card_transcendentalReals_eq_continuum, Cardinal.mk_real]

/-- **Corollary 2**: There are strictly fewer algebraic reals than transcendental reals.

    The algebraic reals are ℵ₀-many; the transcendentals are 𝔠-many, with 𝔠 > ℵ₀. -/
theorem card_algebraics_lt_card_transcendentals :
    (#(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) : Cardinal) <
    #(↑transcendentalReals : Set ℝ) := by
  rw [card_transcendentalReals_eq_continuum]
  calc (#(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) : Cardinal)
      ≤ ℵ₀ := card_algebraic_le_aleph0
    _ < 𝔠 := Cardinal.aleph0_lt_continuum

/-- **Corollary 3**: The algebraic reals have the same cardinality as ℕ. -/
theorem card_algebraics_eq_aleph0 :
    (#(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) : Cardinal) = ℵ₀ := by
  apply le_antisymm card_algebraic_le_aleph0
  have := card_algebraic_reals_eq_aleph0
  -- card_algebraic_reals_eq_aleph0 : #{x : ℝ // IsAlgebraic ℚ x} = ℵ₀
  rw [← this]
  rfl

/-- **Complete cardinality picture** — Cantor's 1874 dichotomy, quantified precisely:
    - Algebraic reals: exactly ℵ₀ (countably infinite)
    - Transcendental reals: exactly 𝔠 = 2^ℵ₀ (continuum-many)
    - All reals: exactly 𝔠 = 2^ℵ₀ (same as transcendentals)

    The algebraics are negligible in cardinality — removing them from ℝ leaves a set of
    equal cardinality. -/
theorem cardinality_dichotomy :
    (#(↑{x : ℝ | IsAlgebraic ℚ x} : Set ℝ) : Cardinal) = ℵ₀ ∧
    (#(↑transcendentalReals : Set ℝ) : Cardinal) = 𝔠 ∧
    (#ℝ : Cardinal) = 𝔠 :=
  ⟨card_algebraics_eq_aleph0, card_transcendentalReals_eq_continuum, Cardinal.mk_real⟩

end AlgebraicNumbersCountableOQ02OQ03
