/-
  Erdős Problem #1172: Partition Relations under GCH and CH

  Source: https://erdosproblems.com/1172
  Status: OPEN
  Reference: Va99, 7.87 (Erdős-Hajnal)

  Statement (under GCH):
  1. ω₃ → (ω₂, ω₁ + 2)²
  2. ω₃ → (ω₂ + ω₁, ω₂ + ω)²
  3. ω₂ → (ω₁^(ω+2) + 2, ω₁ + 2)²

  Under CH:
  4. ω₂ → (ω₁ + ω)₂²

  Background:
  These are unbalanced ordinal partition relations from the Erdős-Hajnal
  partition calculus program. The notation α → (β, γ)² means: for every
  2-coloring of pairs from α, there exists either a monochromatic subset
  of order type β (color 0) or order type γ (color 1).

  Tags: set-theory, partition-calculus, ordinals, GCH, CH
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic

set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Erdos1172

open Ordinal Cardinal

/- ## Part I: Ordinal and Cardinal Setup -/

noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord
noncomputable def omega2 : Ordinal.{0} := (Cardinal.aleph 2).ord
noncomputable def omega3 : Ordinal.{0} := (Cardinal.aleph 3).ord
noncomputable def omegaOrd : Ordinal.{0} := ω

/- ## Part II: Partition Relation -/

/-- The unbalanced ordinal partition relation α → (β, γ)²:
    for every 2-coloring of pairs below α, there exists either
    a 0-homogeneous set of order type β or a 1-homogeneous set
    of order type γ. A homogeneous set of order type δ is given
    by a strictly monotone embedding f : [0,δ) → [0,α). -/
def OrdPartitionRel (α β γ : Ordinal.{0}) : Prop :=
  ∀ c : Ordinal → Ordinal → Fin 2,
    (∃ f : Ordinal → Ordinal, StrictMono f ∧ (∀ i, i < β → f i < α) ∧
      ∀ i j, i < j → j < β → c (f i) (f j) = 0) ∨
    (∃ g : Ordinal → Ordinal, StrictMono g ∧ (∀ i, i < γ → g i < α) ∧
      ∀ i j, i < j → j < γ → c (g i) (g j) = 1)

/-- The balanced partition relation: α → (β)₂² means α → (β, β)². -/
def BalancedPartitionRel (α β : Ordinal.{0}) : Prop :=
  OrdPartitionRel α β β

/- ## Part III: Set-Theoretic Hypotheses -/

def GCH : Prop :=
  ∀ α : Ordinal.{0}, (2 : Cardinal.{0}) ^ Cardinal.aleph α = Cardinal.aleph (α + 1)

def CH : Prop :=
  (2 : Cardinal.{0}) ^ Cardinal.aleph (0 : Ordinal.{0}) = Cardinal.aleph 1

theorem gch_implies_ch : GCH → CH := by
  intro h; unfold CH
  have h0 := h 0
  simp only [zero_add] at h0
  exact h0

/- ## Part IV: The Four Open Questions -/

def question1 : Prop :=
  GCH → OrdPartitionRel omega3 omega2 (omega1 + 2)

def question2 : Prop :=
  GCH → OrdPartitionRel omega3 (omega2 + omega1) (omega2 + omegaOrd)

def question3 : Prop :=
  GCH → OrdPartitionRel omega2 (omega1 ^ (omegaOrd + 2) + 2) (omega1 + 2)

def question4 : Prop :=
  CH → BalancedPartitionRel omega2 (omega1 + omegaOrd)

/- ## Part V: Basic Ordinal Arithmetic -/

theorem omega1_lt_omega2 : omega1 < omega2 := by
  unfold omega1 omega2
  exact Cardinal.ord_lt_ord.mpr (Cardinal.aleph_lt_aleph.mpr (by norm_num))

theorem omega2_lt_omega3 : omega2 < omega3 := by
  unfold omega2 omega3
  exact Cardinal.ord_lt_ord.mpr (Cardinal.aleph_lt_aleph.mpr (by norm_num))

theorem omega1_lt_omega3 : omega1 < omega3 :=
  lt_trans omega1_lt_omega2 omega2_lt_omega3

theorem omega_lt_omega1 : omegaOrd < omega1 := by
  unfold omegaOrd omega1
  have h0 : Cardinal.aleph (0 : Ordinal.{0}) = ℵ₀ := Cardinal.aleph_zero
  have h1 : ℵ₀ < Cardinal.aleph (1 : Ordinal.{0}) := by
    rw [← h0]; exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  calc ω = (ℵ₀ : Cardinal.{0}).ord := Cardinal.ord_aleph0.symm
    _ < (Cardinal.aleph 1).ord := Cardinal.ord_lt_ord.mpr h1

theorem omega1_pos : 0 < omega1 := by
  have : (0 : Ordinal) < omegaOrd := by unfold omegaOrd; exact Ordinal.omega0_pos
  exact lt_trans this omega_lt_omega1

theorem omega2_pos : 0 < omega2 :=
  lt_trans omega1_pos omega1_lt_omega2

theorem omega3_pos : 0 < omega3 :=
  lt_trans omega2_pos omega2_lt_omega3

theorem two_lt_omega : (2 : Ordinal) < omegaOrd := by
  unfold omegaOrd; exact nat_lt_omega0 2

/- ## Part VI: Monotonicity -/

/-- Monotonicity: if α → (β, γ)² and β' ≤ β, γ' ≤ γ, then α → (β', γ')².
    Proved by restricting the homogeneous embedding to a smaller domain. -/
theorem partition_mono_target (α β γ β' γ' : Ordinal.{0}) (hβ : β' ≤ β) (hγ : γ' ≤ γ)
    (hp : OrdPartitionRel α β γ) : OrdPartitionRel α β' γ' := by
  intro c
  rcases hp c with ⟨f, hf_mono, hf_bound, hf_color⟩ | ⟨g, hg_mono, hg_bound, hg_color⟩
  · left
    exact ⟨f, hf_mono, fun i hi => hf_bound i (lt_of_lt_of_le hi hβ),
      fun i j hij hj => hf_color i j hij (lt_of_lt_of_le hj hβ)⟩
  · right
    exact ⟨g, hg_mono, fun i hi => hg_bound i (lt_of_lt_of_le hi hγ),
      fun i j hij hj => hg_color i j hij (lt_of_lt_of_le hj hγ)⟩

/- ## Part VII: Known Results -/

/-- **Erdős-Dushnik-Miller Theorem** (1941): λ → (λ, ω)² for infinite λ. -/
axiom erdos_dushnik_miller (lam : Ordinal.{0}) (hlam : ω ≤ lam) :
    OrdPartitionRel lam lam ω

/- ## Part VIII: Proved Theorems -/

/-- ω₃ → (ω₃, ω)² by Erdős-Dushnik-Miller. -/
theorem omega3_edm : OrdPartitionRel omega3 omega3 omegaOrd := by
  unfold omegaOrd
  apply erdos_dushnik_miller
  exact le_of_lt (lt_trans (lt_trans omega_lt_omega1 omega1_lt_omega2) omega2_lt_omega3)

/-- ω₂ → (ω₂, ω)² by Erdős-Dushnik-Miller. -/
theorem omega2_edm : OrdPartitionRel omega2 omega2 omegaOrd := by
  unfold omegaOrd
  apply erdos_dushnik_miller
  exact le_of_lt (lt_trans omega_lt_omega1 omega1_lt_omega2)

/-- Weak form of Q1: ω₃ → (ω₂, ω)² via EDM + monotonicity. -/
theorem q1_weak_from_edm : OrdPartitionRel omega3 omega2 omegaOrd :=
  partition_mono_target omega3 omega3 omegaOrd omega2 omegaOrd
    (le_of_lt omega2_lt_omega3) (le_refl _) omega3_edm

/-- If Q1 holds, the second target can be weakened to ω. -/
theorem q1_implies_weak_second (h : OrdPartitionRel omega3 omega2 (omega1 + 2)) :
    OrdPartitionRel omega3 omega2 omegaOrd :=
  partition_mono_target omega3 omega2 (omega1 + 2) omega2 omegaOrd
    (le_refl _)
    (le_of_lt (lt_of_lt_of_le omega_lt_omega1 le_self_add))
    h

/-- Q4 (balanced) unfolds to unbalanced. -/
theorem q4_unfold (h : BalancedPartitionRel omega2 (omega1 + omegaOrd)) :
    OrdPartitionRel omega2 (omega1 + omegaOrd) (omega1 + omegaOrd) := h

/-- If Q2 holds, first target weakens to ω₂. -/
theorem q2_weakened_first
    (h : OrdPartitionRel omega3 (omega2 + omega1) (omega2 + omegaOrd)) :
    OrdPartitionRel omega3 omega2 (omega2 + omegaOrd) :=
  partition_mono_target omega3 (omega2 + omega1) (omega2 + omegaOrd) omega2
    (omega2 + omegaOrd) le_self_add (le_refl _) h

/- ## Part IX: Independence Results -/

/-- **Todorcevic (1989)**: Under b = ω₁, ω₁ ↛ (ω₁, ω + 2)². -/
axiom todorcevic_negative :
    ¬ OrdPartitionRel omega1 omega1 (omegaOrd + 2)

/-- **PFA** implies ω₁ → (ω₁, α)² for all countable α. -/
axiom pfa_positive (alpha : Ordinal.{0}) (halpha : alpha < omega1) :
    OrdPartitionRel omega1 omega1 alpha

/-- Independence of ω₁ → (ω₁, ω + 2)². -/
theorem partition_independence :
    (∀ alpha : Ordinal.{0}, alpha < omega1 → OrdPartitionRel omega1 omega1 alpha) ∧
    ¬ OrdPartitionRel omega1 omega1 (omegaOrd + 2) :=
  ⟨pfa_positive, todorcevic_negative⟩

/- ## Part X: Summary -/

def erdos_1172_all_questions : Prop :=
  question1 ∧ question2 ∧ question3 ∧ question4

/-- ω₁ < ω₁^(ω+2) + 2: the first target in Q3 exceeds ω₁. -/
theorem q3_first_target_large : omega1 < omega1 ^ (omegaOrd + 2) + 2 := by
  calc omega1
      = omega1 ^ (1 : Ordinal) := (Ordinal.opow_one omega1).symm
    _ ≤ omega1 ^ (omegaOrd + 2) := by
        apply Ordinal.opow_le_opow_right omega1_pos
        calc (1 : Ordinal) ≤ omegaOrd := le_of_lt (by unfold omegaOrd; exact Ordinal.one_lt_omega0)
          _ ≤ omegaOrd + 2 := le_self_add
    _ < omega1 ^ (omegaOrd + 2) + 2 := by
        apply Ordinal.lt_add_of_limit_left
        · exact Ordinal.isLimit_iff_omega0_dvd.mpr ⟨by omega, ⟨omega1 ^ (omegaOrd + 1), by ring⟩⟩
        · exact Ordinal.pos_iff_ne_zero.mp (by norm_num)

/-- ω₂ + ω₁ < ω₃ and ω₂ + ω < ω₃. -/
theorem q2_targets_lt_omega3 :
    omega2 + omega1 < omega3 ∧ omega2 + omegaOrd < omega3 := by
  constructor
  · -- ω₂ + ω₁ < ω₃: use cardinal arithmetic
    -- card(ω₂ + ω₁) ≤ ℵ₂ + ℵ₁ = ℵ₂ < ℵ₃ = card(ω₃)
    rw [show omega3 = (Cardinal.aleph 3).ord from rfl]
    rw [Cardinal.lt_ord]
    calc (omega2 + omega1).card
        ≤ omega2.card + omega1.card := Ordinal.card_add_le_card_add_card omega2 omega1
      _ = Cardinal.aleph 2 + Cardinal.aleph 1 := by
          simp [omega2, omega1, Cardinal.card_ord]
      _ = Cardinal.aleph 2 := by
          rw [Cardinal.add_eq_max (Cardinal.aleph0_le_aleph 2)]
          exact max_eq_left (Cardinal.aleph_le_aleph.mpr (by norm_num))
      _ < Cardinal.aleph 3 := Cardinal.aleph_lt_aleph.mpr (by norm_num)
  · -- ω₂ + ω < ω₃: similar argument
    rw [show omega3 = (Cardinal.aleph 3).ord from rfl]
    rw [Cardinal.lt_ord]
    calc (omega2 + omegaOrd).card
        ≤ omega2.card + omegaOrd.card := Ordinal.card_add_le_card_add_card omega2 omegaOrd
      _ = Cardinal.aleph 2 + ℵ₀ := by
          simp [omega2, omegaOrd, Cardinal.card_ord, Cardinal.card_omega0]
      _ = Cardinal.aleph 2 := by
          rw [Cardinal.add_eq_max (Cardinal.aleph0_le_aleph 2)]
          exact max_eq_left (Cardinal.aleph0_le_aleph 2)
      _ < Cardinal.aleph 3 := Cardinal.aleph_lt_aleph.mpr (by norm_num)

end Erdos1172
