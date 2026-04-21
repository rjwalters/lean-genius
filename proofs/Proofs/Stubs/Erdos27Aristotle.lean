/-
  Aristotle targets for Erdos Problem #27
  Routine supporting lemmas for automated proof search.
  See Erdos27Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main disproof (Filaseta-Ford-Konyagin-Pomerance-Yu)
  - Routine supporting facts: logical equivalences, monotonicity, basic density bounds
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos27Aristotle

open Finset Real Filter Topology

/-- A congruence class: residue a modulo n with n > 0. -/
structure Congruence where
  residue : ℤ
  modulus : ℕ
  modulus_pos : modulus > 0

/-- A congruence system with distinct moduli. -/
structure CongruenceSystem where
  congruences : Finset Congruence
  distinct_moduli : ∀ c₁ ∈ congruences, ∀ c₂ ∈ congruences,
    c₁.modulus = c₂.modulus → c₁ = c₂

/-- An integer is covered if it satisfies some congruence. -/
def CongruenceSystem.covers (S : CongruenceSystem) (x : ℤ) : Prop :=
  ∃ c ∈ S.congruences, x ≡ c.residue [ZMOD c.modulus]

/-- The number of uncovered integers in {1,...,M}. -/
noncomputable def uncoveredCount (S : CongruenceSystem) (M : ℕ) : ℕ :=
  ((Finset.range M).filter fun m : ℕ => ∀ c ∈ S.congruences,
    ¬((m : ℤ) + 1 ≡ c.residue [ZMOD c.modulus])).card

/-- Asymptotic uncovered density. -/
noncomputable def asymptoticUncoveredDensity (S : CongruenceSystem) : ℝ :=
  liminf (fun M => if M = 0 then 1 else (uncoveredCount S M : ℝ) / M) atTop

/-- e-almost covering: uncovered density <= e. -/
def IsAlmostCovering (S : CongruenceSystem) (ε : ℝ) : Prop :=
  asymptoticUncoveredDensity S ≤ ε

/-- Perfect covering: every integer is covered. -/
def IsPerfectCovering (S : CongruenceSystem) : Prop :=
  ∀ x : ℤ, S.covers x

/-- Moduli in range [N, M]. -/
def HasModuliInRange (S : CongruenceSystem) (N M : ℕ) : Prop :=
  ∀ c ∈ S.congruences, N ≤ c.modulus ∧ c.modulus ≤ M

/-- Moduli in range [N, floor(C*N)]. -/
def HasModuliInCRange (S : CongruenceSystem) (N : ℕ) (C : ℝ) : Prop :=
  HasModuliInRange S N (Nat.floor (C * N))

/-- Erdos conjecture: exists C > 1, forall e > 0, forall N >= 1, exists S with moduli in [N, CN] that is e-almost covering. -/
def ErdosConjecture : Prop :=
  ∃ C : ℝ, C > 1 ∧ ∀ ε > 0, ∀ N : ℕ, N ≥ 1 →
    ∃ S : CongruenceSystem, HasModuliInCRange S N C ∧ IsAlmostCovering S ε

/-- Negation: forall C > 1, exists e > 0, exists N >= 1, no e-almost covering exists with moduli in [N, CN]. -/
def ErdosConjectureNegation : Prop :=
  ∀ C : ℝ, C > 1 → ∃ ε > 0, ∃ N : ℕ, N ≥ 1 ∧
    ∀ S : CongruenceSystem, HasModuliInCRange S N C → ¬IsAlmostCovering S ε

-- Routine: The conjecture and its negation are logical opposites.
-- By de Morgan: exists C, forall e, forall N, exists S, P <-> not (forall C, exists e, exists N, forall S, not P)
theorem conjecture_dichotomy : ErdosConjecture ↔ ¬ErdosConjectureNegation := by
  constructor
  · intro ⟨C, hC, h⟩ hContra
    obtain ⟨ε, hε, N, hN, hS⟩ := hContra C hC
    obtain ⟨S, hmod, halmost⟩ := h ε hε N hN
    exact hS S hmod halmost
  · intro h
    unfold ErdosConjectureNegation at h
    push_neg at h
    exact h

-- Routine: uncoveredCount is bounded by M.
theorem uncoveredCount_le (S : CongruenceSystem) (M : ℕ) :
    uncoveredCount S M ≤ M := by
  unfold uncoveredCount
  have h := Finset.card_filter_le (Finset.range M)
    (fun m : ℕ => ∀ c ∈ S.congruences, ¬((m : ℤ) + 1 ≡ c.residue [ZMOD c.modulus]))
  rwa [Finset.card_range] at h

-- Routine: uncovered density is at most 1.
theorem asymptoticUncoveredDensity_le_one (S : CongruenceSystem) :
    asymptoticUncoveredDensity S ≤ 1 := by
  unfold asymptoticUncoveredDensity
  rw [Filter.liminf_eq]
  apply csSup_le
  · -- Set is nonempty: 0 is an eventual lower bound
    exact ⟨0, Filter.eventually_atTop.mpr ⟨1, fun M hM => by
      have hpos : 0 < M := Nat.lt_of_lt_of_le Nat.one_pos hM
      rw [if_neg (Nat.pos_iff_ne_zero.mp hpos)]
      exact div_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _)⟩⟩
  · -- Every eventual lower bound is ≤ 1
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    rw [Filter.eventually_atTop] at ha
    obtain ⟨N, hN⟩ := ha
    have h := hN (N + 1) (Nat.le_succ N)
    rw [if_neg (Nat.succ_ne_zero N)] at h
    exact h.trans (by
      rw [div_le_one (by exact_mod_cast Nat.succ_pos N)]
      exact_mod_cast uncoveredCount_le S (N + 1))

-- Routine: A perfect covering is a 0-almost covering.
theorem perfect_is_zero_almost (S : CongruenceSystem) (h : IsPerfectCovering S) :
    IsAlmostCovering S 0 := by
  unfold IsAlmostCovering asymptoticUncoveredDensity
  have hzero : ∀ M, uncoveredCount S M = 0 := by
    intro M
    unfold uncoveredCount
    rw [Finset.card_eq_zero]
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and,
               not_forall, not_not]
    intro _
    obtain ⟨c, hc, hcov⟩ := h ((m : ℤ) + 1)
    exact ⟨c, hc, hcov⟩
  rw [Filter.liminf_eq]
  apply csSup_le
  · -- Set is nonempty: 0 is an eventual lower bound
    exact ⟨0, Filter.eventually_atTop.mpr ⟨1, fun M hM => by
      have hpos : 0 < M := Nat.lt_of_lt_of_le Nat.one_pos hM
      rw [if_neg (Nat.pos_iff_ne_zero.mp hpos), hzero M]
      norm_num⟩⟩
  · -- Every eventual lower bound is ≤ 0
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    rw [Filter.eventually_atTop] at ha
    obtain ⟨N, hN⟩ := ha
    have h := hN (N + 1) (Nat.le_succ N)
    rw [if_neg (Nat.succ_ne_zero N), hzero (N + 1)] at h
    simpa using h

-- Routine: IsAlmostCovering is monotone in e.
theorem almostCovering_mono {S : CongruenceSystem} {ε₁ ε₂ : ℝ}
    (h : IsAlmostCovering S ε₁) (hle : ε₁ ≤ ε₂) :
    IsAlmostCovering S ε₂ :=
  le_trans h hle

end Erdos27Aristotle
