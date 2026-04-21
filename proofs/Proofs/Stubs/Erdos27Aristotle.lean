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
  ((Finset.range M).filter fun m => ∀ c ∈ S.congruences, ¬((m + 1 : ℤ) ≡ c.residue [ZMOD c.modulus])).card

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
  unfold ErdosConjecture ErdosConjectureNegation
  constructor
  · intro ⟨C, hC, hEC⟩ hECN
    obtain ⟨ε, hε, N, hN, hbad⟩ := hECN C hC
    obtain ⟨S, hmod, halmost⟩ := hEC ε hε N hN
    exact hbad S hmod halmost
  · intro hnotECN
    push_neg at hnotECN
    exact hnotECN

-- Routine: uncoveredCount is bounded by M.
theorem uncoveredCount_le (S : CongruenceSystem) (M : ℕ) :
    uncoveredCount S M ≤ M := by
  unfold uncoveredCount
  calc ((Finset.range M).filter _).card
      ≤ (Finset.range M).card := Finset.card_filter_le _ _
    _ = M := Finset.card_range M

-- Routine: uncovered density is at most 1.
theorem asymptoticUncoveredDensity_le_one (S : CongruenceSystem) :
    asymptoticUncoveredDensity S ≤ 1 := by
  simp only [asymptoticUncoveredDensity]
  apply (Filter.liminf_le_limsup (f := atTop)
    ⟨1, Filter.eventually_of_forall (fun M => by
      split_ifs with h; exact le_refl 1
      exact div_le_one_of_le (by exact_mod_cast uncoveredCount_le S M)
                              (by exact_mod_cast Nat.zero_le M))⟩
    ⟨0, Filter.eventually_of_forall (fun M => by positivity)⟩).trans
  apply Filter.limsup_le_of_eventually_le
  apply Filter.eventually_of_forall
  intro M
  split_ifs with h
  · exact le_refl 1
  · exact div_le_one_of_le (by exact_mod_cast uncoveredCount_le S M)
                            (by exact_mod_cast Nat.zero_le M)

-- Routine: A perfect covering is a 0-almost covering.
theorem perfect_is_zero_almost (S : CongruenceSystem) (h : IsPerfectCovering S) :
    IsAlmostCovering S 0 := by
  show asymptoticUncoveredDensity S ≤ 0
  simp only [asymptoticUncoveredDensity]
  -- The uncoveredCount is 0 for all M ≥ 1 (every integer x is covered by h x)
  have huc : ∀ M : ℕ, M ≥ 1 →
      (if M = 0 then (1 : ℝ) else (uncoveredCount S M : ℝ) / M) = 0 := by
    intro M hM
    simp only [show M ≠ 0 from by omega, ite_false]
    have hzero : uncoveredCount S M = 0 := by
      simp only [uncoveredCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _
      -- h says (↑m + 1) is covered: ∃ c ∈ S.congruences, (↑m + 1) ≡ c.residue [...]
      -- The filter keeps elements where ∀ c, ¬(...), so push_neg to get ∃
      push_neg
      exact h (↑m + 1)
    simp [hzero]
  -- Function is eventually 0 → tends to 0 → liminf = 0 ≤ 0
  have htend : Tendsto (fun M => if M = 0 then (1 : ℝ) else (uncoveredCount S M : ℝ) / M)
      atTop (nhds 0) :=
    tendsto_const_nhds.congr'
      ((Filter.eventually_ge_atTop 1).mono (fun M hM => (huc M hM).symm))
  linarith [htend.liminf_eq]

-- Routine: IsAlmostCovering is monotone in e.
theorem almostCovering_mono {S : CongruenceSystem} {ε₁ ε₂ : ℝ}
    (h : IsAlmostCovering S ε₁) (hle : ε₁ ≤ ε₂) :
    IsAlmostCovering S ε₂ := le_trans h hle

end Erdos27Aristotle
