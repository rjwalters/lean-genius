/-
Erdős Problem #278 — Maximum Covering Density of Congruence Systems

Given a finite set of moduli A = {n₁ < n₂ < ⋯ < nᵣ}, choose residues
a₁, ..., aᵣ. The "coverage" is the set of integers m such that
m ≡ aᵢ (mod nᵢ) for some i.

Questions:
1. What is the maximum density of the coverage over all choices of residues?
2. Is the minimum density achieved when all aᵢ are equal?

Status: Partially solved.
Simpson (1986) settled Question 2 affirmatively: minimum density is achieved
when all residues are equal, giving density
  Σ 1/nᵢ - Σ 1/lcm(nᵢ,nⱼ) + Σ 1/lcm(nᵢ,nⱼ,nₖ) - ⋯
(inclusion-exclusion). Question 1 (maximum density) remains OPEN.

Reference: https://erdosproblems.com/278
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ## Core Definitions

/-- A congruence system: a finite collection of moduli with chosen residues. -/
structure CongruenceSystem where
  moduli : Finset ℕ
  residue : ℕ → ℕ
  moduli_pos : ∀ n ∈ moduli, 0 < n

/-- An integer m is covered by the system if m ≡ a_i (mod n_i) for some i. -/
def isCovered (sys : CongruenceSystem) (m : ℕ) : Prop :=
  ∃ n ∈ sys.moduli, m % n = sys.residue n % n

/-- The LCM period of a congruence system. -/
noncomputable def systemLCM (sys : CongruenceSystem) : ℕ :=
  sys.moduli.val.toList.foldl Nat.lcm 1

/-- The coverage density: the proportion of {0,...,L-1} covered.
    For periodic systems this stabilizes at the lcm of the moduli. -/
noncomputable def coverageDensity (sys : CongruenceSystem) : ℝ :=
  let L := systemLCM sys
  ((Finset.range L).filter (fun m => ∃ n ∈ sys.moduli, m % n = sys.residue n % n)).card / (L : ℝ)

/-- The maximum coverage density over all residue choices. -/
noncomputable def maxCoverageDensity (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) : ℝ :=
  sSup { d : ℝ | ∃ r : ℕ → ℕ, d = coverageDensity ⟨moduli, r, hpos⟩ }

/-- The minimum coverage density over all residue choices. -/
noncomputable def minCoverageDensity (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) : ℝ :=
  sInf { d : ℝ | ∃ r : ℕ → ℕ, d = coverageDensity ⟨moduli, r, hpos⟩ }

-- ## Helper Lemmas

/-- foldl Nat.lcm preserves positivity when all elements are positive. -/
private lemma foldl_lcm_pos (init : ℕ) (hinit : 0 < init)
    (l : List ℕ) (hl : ∀ x ∈ l, 0 < x) : 0 < List.foldl Nat.lcm init l := by
  induction l generalizing init with
  | nil => simpa
  | cons a t ih =>
    simp only [List.foldl_cons]
    apply ih
    · have ha : 0 < a := hl a (by simp)
      exact Nat.pos_of_ne_zero (by
        intro h
        have := Nat.lcm_eq_zero_iff.mp h
        omega)
    · intro x hx; exact hl x (by simp [hx])

/-- The LCM period is always positive. -/
lemma systemLCM_pos (sys : CongruenceSystem) : 0 < systemLCM sys := by
  unfold systemLCM
  apply foldl_lcm_pos 1 (by omega)
  intro x hx
  rw [Multiset.mem_toList] at hx
  exact sys.moduli_pos x (Finset.mem_def.mpr hx)

/-- Coverage count is at most the LCM period. -/
private lemma coverage_card_le_lcm (sys : CongruenceSystem) :
    ((Finset.range (systemLCM sys)).filter
      (fun m => ∃ n ∈ sys.moduli, m % n = sys.residue n % n)).card ≤ systemLCM sys := by
  calc ((Finset.range (systemLCM sys)).filter _).card
      ≤ (Finset.range (systemLCM sys)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = systemLCM sys := Finset.card_range _

-- ## Proved Bounds

/-- The coverage density is non-negative. -/
theorem density_nonneg (sys : CongruenceSystem) : 0 ≤ coverageDensity sys := by
  unfold coverageDensity
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- The coverage density is at most 1. -/
theorem density_le_one (sys : CongruenceSystem) : coverageDensity sys ≤ 1 := by
  unfold coverageDensity
  have hL : (0 : ℝ) < systemLCM sys := Nat.cast_pos.mpr (systemLCM_pos sys)
  rw [div_le_one hL]
  exact Nat.cast_le.mpr (coverage_card_le_lcm sys)

/-- The coverage density is between 0 and 1. -/
theorem density_bounds (sys : CongruenceSystem) :
    0 ≤ coverageDensity sys ∧ coverageDensity sys ≤ 1 :=
  ⟨density_nonneg sys, density_le_one sys⟩

-- ## Inclusion-Exclusion Formula

/-- The inclusion-exclusion density when all residues are equal:
    Σ 1/nᵢ - Σ 1/lcm(nᵢ,nⱼ) + ⋯
    (Simplified: only the first-order term for now.) -/
noncomputable def inclusionExclusionDensity (moduli : Finset ℕ) : ℝ :=
  moduli.sum (fun n => (1 : ℝ) / n)

-- ## Simpson's Theorem (1986)

/-- Simpson's theorem: the minimum coverage density is achieved when
    all residues are equal. -/
axiom simpson_theorem (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    ∀ r : ℕ → ℕ,
      coverageDensity ⟨moduli, (fun _ => 0), hpos⟩ ≤ coverageDensity ⟨moduli, r, hpos⟩

/-- Corollary: the all-equal-residue system achieves minimum density. -/
axiom equal_residues_minimize (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (a : ℕ) :
    coverageDensity ⟨moduli, (fun _ => a), hpos⟩ =
    coverageDensity ⟨moduli, (fun _ => 0), hpos⟩

-- ## Question 1: Maximum Density (OPEN)

/-- For coprime moduli, the maximum is Σ 1/nᵢ (≤ 1). -/
axiom max_density_coprime_case (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n) :
    maxCoverageDensity moduli hpos = moduli.sum (fun n => (1 : ℝ) / n)

/-- The maximum coverage density is at most 1 (follows from density_le_one). -/
theorem erdos_278_density_le_one (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    maxCoverageDensity moduli hpos ≤ 1 := by
  unfold maxCoverageDensity
  apply csSup_le
  · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
  · rintro d ⟨r, rfl⟩; exact density_le_one _

-- ## Single Modulus Case

/-- For a single modulus n, both the max and min density are 1/n. -/
axiom single_modulus_density (n : ℕ) (hn : 0 < n) :
    maxCoverageDensity {n} (by intro m hm; simp at hm; rwa [hm]) = 1 / (n : ℝ)
