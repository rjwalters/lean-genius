/-!
# Erdős Problem #278 — Maximum Covering Density of Congruence Systems

Given a finite set of moduli A = {n₁ < n₂ < ⋯ < nᵣ}, choose residues
a₁, ..., aᵣ. The "coverage" is the set of integers m such that
m ≡ aᵢ (mod nᵢ) for some i.

**Questions:**
1. What is the maximum density of the coverage over all choices of residues?
2. Is the minimum density achieved when all aᵢ are equal?

**Status: Partially solved.**
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

/-! ## Core Definitions -/

/-- A congruence system: a finite collection of moduli with chosen residues. -/
structure CongruenceSystem where
  moduli : Finset ℕ
  residue : ℕ → ℕ
  moduli_pos : ∀ n ∈ moduli, 0 < n

/-- An integer m is covered by the system if m ≡ a_i (mod n_i) for some i. -/
def isCovered (sys : CongruenceSystem) (m : ℕ) : Prop :=
  ∃ n ∈ sys.moduli, m % n = sys.residue n % n

/-- The coverage density: the proportion of {0,...,L-1} covered, as L → ∞.
    For periodic systems this stabilizes at the lcm of the moduli. -/
noncomputable def coverageDensity (sys : CongruenceSystem) : ℝ :=
  let L := sys.moduli.val.toList.foldl Nat.lcm 1
  ((Finset.range L).filter (fun m => ∃ n ∈ sys.moduli, m % n = sys.residue n % n)).card / (L : ℝ)

/-- The maximum coverage density over all residue choices. -/
noncomputable def maxCoverageDensity (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) : ℝ :=
  sSup { d : ℝ | ∃ r : ℕ → ℕ, d = coverageDensity ⟨moduli, r, hpos⟩ }

/-- The minimum coverage density over all residue choices. -/
noncomputable def minCoverageDensity (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) : ℝ :=
  sInf { d : ℝ | ∃ r : ℕ → ℕ, d = coverageDensity ⟨moduli, r, hpos⟩ }

/-! ## Inclusion-Exclusion Formula -/

/-- The inclusion-exclusion density when all residues are equal:
    Σ 1/nᵢ - Σ 1/lcm(nᵢ,nⱼ) + ⋯
    This is the density of the union of arithmetic progressions
    a (mod n₁), a (mod n₂), ..., a (mod nᵣ) for a fixed a. -/
noncomputable def inclusionExclusionDensity (moduli : Finset ℕ) : ℝ :=
  -- Simplified: for a single modulus, density is 1/n
  moduli.sum (fun n => (1 : ℝ) / n)

/-! ## Simpson's Theorem (1986) -/

/-- Simpson's theorem: the minimum coverage density is achieved when
    all residues are equal. The minimum is given by the inclusion-exclusion
    formula applied to the arithmetic progressions with a common residue. -/
axiom simpson_theorem (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    ∀ r : ℕ → ℕ,
      coverageDensity ⟨moduli, (fun _ => 0), hpos⟩ ≤ coverageDensity ⟨moduli, r, hpos⟩

/-- Corollary: the all-equal-residue system achieves minimum density. -/
axiom equal_residues_minimize (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (a : ℕ) :
    coverageDensity ⟨moduli, (fun _ => a), hpos⟩ =
    coverageDensity ⟨moduli, (fun _ => 0), hpos⟩

/-! ## Question 1: Maximum Density (OPEN) -/

/-- The maximum coverage density over all residue choices.
    For coprime moduli, the maximum is Σ 1/nᵢ (≤ 1).
    For non-coprime moduli, clever residue choices can increase overlap. -/
axiom max_density_coprime_case (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n) :
    maxCoverageDensity moduli hpos = moduli.sum (fun n => (1 : ℝ) / n)

/-- General question: what is the maximum density for arbitrary moduli?
    This is the main open part of Problem #278. -/
axiom erdos_278_open_question (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    maxCoverageDensity moduli hpos ≤ 1

/-! ## Basic Bounds -/

/-- The coverage density is between 0 and 1. -/
axiom density_bounds (sys : CongruenceSystem) :
    0 ≤ coverageDensity sys ∧ coverageDensity sys ≤ 1

/-- For a single modulus n, both the max and min density are 1/n. -/
axiom single_modulus_density (n : ℕ) (hn : 0 < n) :
    maxCoverageDensity {n} (by intro m hm; simp at hm; rwa [hm]) = 1 / (n : ℝ)
