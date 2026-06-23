/-
  Erdős Problem #910 - OQ01: Connected Subsets of Euclidean Space
  Complete formalization with 0 sorries.

  Source: https://erdosproblems.com/910
  Status: DISPROVED (Rudin 1958, under CH)

  Statement:
  Two questions about connected sets in ℝⁿ:

  (1) Does every connected set in ℝⁿ contain a connected subset which is
      not a point and not homeomorphic to the original set?

  (2) If n ≥ 2, does every connected set in ℝⁿ contain more than 2^ℵ₀
      many connected subsets?

  Both questions answered NO by Mary Ellen Rudin (1958) under CH.

  This file provides a clean formalization with:
  - All theorems proved (0 sorries)
  - 1 axiom encoding Rudin's deep construction result
  - Nontriviality included as part of the axiom

  References:
  [Er82e] Erdős, P. "Personal reminiscences and remarks" (1982)
  [Ru58] Rudin, M.E. "A connected subset of the plane"
         Fundamenta Mathematicae 46 (1958), 15-24
-/

import Mathlib

open Set Cardinal

namespace Erdos910

variable {X : Type*} [TopologicalSpace X]

-- ## Definitions

/-- The set of all connected subsets of a given set S -/
def connectedSubsetsOf (S : Set X) : Set (Set X) :=
  { T | T ⊆ S ∧ IsConnected T }

/-- Two sets are homeomorphic as subspaces -/
def AreHomeomorphic (S T : Set X) : Prop :=
  Nonempty (S ≃ₜ T)

/-- A set has the "diverse subsets" property if it has a proper connected
    subset that is neither a singleton nor homeomorphic to the whole -/
def HasDiverseConnectedSubset (S : Set X) : Prop :=
  ∃ T : Set X, T ⊆ S ∧ T ≠ S ∧ IsConnected T ∧
    (∃ x y : X, x ∈ T ∧ y ∈ T ∧ x ≠ y) ∧
    ¬AreHomeomorphic T S

/-- A "Rudin set" is a connected set where every proper connected subset
    is either a point or homeomorphic to the whole -/
def IsRudinSet (S : Set X) : Prop :=
  IsConnected S ∧
  (∀ T : Set X, T ⊆ S → T ≠ S → IsConnected T →
    (∃! x, T = {x}) ∨ AreHomeomorphic T S)

-- ## Homeomorphism basics

theorem areHomeomorphic_refl (S : Set X) : AreHomeomorphic S S :=
  ⟨Homeomorph.refl S⟩

theorem areHomeomorphic_symm {S T : Set X} (h : AreHomeomorphic S T) :
    AreHomeomorphic T S :=
  h.map Homeomorph.symm

-- ## Erdős's conjectures (specialized to ℝ × ℝ to avoid universe issues)

/-- Erdős's first conjecture: every connected set in ℝ² has diverse subsets -/
def erdosFirstConjecture : Prop :=
  ∀ (S : Set (ℝ × ℝ)),
    IsConnected S → HasDiverseConnectedSubset S

/-- The cardinality of connected subsets of S -/
noncomputable def connectedSubsetCardinality (S : Set X) : Cardinal :=
  #(connectedSubsetsOf S)

/-- Erdős's second conjecture: connected sets in ℝ² have > 2^ℵ₀ connected subsets -/
def erdosSecondConjecture : Prop :=
  ∀ (S : Set (ℝ × ℝ)),
    IsConnected S → connectedSubsetCardinality S > Cardinal.continuum

-- ## Rudin's axiom

/-- Rudin's theorem (1958): Under CH, there exists a connected planar set that is
    a Rudin set with exactly continuum-many connected subsets.
    We encode this deep topological construction as an axiom, including
    nontriviality which follows from having continuum-many connected subsets. -/
axiom rudin_theorem_ch :
  Cardinal.continuum = aleph 1 →
  ∃ (S : Set (ℝ × ℝ)),
    IsRudinSet S ∧
    connectedSubsetCardinality S = Cardinal.continuum ∧
    Set.Nontrivial S

-- ## Main theorems (all proved, 0 sorries)

/-- Rudin sets have no diverse connected subsets.
    Every proper connected subset is either a singleton or homeomorphic to the whole. -/
theorem rudin_set_no_diverse_subset (S : Set X) (hS : IsRudinSet S) :
    ¬HasDiverseConnectedSubset S := by
  intro ⟨T, hTsub, hTne, hTconn, ⟨x, y, hx, hy, hxy⟩, hnotHomeo⟩
  have := hS.2 T hTsub hTne hTconn
  cases this with
  | inl hsing =>
    obtain ⟨z, hz⟩ := hsing
    have hxz : x = z := by
      have := hz.1
      rw [this] at hx
      exact mem_singleton_iff.mp hx
    have hyz : y = z := by
      have := hz.1
      rw [this] at hy
      exact mem_singleton_iff.mp hy
    exact hxy (hxz.trans hyz.symm)
  | inr hhomeo =>
    exact hnotHomeo hhomeo

/-- Erdős's first conjecture is false under CH -/
theorem erdos_first_conjecture_false
    (hCH : Cardinal.continuum = aleph 1) :
    ¬erdosFirstConjecture := by
  intro hconj
  obtain ⟨S, hRudin, _, _⟩ := rudin_theorem_ch hCH
  exact rudin_set_no_diverse_subset S hRudin (hconj S hRudin.1)

/-- Erdős's second conjecture is false under CH -/
theorem erdos_second_conjecture_false
    (hCH : Cardinal.continuum = aleph 1) :
    ¬erdosSecondConjecture := by
  intro hconj
  obtain ⟨S, hRudin, hcard, _⟩ := rudin_theorem_ch hCH
  have h := hconj S hRudin.1
  rw [hcard] at h
  exact lt_irrefl _ h

-- ## Summary

/-- The combined result: Under CH, both of Erdős's conjectures about
    connected subsets of Euclidean space are false.

    PROBLEM: Do connected sets in ℝⁿ always have diverse connected subsets?
             Do they always have more than continuum-many connected subsets?

    ANSWER: NO to both (under CH), via Rudin's 1958 construction. -/
theorem erdos_910_both_false
    (hCH : Cardinal.continuum = aleph 1) :
    ¬erdosFirstConjecture ∧ ¬erdosSecondConjecture :=
  ⟨erdos_first_conjecture_false hCH, erdos_second_conjecture_false hCH⟩

end Erdos910
