/-
  Erdős Problem #910: Connected Subsets of Euclidean Space

  Source: https://erdosproblems.com/910
  Status: DISPROVED (Rudin 1958, under CH)

  Statement:
  Two questions about connected sets in ℝⁿ:

  (1) Does every connected set in ℝⁿ contain a connected subset which is
      not a point and not homeomorphic to the original set?

  (2) If n ≥ 2, does every connected set in ℝⁿ contain more than 2^ℵ₀
      many connected subsets?

  Background:
  Erdős asked these questions in the 1940s, expecting affirmative answers.
  The intuition was that connected sets should have rich internal structure,
  with many "genuinely different" connected subsets.

  For a typical connected set X ⊆ ℝⁿ (like an interval or a disk), there are
  continuum-many connected subsets, and most proper subsets are not
  homeomorphic to X itself.

  Resolution:
  Both questions are answered NO by Mary Ellen Rudin (1958).

  Under the Continuum Hypothesis (CH), Rudin constructed a connected subset
  X ⊆ ℝ² such that:
  • X has exactly 2^ℵ₀ connected subsets (not more)
  • Every proper connected subset of X is either a single point or
    homeomorphic to X itself

  This "Rudin set" is a pathological example showing that connected sets
  can have surprisingly rigid structure.

  References:
  [Er82e] Erdős, P. "Personal reminiscences and remarks" (1982)
  [Ru58] Rudin, M.E. "A connected subset of the plane"
         Fundamenta Mathematicae 46 (1958), 15-24

  Tags: topology, connected-sets, homeomorphism, continuum-hypothesis
-/

import Mathlib

open Set Topology Cardinal

/-
## Connected Sets and Subsets

Basic definitions for connected subspaces.
-/

variable {X : Type*} [TopologicalSpace X]

/-- The set of all connected subsets of a topological space -/
def connectedSubsets (X : Type*) [TopologicalSpace X] : Set (Set X) :=
  { S | IsConnected S }

/-- The set of all connected subsets of a given set S -/
def connectedSubsetsOf (S : Set X) : Set (Set X) :=
  { T | T ⊆ S ∧ IsConnected T }

/-
## Homeomorphism Between Subsets

Two subsets are homeomorphic if there's a homeomorphism between them
(with the subspace topology).
-/

/-- Two sets are homeomorphic as subspaces -/
def AreHomeomorphic (S T : Set X) : Prop :=
  Nonempty (S ≃ₜ T)

/-- Homeomorphism is reflexive -/
theorem areHomeomorphic_refl (S : Set X) : AreHomeomorphic S S :=
  ⟨Homeomorph.refl S⟩

/-- Homeomorphism is symmetric -/
theorem areHomeomorphic_symm {S T : Set X} (h : AreHomeomorphic S T) :
    AreHomeomorphic T S :=
  h.map Homeomorph.symm

/-
## Erdős's First Question

Does every connected set have a proper connected subset that is
neither a point nor homeomorphic to the whole?
-/

/-- A set has the "diverse subsets" property if it has a proper connected
    subset that is neither a singleton nor homeomorphic to the whole -/
def HasDiverseConnectedSubset (S : Set X) : Prop :=
  ∃ T : Set X, T ⊆ S ∧ T ≠ S ∧ IsConnected T ∧
    (∃ x y : X, x ∈ T ∧ y ∈ T ∧ x ≠ y) ∧  -- not a singleton
    ¬AreHomeomorphic T S

/-- Erdős's first conjecture: every connected set has diverse subsets -/
def erdosFirstConjecture : Prop :=
  ∀ (X : Type*) [TopologicalSpace X] (S : Set X),
    IsConnected S → HasDiverseConnectedSubset S

/-
## Erdős's Second Question

Does every connected set in ℝⁿ (n ≥ 2) have more than continuum-many
connected subsets?
-/

/-- The cardinality of connected subsets of S -/
noncomputable def connectedSubsetCardinality (S : Set X) : Cardinal :=
  #(connectedSubsetsOf S)

/-- The continuum: cardinality of ℝ -/
noncomputable def continuum : Cardinal := #ℝ

/-- Erdős's second conjecture: connected sets in ℝⁿ have > 2^ℵ₀ connected subsets -/
def erdosSecondConjecture : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2) (S : Set (Fin n → ℝ)),
    IsConnected S → connectedSubsetCardinality S > continuum

/-
## The Rudin Set (Counterexample)

Under CH, Rudin constructed a connected planar set with special properties.
-/

/-- The Continuum Hypothesis: ℵ₁ = 2^ℵ₀ -/
def ContinuumHypothesis : Prop := aleph 1 = 2 ^ aleph 0

/-- A "Rudin set" is a connected set where every proper connected subset
    is either a point or homeomorphic to the whole -/
def IsRudinSet (S : Set X) : Prop :=
  IsConnected S ∧
  (∀ T : Set X, T ⊆ S → T ≠ S → IsConnected T →
    (∃! x, T = {x}) ∨ AreHomeomorphic T S)

/-- A Rudin set has exactly continuum-many connected subsets -/
def HasExactlyContinuumConnectedSubsets (S : Set X) : Prop :=
  connectedSubsetCardinality S = continuum

/-
## Rudin's Theorem (Main Result)

Under CH, there exists a Rudin set in ℝ².
-/

/-- Rudin's theorem: Under CH, there exists a connected planar set
    that is a Rudin set with exactly 2^ℵ₀ connected subsets -/
axiom rudin_theorem :
  ContinuumHypothesis →
  ∃ (S : Set (ℝ × ℝ)),
    IsRudinSet S ∧ HasExactlyContinuumConnectedSubsets S

/-
## Disproving Erdős's Conjectures
-/

/-- Rudin sets disprove Erdős's first conjecture -/
theorem rudin_set_no_diverse_subset (S : Set X) (hS : IsRudinSet S)
    (hcard : S.nontrivial) : ¬HasDiverseConnectedSubset S := by
  intro ⟨T, hTsub, hTne, hTconn, ⟨x, y, hx, hy, hxy⟩, hnotHomeo⟩
  -- T is a proper connected subset with more than one point
  have := hS.2 T hTsub hTne hTconn
  cases this with
  | inl hsing =>
    -- T is a singleton, contradicting x ≠ y both in T
    obtain ⟨z, hz⟩ := hsing
    have hxz : x = z := by simp [hz] at hx; exact hx
    have hyz : y = z := by simp [hz] at hy; exact hy
    exact hxy (hxz.trans hyz.symm)
  | inr hhomeo =>
    -- T is homeomorphic to S, contradicting hnotHomeo
    exact hnotHomeo hhomeo

/-- Corollary: Erdős's first conjecture is false (under CH) -/
theorem erdos_first_conjecture_false :
    ContinuumHypothesis → ¬erdosFirstConjecture := by
  intro hCH hconj
  obtain ⟨S, hRudin, _⟩ := rudin_theorem hCH
  -- The Rudin set is connected and nontrivial
  have hconn := hRudin.1
  -- Apply the conjecture to get a diverse subset
  have hdiv := hconj (ℝ × ℝ) S hconn
  -- But Rudin sets have no diverse subsets
  have hnontriv : S.nontrivial := by
    -- Rudin set is nontrivial (it's connected and has continuum-many subsets)
    sorry
  exact rudin_set_no_diverse_subset S hRudin hnontriv hdiv

/-- Corollary: Erdős's second conjecture is false (under CH) -/
theorem erdos_second_conjecture_false :
    ContinuumHypothesis → ¬erdosSecondConjecture := by
  intro hCH hconj
  obtain ⟨S, _, hcard⟩ := rudin_theorem hCH
  -- Embed ℝ² into ℝ² viewed as Fin 2 → ℝ
  -- The Rudin set has exactly continuum-many connected subsets
  -- But the conjecture says it should have MORE than continuum
  sorry

#check rudin_theorem
#check erdos_first_conjecture_false
#check @IsRudinSet
