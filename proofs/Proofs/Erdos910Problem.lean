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
    that is a Rudin set with exactly 2^ℵ₀ connected subsets.

    The nontriviality condition is immediate from the construction:
    Rudin's set has continuum-many points (it's a nontrivial connected
    subset of the plane). -/
axiom rudin_theorem :
  ContinuumHypothesis →
  ∃ (S : Set (ℝ × ℝ)),
    IsRudinSet S ∧ HasExactlyContinuumConnectedSubsets S ∧ S.Nontrivial

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
  obtain ⟨S, hRudin, _, hnontriv⟩ := rudin_theorem hCH
  -- Apply the conjecture to get a diverse subset
  have hdiv := hconj (ℝ × ℝ) S hRudin.1
  -- But Rudin sets have no diverse subsets
  exact rudin_set_no_diverse_subset S hRudin hnontriv hdiv

/-- Homeomorphisms preserve connected subset cardinality. -/
private theorem connectedSubsetCardinality_image_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (S : Set X) :
    connectedSubsetCardinality (e '' S) = connectedSubsetCardinality S := by
  unfold connectedSubsetCardinality
  apply Cardinal.mk_congr
  exact {
    toFun := fun ⟨T', hT'⟩ => ⟨e.symm '' T', by
      refine ⟨?_, hT'.2.image _ e.symm.continuous.continuousOn⟩
      calc ⇑e.symm '' T'
          ⊆ ⇑e.symm '' (⇑e '' S) := Set.image_subset _ hT'.1
        _ = (⇑e.symm ∘ ⇑e) '' S := (Set.image_image _ _ _).symm
        _ = id '' S := by rw [show ⇑e.symm ∘ ⇑e = id from funext e.symm_apply_apply]
        _ = S := Set.image_id _⟩
    invFun := fun ⟨T, hT⟩ =>
      ⟨e '' T, Set.image_subset _ hT.1, hT.2.image _ e.continuous.continuousOn⟩
    left_inv := fun ⟨T', _⟩ => Subtype.ext <| by
      rw [Set.image_image, show ⇑e ∘ ⇑e.symm = id from funext e.apply_symm_apply, Set.image_id]
    right_inv := fun ⟨T, _⟩ => Subtype.ext <| by
      rw [Set.image_image, show ⇑e.symm ∘ ⇑e = id from funext e.symm_apply_apply, Set.image_id]
  }

/-- Corollary: Erdős's second conjecture is false (under CH) -/
theorem erdos_second_conjecture_false :
    ContinuumHypothesis → ¬erdosSecondConjecture := by
  intro hCH hconj
  obtain ⟨S, hRudin, hcard, _⟩ := rudin_theorem hCH
  -- Build homeomorphism ℝ × ℝ ≃ₜ (Fin 2 → ℝ)
  let e : (ℝ × ℝ) ≃ₜ (Fin 2 → ℝ) :=
    { toEquiv := (piFinTwoEquiv (fun _ => ℝ)).symm
      continuous_toFun :=
        continuous_pi (fun i => Fin.cases continuous_fst (fun _ => continuous_snd) i)
      continuous_invFun := (continuous_apply 0).prod_mk (continuous_apply 1) }
  -- Transfer the Rudin set to Fin 2 → ℝ
  have hconn : IsConnected (e '' S) := hRudin.1.image _ e.continuous.continuousOn
  -- The conjecture claims > continuum connected subsets
  have hgt := hconj 2 (by omega) (e '' S) hconn
  -- But the homeomorphism preserves connected subset cardinality
  have hcard' : connectedSubsetCardinality S = continuum := hcard
  rw [connectedSubsetCardinality_image_homeomorph e S, hcard'] at hgt
  exact lt_irrefl _ hgt

#check rudin_theorem
#check erdos_first_conjecture_false
#check @IsRudinSet
