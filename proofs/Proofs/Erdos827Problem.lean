/-
# Erdős Problem #827: Distinct Circumradii in General Position

Let n_k be the minimal number such that any n_k points in general position
in ℝ² must contain a subset of k points where all C(k,3) triples determine
circles of distinct radii.

Erdős (1975) asked whether n_k exists. He claimed n_k ≤ k + 2·C(k-1,2)·C(k-1,3)
in 1978, but the proof contained errors. Martinez and Roldán-Pensado corrected
the argument and showed n_k ≪ k⁹.

The problem asks to determine n_k more precisely.

Reference: https://erdosproblems.com/827

Axioms: 4 (nk_exists, martinez_roldan_pensado, nk_three, nk_ge_k)
Proved: minimalNk_valid, minimalNk_sharp, nk_monotone, GeneralPosition_subset
Sorries: 0
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/- ## Points in General Position -/

/-- A point in the plane. -/
abbrev Point := ℝ × ℝ

/-- The squared distance between two points. -/
noncomputable def distSq (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Points are in general position: no three are collinear. -/
def GeneralPosition (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    p ≠ q → q ≠ r → p ≠ r →
    (p.1 - r.1) * (q.2 - r.2) ≠ (q.1 - r.1) * (p.2 - r.2)

/-- A subset of a general position set is in general position. -/
theorem GeneralPosition_subset {S T : Finset Point} (hTS : T ⊆ S)
    (hGP : GeneralPosition S) : GeneralPosition T :=
  fun p hp q hq r hr => hGP p (hTS hp) q (hTS hq) r (hTS hr)

/- ## Circumradius -/

/-- The squared circumradius of three non-collinear points.
    For the circumcircle of triangle pqr, R² = (|pq|²·|qr|²·|rp|²) / (16·Area²). -/
noncomputable def circumRadiusSq (p q r : Point) : ℝ :=
  let a2 := distSq p q
  let b2 := distSq q r
  let c2 := distSq r p
  let area2 := ((p.1 - r.1) * (q.2 - r.2) - (q.1 - r.1) * (p.2 - r.2)) ^ 2
  a2 * b2 * c2 / (4 * area2)

/-- A subset of k points has all distinct circumradii: every two triples
    determine circles of different radii. -/
def AllDistinctCircumradii (S : Finset Point) : Prop :=
  ∀ p₁ ∈ S, ∀ q₁ ∈ S, ∀ r₁ ∈ S,
  ∀ p₂ ∈ S, ∀ q₂ ∈ S, ∀ r₂ ∈ S,
    p₁ ≠ q₁ → q₁ ≠ r₁ → p₁ ≠ r₁ →
    p₂ ≠ q₂ → q₂ ≠ r₂ → p₂ ≠ r₂ →
    ({p₁, q₁, r₁} : Finset Point) ≠ {p₂, q₂, r₂} →
    circumRadiusSq p₁ q₁ r₁ ≠ circumRadiusSq p₂ q₂ r₂

/- ## The Minimal Number n_k -/

/-- n_k exists: for each k, there is a threshold such that any set of
    that many points in general position contains a k-subset with all
    distinct circumradii. -/
def NkExists (k : ℕ) : Prop :=
  ∃ n : ℕ, ∀ S : Finset Point, GeneralPosition S → n ≤ S.card →
    ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

/-- The set of valid thresholds: values of n for which any n points in
    general position contain a k-subset with all distinct circumradii. -/
def ThresholdSet (k : ℕ) : Set ℕ :=
  {n : ℕ | ∀ S : Finset Point, GeneralPosition S → n ≤ S.card →
    ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T}

/-- n_k exists for k ≥ 3: the threshold set is nonempty.
    Established by Martinez and Roldán-Pensado (2015), correcting Erdős (1978). -/
axiom nk_exists (k : ℕ) (hk : 3 ≤ k) : (ThresholdSet k).Nonempty

/-- n_k is the minimal valid threshold, defined as sInf of the threshold set. -/
noncomputable def minimalNk (k : ℕ) : ℕ := sInf (ThresholdSet k)

/-- minimalNk k is a valid threshold: any GP set of size ≥ minimalNk k
    contains a k-subset with all distinct circumradii.
    Proved from sInf membership in nonempty set (well-ordering of ℕ). -/
theorem minimalNk_valid (k : ℕ) (hk : 3 ≤ k) :
    ∀ S : Finset Point, GeneralPosition S → minimalNk k ≤ S.card →
      ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T :=
  Nat.sInf_mem (nk_exists k hk)

/-- minimalNk k is minimal: there exist configurations with minimalNk k - 1
    points that avoid k-subsets with all distinct circumradii.
    Proved from minimality of sInf and classical extraction of witnesses. -/
theorem minimalNk_sharp (k : ℕ) (hk : 3 ≤ k) :
    ∃ S : Finset Point, GeneralPosition S ∧ S.card = minimalNk k - 1 ∧
      ¬∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T := by
  -- Step 1: minimalNk k > 0 (the empty set witnesses that 0 is not a threshold)
  have h_pos : 0 < minimalNk k := by
    by_contra h_not_pos
    push_neg at h_not_pos
    have h0 : minimalNk k = 0 := by omega
    have hmem := Nat.sInf_mem (nk_exists k hk)
    rw [show minimalNk k = sInf (ThresholdSet k) from rfl, h0] at hmem
    obtain ⟨T, hT_sub, hT_card, _⟩ :=
      hmem ∅ (fun p hp => absurd hp (Finset.not_mem_empty p)) (Nat.zero_le _)
    have : T = ∅ := Finset.subset_empty.mp hT_sub
    rw [this, Finset.card_empty] at hT_card; omega
  -- Step 2: minimalNk k - 1 is not a valid threshold (below the minimum)
  have h_not_thresh : ¬∀ S : Finset Point, GeneralPosition S →
      minimalNk k - 1 ≤ S.card →
      ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T := by
    intro hmem
    have h_le := Nat.sInf_le (show minimalNk k - 1 ∈ ThresholdSet k from hmem)
    omega
  -- Step 3: Extract witness with |S| ≥ m-1 and no good k-subset
  have h_fail : ∃ S : Finset Point, GeneralPosition S ∧ minimalNk k - 1 ≤ S.card ∧
      ¬∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T := by
    by_contra h_all_good
    push_neg at h_all_good
    exact h_not_thresh h_all_good
  -- Step 4: Trim to exact cardinality
  obtain ⟨S, hGP, hCard, hBad⟩ := h_fail
  obtain ⟨S', hS'_sub, hS'_card⟩ := Finset.exists_smaller_set S (minimalNk k - 1) hCard
  exact ⟨S', GeneralPosition_subset hS'_sub hGP, hS'_card,
    fun ⟨T, hT_sub, hT_card, hT_good⟩ =>
      hBad ⟨T, Finset.Subset.trans hT_sub hS'_sub, hT_card, hT_good⟩⟩

/- ## Main Problem -/

/-- Erdős Problem 827: Determine n_k. In particular, find the growth rate. -/
def ErdosProblem827 : Prop :=
  ∀ k : ℕ, 3 ≤ k → NkExists k

/- ## Known Bounds -/

/-- Martinez-Roldán-Pensado: n_k ≪ k⁹. -/
def MartinezBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
    (minimalNk k : ℝ) ≤ C * k ^ 9

/-- Erdős's original (incorrect) claimed bound: n_k ≤ k + 2·C(k-1,2)·C(k-1,3). -/
noncomputable def erdosClaimedBound (k : ℕ) : ℕ :=
  k + 2 * (k - 1).choose 2 * (k - 1).choose 3

/-- Martinez and Roldán-Pensado proved the corrected polynomial bound. -/
axiom martinez_roldan_pensado : MartinezBound

/- ## Trivial Cases -/

/-- For k = 3, any 3 points in general position form a triangle with
    exactly one circumradius, so n_3 = 3. -/
axiom nk_three : minimalNk 3 = 3

/-- n_k is monotone non-decreasing.

    Proof: Assume for contradiction that n_{k₂} < n_{k₁}. By minimalNk_sharp,
    there exists a GP set S of size n_{k₁} - 1 with no good k₁-subset.
    Since |S| ≥ n_{k₂}, by minimalNk_valid there is a good k₂-subset T ⊆ S.
    Since k₁ ≤ k₂ = |T|, we can take T' ⊆ T of size k₁. AllDistinctCircumradii
    is inherited by subsets (fewer triples, same radii). So T' is a good k₁-subset
    of S, contradicting the sharpness of S. -/
theorem nk_monotone (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) (hk : 3 ≤ k₁) :
    minimalNk k₁ ≤ minimalNk k₂ := by
  by_contra hlt
  push_neg at hlt
  have hk2 : 3 ≤ k₂ := le_trans hk h
  obtain ⟨S, hGP, hCard, hBad⟩ := minimalNk_sharp k₁ hk
  have hBig : minimalNk k₂ ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard, hTgood⟩ := minimalNk_valid k₂ hk2 S hGP hBig
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_smaller_set T k₁ (by omega)
  have hT'good : AllDistinctCircumradii T' := by
    intro p₁ hp₁ q₁ hq₁ r₁ hr₁ p₂ hp₂ q₂ hq₂ r₂ hr₂
    exact hTgood p₁ (hT'T hp₁) q₁ (hT'T hq₁) r₁ (hT'T hr₁)
      p₂ (hT'T hp₂) q₂ (hT'T hq₂) r₂ (hT'T hr₂)
  exact hBad ⟨T', Finset.Subset.trans hT'T hTS, hT'card, hT'good⟩

/-- n_k ≥ k trivially. -/
axiom nk_ge_k (k : ℕ) (hk : 3 ≤ k) : k ≤ minimalNk k
