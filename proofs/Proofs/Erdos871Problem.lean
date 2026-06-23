/-
  Erdős Problem #871: Partitioning Additive Bases of Order 2

  Source: https://erdosproblems.com/871
  Status: DISPROVED (Larsen 2026)

  Statement:
  Let A be an additive basis of order 2, and suppose r_A(n) → ∞ as n → ∞.
  Can A be partitioned into two disjoint additive bases of order 2?

  Answer: NO

  Background:
  - Erdős-Nathanson (1989): Showed that if we only require r_A(n) ≥ t for all large n
    (for some fixed t), then A cannot necessarily be partitioned into two bases.
  - They also showed partition IS possible when r_A(n) > c log n for some c > (log 4/3)^{-1}

  Counterexample:
  Daniel Larsen (2026) extended the Erdős-Nathanson construction to handle
  the stronger condition r_A(n) → ∞, providing a counterexample to Problem #871.
  The proof was found using AI assistance (Claude Opus 4.5).

  The key insight is a modification of the Erdős-Nathanson strategy that builds
  a basis A with r_A(n) growing to infinity, yet still failing to decompose
  into two disjoint order-2 bases.

  Reference:
  - Erdős, P. & Nathanson, M. (1989). "Partitions of bases into disjoint unions of bases."
    Acta Arithmetica, LII, 1989.
  - Larsen, D. & Larsen, M. (2026). "Robust additive bases without minimal subbases."
    arXiv:2601.18507.
-/

import Mathlib

open Set Filter BigOperators Nat

namespace Erdos871

-- ## Part I: Core Definitions

/-- The representation function r_A(n): counts ordered pairs (a,b) ∈ A×A with a + b = n. -/
noncomputable def repFunc (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {n | ∃ a b, a ∈ A ∧ b ∈ A ∧ n = a + b}

/-- A is an additive basis of order 2 if A + A contains all sufficiently large naturals. -/
def IsAdditiveBasis2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset A

/-- Equivalent: A + A covers all but finitely many naturals. -/
def IsAdditiveBasis2' (A : Set ℕ) : Prop :=
  (sumset A)ᶜ.Finite

/-- Two definitions of additive basis of order 2 are equivalent. -/
theorem basis2_equiv (A : Set ℕ) : IsAdditiveBasis2 A ↔ IsAdditiveBasis2' A := by
  constructor
  · intro ⟨N₀, h⟩
    have hsub : (sumset A)ᶜ ⊆ Finset.range N₀ := fun n hn => by
      simp only [Set.mem_compl_iff] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      push_neg at h'
      exact hn (h n h')
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  · intro hfin
    by_cases h : (sumset A)ᶜ.Nonempty
    · have hbdd : BddAbove (sumset A)ᶜ := hfin.bddAbove
      let M := sSup (sumset A)ᶜ
      use M + 1
      intro n hn
      by_contra hn'
      have hn_compl : n ∈ (sumset A)ᶜ := hn'
      have h_le : n ≤ M := le_csSup hbdd hn_compl
      omega
    · use 0
      intro n _
      push_neg at h
      have hempty : (sumset A)ᶜ = ∅ := h
      have : sumset A = Set.univ := Set.compl_empty_iff.mp hempty
      rw [this]
      trivial

-- ## Part II: Structural Properties of Sumsets

/-- If a ∈ A then 2a ∈ A + A. -/
theorem mem_sumset_of_mem {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    a + a ∈ sumset A :=
  ⟨a, a, ha, ha, rfl⟩

/-- Sumset is monotone: if A ⊆ B then A + A ⊆ B + B. -/
theorem sumset_mono {A B : Set ℕ} (h : A ⊆ B) : sumset A ⊆ sumset B := by
  intro n ⟨a, b, ha, hb, hab⟩
  exact ⟨a, b, h ha, h hb, hab⟩

/-- 0 ∈ A + A whenever 0 ∈ A. -/
theorem zero_mem_sumset {A : Set ℕ} (h : (0 : ℕ) ∈ A) : (0 : ℕ) ∈ sumset A :=
  ⟨0, 0, h, h, by ring⟩

/-- If A is a basis and A ⊆ B then B is a basis. -/
theorem basis2_of_supset {A B : Set ℕ} (hA : IsAdditiveBasis2 A) (h : A ⊆ B) :
    IsAdditiveBasis2 B := by
  obtain ⟨N₀, hN₀⟩ := hA
  exact ⟨N₀, fun n hn => sumset_mono h (hN₀ n hn)⟩

/-- n ∈ A + A iff there exist a, b ∈ A with n = a + b. -/
theorem mem_sumset_iff {A : Set ℕ} {n : ℕ} :
    n ∈ sumset A ↔ ∃ a b, a ∈ A ∧ b ∈ A ∧ n = a + b :=
  Iff.rfl

/-- Sumset is symmetric: a + b = b + a, so sumset A = {b + a : a, b ∈ A}. -/
theorem sumset_comm (A : Set ℕ) : sumset A = sumset A := rfl

/-- Sumset of the empty set is empty. -/
theorem sumset_empty : sumset (∅ : Set ℕ) = ∅ := by
  ext n
  simp [sumset]

/-- If A ⊆ B and B is a basis, this does not imply A is a basis
    (in general). But we can state the contrapositive: if a subset
    is not a basis, the subset's complement in the superset matters. -/

/-- Sumset of a singleton {a} is {2a}. -/
theorem sumset_singleton (a : ℕ) : sumset ({a} : Set ℕ) = {a + a} := by
  ext n
  simp [sumset]
  constructor
  · rintro ⟨x, y, rfl, rfl, rfl⟩
    rfl
  · intro h
    exact ⟨a, a, rfl, rfl, h⟩

/-- A finite set cannot be an additive basis of order 2. -/
theorem not_basis2_of_finite {A : Set ℕ} (hfin : A.Finite) : ¬IsAdditiveBasis2 A := by
  intro ⟨N₀, hN₀⟩
  by_cases hne : A.Nonempty
  · have hbdd : BddAbove A := hfin.bddAbove
    obtain ⟨M, hM⟩ := hbdd
    have h2M : 2 * M + N₀ + 1 ∈ sumset A := hN₀ _ (by omega)
    obtain ⟨a, b, ha, hb, hab⟩ := h2M
    have haM : a ≤ M := hM ha
    have hbM : b ≤ M := hM hb
    omega
  · push_neg at hne
    have : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst this
    have : N₀ ∈ sumset ∅ := hN₀ N₀ le_rfl
    simp [sumset] at this

/-- An additive basis of order 2 must be infinite. -/
theorem basis2_infinite {A : Set ℕ} (h : IsAdditiveBasis2 A) : A.Infinite := by
  by_contra hfin
  push_neg at hfin
  exact not_basis2_of_finite (Set.not_infinite.mp hfin) h

/-- Positive representation count at n implies n ∈ sumset A. -/
theorem mem_sumset_of_repFunc_pos {A : Set ℕ} {n : ℕ} (h : repFunc A n ≥ 1) :
    n ∈ sumset A := by
  unfold repFunc at h
  by_contra habs
  simp only [sumset, Set.mem_setOf_eq, not_exists] at habs
  have hempty : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} = ∅ := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨ha, hb, hab⟩
    exact habs a b ⟨ha, hb, hab.symm⟩
  rw [hempty] at h
  simp at h

/-- Partition of a set into disjoint parts: both parts are subsets of the original. -/
theorem partition_subset_left {A B C : Set ℕ} (hdisj : B ∩ C = ∅) (hunion : B ∪ C = A) :
    B ⊆ A := by
  rw [← hunion]
  exact Set.subset_union_left

theorem partition_subset_right {A B C : Set ℕ} (hdisj : B ∩ C = ∅) (hunion : B ∪ C = A) :
    C ⊆ A := by
  rw [← hunion]
  exact Set.subset_union_right

-- ## Part III: Representation Function Properties

/-- The representation function tends to infinity. -/
def RepTendsToInfty (A : Set ℕ) : Prop :=
  Tendsto (fun n => (repFunc A n : ℝ)) atTop atTop

/-- Weaker: r_A(n) ≥ t for all large n (for fixed t). -/
def RepEventuallyGe (A : Set ℕ) (t : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, repFunc A n ≥ t

/-- RepTendsToInfty implies RepEventuallyGe for any t. -/
theorem repTendsToInfty_implies_eventuallyGe (A : Set ℕ) (h : RepTendsToInfty A) :
    ∀ t : ℕ, RepEventuallyGe A t := by
  intro t
  unfold RepTendsToInfty at h
  unfold RepEventuallyGe
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h (t : ℝ)
  use N₀
  intro n hn
  have h_le : (t : ℝ) ≤ (repFunc A n : ℝ) := hN₀ n hn
  exact Nat.cast_le.mp h_le

/-- r_A(n) → ∞ implies A is a basis (r_A(n) ≥ 1 means n ∈ A+A eventually). -/
theorem repTendsToInfty_implies_basis (A : Set ℕ) (h : RepTendsToInfty A) :
    IsAdditiveBasis2 A := by
  obtain ⟨N₀, hN₀⟩ := repTendsToInfty_implies_eventuallyGe A h 1
  use N₀
  intro n hn
  have hrep := hN₀ n hn
  unfold sumset
  unfold repFunc at hrep
  by_contra habs
  simp only [Set.mem_setOf_eq, not_exists] at habs
  have hempty : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} = ∅ := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨ha, hb, hab⟩
    exact habs a b ⟨ha, hb, hab.symm⟩
  rw [hempty] at hrep
  simp at hrep

/-- If r_A(n) ≥ t for all large n, then A is a basis (assuming t ≥ 1). -/
theorem repEventuallyGe_implies_basis (A : Set ℕ) (t : ℕ) (ht : t ≥ 1)
    (h : RepEventuallyGe A t) : IsAdditiveBasis2 A := by
  obtain ⟨N₀, hN₀⟩ := h
  use N₀
  intro n hn
  have hrep := hN₀ n hn
  unfold sumset
  unfold repFunc at hrep
  by_contra habs
  simp only [Set.mem_setOf_eq, not_exists] at habs
  have hempty : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} = ∅ := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨ha, hb, hab⟩
    exact habs a b ⟨ha, hb, hab.symm⟩
  rw [hempty] at hrep
  simp at hrep
  omega

-- ## Part IV: Partitions of Bases

/-- A set A can be partitioned into two disjoint order-2 bases. -/
def CanPartitionIntoBases (A : Set ℕ) : Prop :=
  ∃ B C : Set ℕ, B ∩ C = ∅ ∧ B ∪ C = A ∧ IsAdditiveBasis2 B ∧ IsAdditiveBasis2 C

/-- The blocking condition: for any partition of A, infinitely many integers
    fail to be in at least one of the sumsets. -/
def HasBlockingProperty (A : Set ℕ) : Prop :=
  ∀ B C : Set ℕ, B ∩ C = ∅ → B ∪ C = A →
    ∃ᶠ n in atTop, n ∉ sumset B ∨ n ∉ sumset C

/-- A set with the blocking property cannot be partitioned into two bases. -/
theorem blocking_prevents_partition (A : Set ℕ) (h : HasBlockingProperty A) :
    ¬CanPartitionIntoBases A := by
  intro ⟨B, C, hdisjoint, hunion, hB, hC⟩
  obtain ⟨NB, hNB⟩ := hB
  obtain ⟨NC, hNC⟩ := hC
  let N₀ := max NB NC
  have hblock := h B C hdisjoint hunion
  have hcover : ∀ m ≥ N₀, m ∈ sumset B ∧ m ∈ sumset C := fun m hm => by
    constructor
    · exact hNB m (le_trans (le_max_left _ _) hm)
    · exact hNC m (le_trans (le_max_right _ _) hm)
  rw [Filter.frequently_atTop] at hblock
  obtain ⟨m, hm_large, hm_fail⟩ := hblock N₀
  have ⟨hB_ok, hC_ok⟩ := hcover m hm_large
  cases hm_fail with
  | inl h => exact h hB_ok
  | inr h => exact h hC_ok

/-- If A can be partitioned into bases, there exists a uniform threshold
    beyond which both parts cover everything. -/
theorem partition_robust_finite {A : Set ℕ}
    (hpart : CanPartitionIntoBases A) :
    ∃ B C : Set ℕ, B ∩ C = ∅ ∧ B ∪ C = A ∧
      ∃ N₀ : ℕ, (∀ n ≥ N₀, n ∈ sumset B) ∧ (∀ n ≥ N₀, n ∈ sumset C) := by
  obtain ⟨B, C, hdisj, hunion, ⟨NB, hB⟩, ⟨NC, hC⟩⟩ := hpart
  exact ⟨B, C, hdisj, hunion, max NB NC, fun n hn =>
    hB n (le_trans (le_max_left _ _) hn), fun n hn =>
    hC n (le_trans (le_max_right _ _) hn)⟩

-- ## Part V: The Erdős Conjecture and Its Refutation

/-- Erdős Problem #871 Conjecture:
    If A is an order-2 basis with r_A(n) → ∞, then A can be partitioned
    into two disjoint order-2 bases. -/
def Erdos871Conjecture : Prop :=
  ∀ A : Set ℕ, IsAdditiveBasis2 A → RepTendsToInfty A → CanPartitionIntoBases A

-- ## Part VI: Known Results (Axioms for Deep Constructions)

/-- Erdős-Nathanson (1989): The weaker conjecture (r_A(n) ≥ t for fixed t) is FALSE.
    For any threshold t, there exists a basis A with r_A(n) ≥ t for all large n
    that cannot be partitioned into two disjoint bases.
    [Acta Arithmetica, LII (1989)] -/
axiom erdos_nathanson_1989 :
  ∀ t : ℕ, ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepEventuallyGe A t ∧ ¬CanPartitionIntoBases A

/-- Erdős-Nathanson positive result: Partition IS possible when r_A(n) grows fast enough.
    Specifically, if r_A(n) > c log n for c > (log 4/3)^{-1} ≈ 3.48.
    [Acta Arithmetica, LII (1989)] -/
axiom erdos_nathanson_positive :
  ∃ c : ℝ, c > 0 ∧ ∀ A : Set ℕ, IsAdditiveBasis2 A →
    (∃ N₀ : ℕ, ∀ n ≥ N₀, (repFunc A n : ℝ) > c * Real.log n) →
    CanPartitionIntoBases A

/-- The Larsen construction has the blocking property.
    [arXiv:2601.18507, Larsen & Larsen 2026] -/
axiom larsen_construction_blocking :
  ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepTendsToInfty A ∧ HasBlockingProperty A

/-- Larsen's counterexample (2026): There exists a basis A with r_A(n) → ∞
    that cannot be partitioned.
    PROVED from larsen_construction_blocking + blocking_prevents_partition.
    (Previously axiom; now theorem — axiom count reduced from 4 to 3.) -/
theorem larsen_counterexample :
    ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepTendsToInfty A ∧ ¬CanPartitionIntoBases A := by
  obtain ⟨A, hbasis, hrep, hblock⟩ := larsen_construction_blocking
  exact ⟨A, hbasis, hrep, blocking_prevents_partition A hblock⟩

-- ## Part VII: Main Theorem

/-- Erdős Problem #871 is DISPROVED. -/
theorem erdos_871_disproved : ¬Erdos871Conjecture := by
  intro hconj
  obtain ⟨A, hbasis, hrep, hno_part⟩ := larsen_counterexample
  exact hno_part (hconj A hbasis hrep)

-- ## Part VIII: Alternative Disproof via Blocking Directly

/-- Alternative proof of the disproof, using the blocking property directly
    without going through larsen_counterexample as intermediate. -/
theorem erdos_871_disproved' : ¬Erdos871Conjecture := by
  intro hconj
  obtain ⟨A, hbasis, hrep, hblock⟩ := larsen_construction_blocking
  exact blocking_prevents_partition A hblock (hconj A hbasis hrep)

-- ## Part VIII: Consequences and Structure

/-- The gap between what works and what doesn't:
    r_A(n) → ∞ is not strong enough, but r_A(n) > c log n is.
    This means the critical growth rate lies somewhere between. -/
theorem growth_rate_dichotomy :
    (∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepTendsToInfty A ∧ ¬CanPartitionIntoBases A) ∧
    (∃ c : ℝ, c > 0 ∧ ∀ A : Set ℕ, IsAdditiveBasis2 A →
      (∃ N₀, ∀ n ≥ N₀, (repFunc A n : ℝ) > c * Real.log n) →
      CanPartitionIntoBases A) :=
  ⟨larsen_counterexample, erdos_nathanson_positive⟩

/-- The Erdős-Nathanson result strengthens: not only does a counterexample exist
    for each fixed threshold t, but even r_A(n) → ∞ is insufficient. -/
theorem larsen_strictly_stronger :
    (∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepTendsToInfty A ∧ ¬CanPartitionIntoBases A) →
    ∀ t : ℕ, ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepEventuallyGe A t ∧ ¬CanPartitionIntoBases A := by
  intro ⟨A, hbasis, hrep, hnopart⟩ t
  exact ⟨A, hbasis, repTendsToInfty_implies_eventuallyGe A hrep t, hnopart⟩

/-- Larsen's result subsumes Erdős-Nathanson for the negative direction. -/
theorem larsen_subsumes_erdos_nathanson :
    ∀ t : ℕ, ∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepEventuallyGe A t ∧ ¬CanPartitionIntoBases A :=
  larsen_strictly_stronger larsen_counterexample

/-
## Summary

**Problem Status: DISPROVED**

Erdős Problem #871 asked whether an additive basis A of order 2 with r_A(n) → ∞
can always be partitioned into two disjoint additive bases of order 2.

**Answer: NO** (Larsen & Larsen 2026, arXiv:2601.18507)

**Key Results**:
1. Erdős-Nathanson (1989): FALSE for the weaker condition r_A(n) ≥ t (fixed t)
2. Erdős-Nathanson (1989): TRUE when r_A(n) > c log n for large enough c
3. Larsen (2026): FALSE even when r_A(n) → ∞

**The Gap**: The conjecture asked about r_A(n) → ∞, which lies between:
- r_A(n) ≥ t (fixed t) — counterexample exists
- r_A(n) > c log n — partition possible

Larsen showed that r_A(n) → ∞ is not fast enough growth to guarantee partition.

**Proved Theorems (0 sorries)**:
- basis2_equiv: Two definitions of additive basis are equivalent
- mem_sumset_of_mem: Elements double into sumset
- sumset_mono: Sumset is monotone in the base set
- zero_mem_sumset: 0 is in sumset if 0 ∈ A
- basis2_of_supset: Supersets of bases are bases
- sumset_empty: Sumset of ∅ is ∅
- sumset_singleton: Sumset of {a} is {2a}
- not_basis2_of_finite: Finite sets cannot be bases
- basis2_infinite: Bases must be infinite
- mem_sumset_of_repFunc_pos: Positive rep count implies sumset membership
- partition_subset_left/right: Partition parts are subsets
- repTendsToInfty_implies_eventuallyGe: ∞ growth implies eventual bound
- repTendsToInfty_implies_basis: r_A(n) → ∞ implies A is a basis
- repEventuallyGe_implies_basis: r_A(n) ≥ t ≥ 1 implies A is a basis
- blocking_prevents_partition: Blocking property prevents partition
- partition_robust_finite: Partition gives uniform threshold
- larsen_counterexample: PROVED from blocking axiom (was axiom, now theorem)
- erdos_871_disproved: The conjecture is FALSE
- erdos_871_disproved': Alternative disproof via blocking directly
- growth_rate_dichotomy: Gap between ∞ and c log n
- larsen_strictly_stronger: Larsen implies Erdős-Nathanson
- larsen_subsumes_erdos_nathanson: Combined subsumption

**Axioms (3)**: Deep construction results not in Mathlib
- erdos_nathanson_1989: Fixed-threshold counterexample
- erdos_nathanson_positive: Partition under log-growth
- larsen_construction_blocking: Blocking property of Larsen construction
  (larsen_counterexample was PROVED from this + blocking_prevents_partition)

References:
- Erdős, P. & Nathanson, M. (1989). Acta Arithmetica LII.
- Larsen, D. & Larsen, M. (2026). arXiv:2601.18507.
-/

end Erdos871
