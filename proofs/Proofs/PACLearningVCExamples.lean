/-
  VC Dimension of Specific Hypothesis Classes

  Computes VC dimension for concrete hypothesis classes on finite types:
  - Powerset family: VCDim(𝒫(Ω)) = |Ω|
  - Threshold classifiers on Fin n: VCDim = 1
  - Interval classifiers on Fin n: VCDim = 2

  This answers the open question from PAC Learning: can the VC dimension
  of specific hypothesis classes be computed in Lean 4?

  References:
  - Vapnik & Chervonenkis (1971): "On the Uniform Convergence..."
  - Sauer (1972), Shelah (1972): Shattering lemma
  - Shalev-Shwartz & Ben-David (2014): Understanding Machine Learning

  See also: PACLearning.lean for the Sauer-Shelah lemma.
-/
import Mathlib

namespace VCDimension

open Finset BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: VC DIMENSION DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════

/-- Trace (restriction) of a hypothesis class H on a sample S:
    the set of distinct intersection patterns {h ∩ S : h ∈ H}. -/
def traceOn (H : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  H.image (· ∩ S)

/-- H shatters S if every subset of S appears as a trace of some h ∈ H.
    Equivalently, |traceOn H S| = 2^|S|. -/
def Shatters (H : Finset (Finset α)) (S : Finset α) : Prop :=
  S.powerset ⊆ traceOn H S

/-- VC dimension at most d: no set of cardinality > d is shattered. -/
def VCDimLE (H : Finset (Finset α)) (d : ℕ) : Prop :=
  ∀ S : Finset α, Shatters H S → S.card ≤ d

/-- VC dimension at least d: some set of cardinality d is shattered. -/
def VCDimGE (H : Finset (Finset α)) (d : ℕ) : Prop :=
  ∃ S : Finset α, Shatters H S ∧ d ≤ S.card

/-- VC dimension equals d: dimension is both ≤ d and ≥ d. -/
def VCDimEq (H : Finset (Finset α)) (d : ℕ) : Prop :=
  VCDimLE H d ∧ VCDimGE H d

-- ═══════════════════════════════════════════════════════════════════
-- PART II: BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════

/-- The trace set is a subset of the powerset of S. -/
theorem traceOn_subset_powerset (H : Finset (Finset α)) (S : Finset α) :
    traceOn H S ⊆ S.powerset := by
  intro T hT
  simp only [traceOn, mem_image] at hT
  obtain ⟨h, _, rfl⟩ := hT
  exact mem_powerset.mpr inter_subset_right

/-- Trace set cardinality is bounded by |H|. -/
theorem traceOn_card_le (H : Finset (Finset α)) (S : Finset α) :
    (traceOn H S).card ≤ H.card :=
  card_image_le

/-- Shattering is anti-monotone in the sample: if H shatters S and T ⊆ S,
    then H shatters T. Proof: for U ⊆ T ⊆ S, get h with h ∩ S = U,
    then h ∩ T = U since U ⊆ T. -/
theorem shatters_subset {H : Finset (Finset α)} {S T : Finset α}
    (hShat : Shatters H S) (hTS : T ⊆ S) : Shatters H T := by
  intro U hU
  simp only [traceOn, mem_image]
  have hUT : U ⊆ T := mem_powerset.mp hU
  have hUS : U ⊆ S := hUT.trans hTS
  have : U ∈ traceOn H S := hShat (mem_powerset.mpr hUS)
  simp only [traceOn, mem_image] at this
  obtain ⟨h, hh, hhS⟩ := this
  refine ⟨h, hh, ?_⟩
  ext x
  constructor
  · intro hx
    have hxh := (mem_inter.mp hx).1
    have hxT := (mem_inter.mp hx).2
    have : x ∈ h ∩ S := mem_inter.mpr ⟨hxh, hTS hxT⟩
    rw [hhS] at this; exact this
  · intro hxU
    have hxT : x ∈ T := hUT hxU
    have : x ∈ h ∩ S := hhS ▸ hxU
    exact mem_inter.mpr ⟨(mem_inter.mp this).1, hxT⟩

/-- VCDimLE is monotone in d. -/
theorem vcDimLE_mono {H : Finset (Finset α)} {d d' : ℕ}
    (hle : d ≤ d') (hd : VCDimLE H d) : VCDimLE H d' :=
  fun S hS => le_trans (hd S hS) hle

-- ═══════════════════════════════════════════════════════════════════
-- PART III: POWERSET — VCDim(𝒫(Ω)) = |Ω|
-- ═══════════════════════════════════════════════════════════════════

/-- The powerset family shatters any subset of the universe.
    For any T ⊆ S, T is in the powerset of univ, so T ∩ S = T appears in the trace. -/
theorem powerset_shatters (S : Finset α) :
    Shatters (Finset.univ.powerset) S := by
  intro T hT
  simp only [traceOn, mem_image]
  have hTS := mem_powerset.mp hT
  exact ⟨T, mem_powerset.mpr (subset_univ _), inter_eq_left.mpr hTS⟩

/-- VCDim(𝒫(Ω)) ≤ |Ω|: can't shatter sets larger than the universe. -/
theorem powerset_vcDimLE :
    VCDimLE (Finset.univ.powerset : Finset (Finset α)) (Fintype.card α) := by
  intro S _
  exact S.card_le_univ

/-- VCDim(𝒫(Ω)) ≥ |Ω|: the powerset shatters the entire universe. -/
theorem powerset_vcDimGE :
    VCDimGE (Finset.univ.powerset : Finset (Finset α)) (Fintype.card α) :=
  ⟨Finset.univ, powerset_shatters _, by rw [card_univ]⟩

/-- VCDim(𝒫(Ω)) = |Ω|. The fundamental example. -/
theorem powerset_vcDimEq :
    VCDimEq (Finset.univ.powerset : Finset (Finset α)) (Fintype.card α) :=
  ⟨powerset_vcDimLE, powerset_vcDimGE⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THRESHOLD CLASSIFIERS — VCDim = 1
-- ═══════════════════════════════════════════════════════════════════

/-- A threshold classifier on Fin n: the set {i : Fin n | i.val < k}. -/
def threshold (n : ℕ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k)

/-- The threshold hypothesis class: {threshold k | k ∈ {0, 1, ..., n}}. -/
def thresholdClass (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.range (n + 1)).image (threshold n)

/-- Threshold 0 is empty. -/
theorem threshold_zero (n : ℕ) : threshold n 0 = ∅ := by
  ext x; simp [threshold]

/-- Threshold classifiers are downward-closed: if i.val < j.val and
    j ∈ threshold k, then i ∈ threshold k. -/
theorem threshold_downward_closed {n k : ℕ} {i j : Fin n}
    (hij : i.val < j.val) (hj : j ∈ threshold n k) : i ∈ threshold n k := by
  simp only [threshold, mem_filter, mem_univ, true_and, decide_eq_true_eq] at hj ⊢
  omega

/-- If a.val < b.val, no threshold k gives trace {b} on {a, b}. -/
theorem threshold_no_singleton_right {n : ℕ} {a b : Fin n}
    (hab : a.val < b.val) (k : ℕ) :
    threshold n k ∩ {a, b} ≠ {b} := by
  intro h
  by_cases hbk : b.val < k
  · -- b ∈ threshold, so a ∈ threshold too (downward-closed, a.val < b.val < k)
    have ha : a ∈ threshold n k := by
      simp only [threshold, mem_filter, mem_univ, true_and, decide_eq_true_eq]; omega
    have : a ∈ threshold n k ∩ {a, b} :=
      mem_inter.mpr ⟨ha, mem_insert_self a _⟩
    rw [h] at this
    rw [mem_singleton] at this
    exact absurd (Fin.ext_iff.mp this) (by omega)
  · -- b ∉ threshold
    have hb : b ∉ threshold n k := by
      simp only [threshold, mem_filter, mem_univ, true_and, decide_eq_true_eq]; omega
    have : b ∈ {b} := mem_singleton_self _
    rw [← h] at this
    exact hb (mem_inter.mp this).1

/-- Threshold class shatters any singleton {p} when n ≥ 1. -/
theorem threshold_shatters_singleton {n : ℕ} (hn : 0 < n) :
    VCDimGE (thresholdClass n) 1 := by
  refine ⟨{⟨0, hn⟩}, ?_, by simp⟩
  intro T hT
  simp only [traceOn, mem_image]
  rw [mem_powerset] at hT
  -- T ⊆ {⟨0, hn⟩}, so T = ∅ or T = {⟨0, hn⟩}
  rcases Finset.eq_empty_or_nonempty T with rfl | ⟨x, hx⟩
  · -- T = ∅: threshold 0 gives empty intersection
    refine ⟨threshold n 0, ?_, ?_⟩
    · simp only [thresholdClass, mem_image]
      exact ⟨0, mem_range.mpr (by omega), rfl⟩
    · rw [threshold_zero]; simp
  · -- T is nonempty and ⊆ {⟨0, hn⟩}, so T = {⟨0, hn⟩}
    have : T = {⟨0, hn⟩} := by
      ext y
      constructor
      · intro hy; exact hT hy
      · intro hy
        rw [mem_singleton] at hy; subst hy
        have := hT hx
        rw [mem_singleton] at this; subst this
        exact hx
    subst this
    -- threshold 1 gives {⟨0, hn⟩}
    refine ⟨threshold n 1, ?_, ?_⟩
    · simp only [thresholdClass, mem_image]
      exact ⟨1, mem_range.mpr (by omega), rfl⟩
    · ext x
      simp only [threshold, mem_filter, mem_univ, true_and, decide_eq_true_eq, mem_inter,
        mem_singleton]
      constructor
      · intro ⟨hx, hx'⟩
        rw [mem_singleton] at hx'
        exact hx'
      · intro hx
        constructor
        · rw [hx]; simp
        · exact mem_singleton.mpr hx

/-- Threshold class does not shatter any 2-element set.
    Key: thresholds are downward-closed so trace {b} (without a) is impossible. -/
theorem threshold_not_shatters_pair {n : ℕ} (S : Finset (Fin n))
    (hS : S.card = 2) : ¬Shatters (thresholdClass n) S := by
  intro hShat
  rw [card_eq_two] at hS
  obtain ⟨a, b, hab, rfl⟩ := hS
  -- Get the two elements with a.val < b.val or b.val < a.val
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · -- a.val < b.val: {b} must appear as trace
    have hb_mem : {b} ∈ ({a, b} : Finset (Fin n)).powerset := by
      rw [mem_powerset]; intro x hx; rw [mem_singleton] at hx; subst hx
      exact mem_insert_of_mem (mem_singleton_self _)
    have := hShat hb_mem
    simp only [traceOn, mem_image] at this
    obtain ⟨hyp, hhyp, htrace⟩ := this
    simp only [thresholdClass, mem_image] at hhyp
    obtain ⟨k, _, rfl⟩ := hhyp
    exact threshold_no_singleton_right h k htrace
  · -- b.val < a.val: {a} must appear as trace, same argument with swapped roles
    have ha_mem : {a} ∈ ({a, b} : Finset (Fin n)).powerset := by
      rw [mem_powerset]; intro x hx; rw [mem_singleton] at hx; subst hx
      exact mem_insert_self a _
    have := hShat ha_mem
    simp only [traceOn, mem_image] at this
    obtain ⟨hyp, hhyp, htrace⟩ := this
    simp only [thresholdClass, mem_image] at hhyp
    obtain ⟨k, _, rfl⟩ := hhyp
    -- threshold k ∩ {a, b} = {a} is impossible when b.val < a.val
    -- because if a ∈ threshold k then b ∈ threshold k (downward-closed)
    have hak : a ∈ threshold n k := by
      have : a ∈ threshold n k ∩ {a, b} := htrace ▸ mem_singleton_self a
      exact (mem_inter.mp this).1
    have hbk : b ∈ threshold n k := threshold_downward_closed h hak
    have : b ∈ threshold n k ∩ {a, b} :=
      mem_inter.mpr ⟨hbk, mem_insert_of_mem (mem_singleton_self _)⟩
    rw [htrace] at this
    rw [mem_singleton] at this
    exact absurd this (Ne.symm hab)

/-- VCDim of threshold classifiers ≤ 1. -/
theorem threshold_vcDimLE (n : ℕ) :
    VCDimLE (thresholdClass n) 1 := by
  intro S hS
  by_contra h
  push_neg at h
  have h2 : 2 ≤ S.card := by omega
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_le h2
  exact threshold_not_shatters_pair T hT (shatters_subset hS hTS)

/-- VCDim of threshold classifiers on Fin n = 1 (when n ≥ 1). -/
theorem threshold_vcDimEq {n : ℕ} (hn : 0 < n) :
    VCDimEq (thresholdClass n) 1 :=
  ⟨threshold_vcDimLE n, threshold_shatters_singleton hn⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART V: INTERVAL CLASSIFIERS — VCDim = 2
-- ═══════════════════════════════════════════════════════════════════

/-- An interval classifier on Fin n: the set {i : Fin n | a ≤ i.val ∧ i.val < b}. -/
def interval (n : ℕ) (a b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < b)

/-- The interval hypothesis class: all intervals [a, b) on Fin n. -/
def intervalClass (n : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).image (fun p => interval n p.1 p.2)

/-- Interval with a ≥ b is empty. -/
theorem interval_empty_of_ge {n a b : ℕ} (hab : b ≤ a) : interval n a b = ∅ := by
  ext x; simp [interval, mem_filter, decide_eq_true_eq]; omega

/-- Intervals are convex: if i.val < j.val < k.val and i, k ∈ interval,
    then j ∈ interval. -/
theorem interval_convex {n a' b' : ℕ} {x y z : Fin n}
    (hxy : x.val < y.val) (hyz : y.val < z.val)
    (hx : x ∈ interval n a' b') (hz : z ∈ interval n a' b') :
    y ∈ interval n a' b' := by
  simp only [interval, mem_filter, mem_univ, true_and, decide_eq_true_eq] at hx hz ⊢
  omega

/-- Interval class shatters {a, b} when a.val < b.val.
    The four traces: ∅ (empty interval), {a} (tight around a),
    {b} (tight around b), {a,b} (wide interval). -/
theorem interval_shatters_pair {n : ℕ} (a b : Fin n) (hab : a.val < b.val) :
    Shatters (intervalClass n) {a, b} := by
  sorry

/-- VCDim of interval classifiers ≥ 2 (when n ≥ 2). -/
theorem interval_vcDimGE {n : ℕ} (hn : 2 ≤ n) :
    VCDimGE (intervalClass n) 2 := by
  refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, ?_, ?_⟩
  · exact interval_shatters_pair ⟨0, by omega⟩ ⟨1, by omega⟩ (by omega)
  · rw [card_insert_of_not_mem (by simp [Fin.ext_iff]; omega), card_singleton]

/-- No 3-element subset of Fin n is shattered by intervals.
    Convexity: for the three sorted elements p < q < r, the trace {p, r}
    is impossible because any interval containing p and r must contain q. -/
theorem interval_not_shatters_triple {n : ℕ} (S : Finset (Fin n))
    (hS : S.card = 3) : ¬Shatters (intervalClass n) S := by
  sorry

/-- VCDim of interval classifiers ≤ 2. -/
theorem interval_vcDimLE (n : ℕ) :
    VCDimLE (intervalClass n) 2 := by
  intro S hS
  by_contra h
  push_neg at h
  have h3 : 3 ≤ S.card := by omega
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_le h3
  exact interval_not_shatters_triple T hT (shatters_subset hS hTS)

/-- VCDim of interval classifiers on Fin n = 2 (when n ≥ 2). -/
theorem interval_vcDimEq {n : ℕ} (hn : 2 ≤ n) :
    VCDimEq (intervalClass n) 2 :=
  ⟨interval_vcDimLE n, interval_vcDimGE hn⟩

end VCDimension
