/-
# Erdős Problem #1097 — Common Differences in Three-Term Arithmetic Progressions

Let A be a set of n integers. How many distinct d can occur as the
common difference of a three-term arithmetic progression in A?
Are there always O(n^{3/2}) many such d?

## Status: OPEN

## Key Results

- **Erdős–Spencer**: Probabilistic construction achieving n^{3/2} common
  differences.
- **Erdős–Ruzsa**: Explicit construction achieving n^{1+c} for some c > 0.
- **Katz–Tao (1999)**: Upper bound f(n) ≤ C · n^{11/6}.
- **Lemm (2015)**: Lower bound f(n) ≥ n^{1.77898...}.
- **AlphaEvolve (2025)**: Slight improvement on Lemm's lower bound.

Current gap: 1.778... ≤ c ≤ 11/6 ≈ 1.833.

## Equivalent Formulation

The problem is equivalent to Bourgain's sums-differences problem: find
the smallest c such that |A −_G B| ≤ C · max(|A|, |B|, |A +_G B|)^c.
This connects to the Kakeya conjecture via Bourgain's arithmetic approach.

*Reference:* [erdosproblems.com/1097](https://www.erdosproblems.com/1097)
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

/- ## Core Definitions -/

/-- A three-term AP with base a and common difference d in set A:
a, a+d, a+2d all belong to A. -/
def IsThreeAP (A : Set ℤ) (a d : ℤ) : Prop :=
  a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A

/-- The set of common differences of three-term APs in A:
  D(A) = { d : ∃ a, {a, a+d, a+2d} ⊆ A }. -/
def commonDifferences (A : Set ℤ) : Set ℤ :=
  { d | ∃ a, IsThreeAP A a d }

/-- Finite version: common differences of a finite integer set. -/
noncomputable def commonDiffFinset (A : Finset ℤ) : Finset ℤ :=
  (A - A).filter fun d => ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A

/-- Count of distinct common differences |D(A)|. -/
noncomputable def numCommonDiff (A : Finset ℤ) : ℕ :=
  (commonDiffFinset A).card

/- ## Proven Infrastructure Lemmas -/

/-- The set of common differences is a subset of the difference set A - A. -/
theorem commonDiffFinset_subset (A : Finset ℤ) :
    commonDiffFinset A ⊆ A - A :=
  filter_subset _ _

/-- Trivial upper bound: |D(A)| ≤ |A - A| ≤ |A|². This is the naive
quadratic bound that the conjecture seeks to improve to n^{3/2}. -/
theorem numCommonDiff_le_card_sq (A : Finset ℤ) :
    numCommonDiff A ≤ A.card * A.card := by
  unfold numCommonDiff commonDiffFinset
  calc ((A - A).filter _).card
      ≤ (A - A).card := card_filter_le _ _
    _ ≤ A.card * A.card := by
        rw [sub_def]
        exact le_trans card_image_le (le_of_eq (card_product A A))

/-- Zero is always a common difference for nonempty sets: every element
forms the trivial 3-AP (a, a, a) with d = 0. -/
theorem zero_mem_commonDiffFinset {A : Finset ℤ} (hA : A.Nonempty) :
    (0 : ℤ) ∈ commonDiffFinset A := by
  unfold commonDiffFinset
  rw [mem_filter]
  obtain ⟨a, ha⟩ := hA
  constructor
  · exact zero_mem_sub.mpr hA
  · exact ⟨a, ha, by ring_nf; exact ha, by ring_nf; exact ha⟩

/-- For nonempty sets, there is at least one common difference. -/
theorem numCommonDiff_pos {A : Finset ℤ} (hA : A.Nonempty) :
    0 < numCommonDiff A := by
  unfold numCommonDiff
  exact card_pos.mpr ⟨0, zero_mem_commonDiffFinset hA⟩

/-- The empty set has no common differences. -/
theorem commonDiffFinset_empty : commonDiffFinset (∅ : Finset ℤ) = ∅ := by
  unfold commonDiffFinset
  simp [Finset.sub_def]

/-- Monotonicity: larger sets have (weakly) more common differences. -/
theorem commonDiffFinset_mono {A B : Finset ℤ} (h : A ⊆ B) :
    commonDiffFinset A ⊆ commonDiffFinset B := by
  intro d hd
  unfold commonDiffFinset at hd ⊢
  rw [mem_filter] at hd ⊢
  constructor
  · exact Finset.sub_subset_sub h h hd.1
  · obtain ⟨a, ha, had, ha2d⟩ := hd.2
    exact ⟨a, h ha, h had, h ha2d⟩

/-- Symmetry: if d is a common difference, so is -d.
    Because a, a+d, a+2d ∈ A implies (a+2d), (a+2d)+(-d), (a+2d)+2(-d) ∈ A. -/
theorem neg_mem_commonDiffFinset {A : Finset ℤ} {d : ℤ}
    (hd : d ∈ commonDiffFinset A) : -d ∈ commonDiffFinset A := by
  unfold commonDiffFinset at hd ⊢
  rw [mem_filter] at hd ⊢
  obtain ⟨_, a, ha, had, ha2d⟩ := hd
  constructor
  · rw [Finset.mem_sub]
    exact ⟨a, ha, a + 2 * d, ha2d, by ring⟩
  · exact ⟨a + 2 * d, ha2d, by ring_nf; exact had, by ring_nf; exact ha⟩

/-- Tighter upper bound through the difference set: |D(A)| ≤ |A - A|.
The common differences form a subset of the difference set. -/
theorem numCommonDiff_le_card_sub (A : Finset ℤ) :
    numCommonDiff A ≤ (A - A).card := by
  unfold numCommonDiff
  exact card_filter_le _ _

/-- For a singleton {a}, the only common difference is 0. -/
theorem commonDiffFinset_singleton (a : ℤ) :
    commonDiffFinset ({a} : Finset ℤ) = {0} := by
  ext d
  constructor
  · intro hd
    unfold commonDiffFinset at hd
    rw [mem_filter] at hd
    obtain ⟨_, b, hb, hbd, _⟩ := hd
    rw [Finset.mem_singleton] at hb hbd
    rw [Finset.mem_singleton]
    linarith
  · intro hd
    rw [Finset.mem_singleton] at hd
    rw [hd]
    exact zero_mem_commonDiffFinset ⟨a, Finset.mem_singleton_self a⟩

/-- Translation invariance: the set of common differences is unchanged
when every element of A is shifted by a constant c. -/
theorem commonDiffFinset_translate (A : Finset ℤ) (c : ℤ) :
    commonDiffFinset (A.image (· + c)) = commonDiffFinset A := by
  ext d
  simp only [commonDiffFinset, mem_filter]
  constructor
  · -- D(A+c) ⊆ D(A): un-translate witnesses
    intro ⟨hmem, a', ha', had', ha2d'⟩
    simp only [Finset.mem_image] at ha' had' ha2d'
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨b, hb, hbd⟩ := had'
    obtain ⟨e, he, hed⟩ := ha2d'
    have hbeq : b = a + d := by linarith
    have heeq : e = a + 2 * d := by linarith
    constructor
    · rw [Finset.mem_sub]
      exact ⟨a, ha, a + 2 * d, heeq ▸ he, by ring⟩
    · exact ⟨a, ha, hbeq ▸ hb, heeq ▸ he⟩
  · -- D(A) ⊆ D(A+c): translate witnesses
    intro ⟨hmem, a, ha, had, ha2d⟩
    constructor
    · rw [Finset.mem_sub] at hmem ⊢
      obtain ⟨x, hx, y, hy, hxy⟩ := hmem
      exact ⟨x + c, Finset.mem_image_of_mem _ hx, y + c, Finset.mem_image_of_mem _ hy,
             by linarith⟩
    · exact ⟨a + c, Finset.mem_image_of_mem _ ha,
             by rw [show a + c + d = (a + d) + c from by ring]; exact Finset.mem_image_of_mem _ had,
             by rw [show a + c + 2 * d = (a + 2 * d) + c from by ring]; exact Finset.mem_image_of_mem _ ha2d⟩

/-- The Set-level common differences are symmetric: d ∈ D(A) ↔ -d ∈ D(A). -/
theorem commonDifferences_neg_iff (A : Set ℤ) (d : ℤ) :
    d ∈ commonDifferences A ↔ -d ∈ commonDifferences A := by
  constructor
  · intro ⟨a, ha, had, ha2d⟩
    exact ⟨a + 2 * d, ha2d, by ring_nf; exact had, by ring_nf; exact ha⟩
  · intro ⟨a, ha, had, ha2d⟩
    exact ⟨a + 2 * (-d), ha2d, by ring_nf; exact had, by ring_nf; exact ha⟩

/-- Any element of commonDiffFinset is also in the Set-level commonDifferences. -/
theorem commonDiffFinset_mem_commonDifferences (A : Finset ℤ) (d : ℤ)
    (hd : d ∈ commonDiffFinset A) : d ∈ commonDifferences (↑A : Set ℤ) := by
  unfold commonDiffFinset at hd
  rw [mem_filter] at hd
  obtain ⟨_, a, ha, had, ha2d⟩ := hd
  exact ⟨a, ha, had, ha2d⟩

/-- Monotonicity for numCommonDiff: larger sets have at least as many
common differences. -/
theorem numCommonDiff_mono {A B : Finset ℤ} (h : A ⊆ B) :
    numCommonDiff A ≤ numCommonDiff B := by
  unfold numCommonDiff
  exact card_le_card (commonDiffFinset_mono h)

/- ## Structural Theorems -/

/-- For a two-element set {a, b} with a ≠ b, the only common difference is 0.
This is because the only 3-AP in a two-point set is the trivial one.
For d = b-a, we'd need 2b-a ∈ {a,b}, giving b = a (contradiction). -/
theorem commonDiffFinset_pair {a b : ℤ} (hab : a ≠ b) :
    commonDiffFinset ({a, b} : Finset ℤ) = {0} := by
  ext d
  constructor
  · intro hd
    unfold commonDiffFinset at hd
    rw [mem_filter] at hd
    obtain ⟨_, x, hx, hxd, hx2d⟩ := hd
    rw [Finset.mem_singleton]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hxd hx2d
    rcases hx with rfl | rfl <;> rcases hxd with h | h <;> rcases hx2d with h' | h' <;> omega
  · intro hd
    rw [Finset.mem_singleton] at hd
    rw [hd]
    exact zero_mem_commonDiffFinset ⟨a, Finset.mem_insert_self a _⟩

/-- An arithmetic progression {a, a+d, a+2d} has d as a common difference
at the Set level. -/
theorem ap_three_has_diff (A : Set ℤ) (a d : ℤ)
    (ha : a ∈ A) (had : a + d ∈ A) (ha2d : a + 2 * d ∈ A) :
    d ∈ commonDifferences A :=
  ⟨a, ha, had, ha2d⟩

/-- If A ⊆ B at the Set level, then D(A) ⊆ D(B). -/
theorem commonDifferences_mono {A B : Set ℤ} (h : A ⊆ B) :
    commonDifferences A ⊆ commonDifferences B := by
  intro d ⟨a, ha, had, ha2d⟩
  exact ⟨a, h ha, h had, h ha2d⟩

/-- Involution property: negating all common differences gives back
the same set. This follows from the symmetry theorem. -/
theorem commonDiffFinset_neg_image (A : Finset ℤ) :
    (commonDiffFinset A).image (· * (-1)) ⊆ commonDiffFinset A := by
  intro d hd
  rw [Finset.mem_image] at hd
  obtain ⟨e, he, rfl⟩ := hd
  have : -e ∈ commonDiffFinset A := neg_mem_commonDiffFinset he
  convert this using 1
  ring

/- ## Minimum Set Size for Non-Trivial Differences -/

/-- A non-zero common difference d ≠ 0 requires three distinct elements:
    a, a+d, a+2d are all distinct when d ≠ 0. -/
theorem three_distinct_of_nonzero_diff {A : Set ℤ} {a d : ℤ}
    (hAP : IsThreeAP A a d) (hd : d ≠ 0) :
    a ≠ a + d ∧ a + d ≠ a + 2 * d ∧ a ≠ a + 2 * d := by
  constructor
  · intro h; linarith
  · constructor
    · intro h; linarith
    · intro h; linarith

/-- If d ≠ 0 is a common difference of A, then |A| ≥ 3.
This is tight: {0,1,2} has d=1 and |A|=3. -/
theorem card_ge_three_of_nonzero_diff {A : Finset ℤ} {d : ℤ}
    (hd : d ∈ commonDiffFinset A) (hne : d ≠ 0) : 3 ≤ A.card := by
  unfold commonDiffFinset at hd
  rw [mem_filter] at hd
  obtain ⟨_, a, ha, had, ha2d⟩ := hd
  have h1 : a ≠ a + d := by intro h; linarith
  have h2 : a + d ≠ a + 2 * d := by intro h; linarith
  have h3 : a ≠ a + 2 * d := by intro h; linarith
  have hcard : ({a, a + d, a + 2 * d} : Finset ℤ).card = 3 := by
    rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
    · simp [h2]
    · simp [h1, h3]
  calc 3 = ({a, a + d, a + 2 * d} : Finset ℤ).card := hcard.symm
    _ ≤ A.card := card_le_card (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ha
        · exact had
        · exact ha2d)

/- ## Computable Small-Case Verification -/

section ComputableVerification
attribute [-instance] Classical.propDecidable

-- Computable version matching commonDiffFinset for decide proofs
private def cdf (A : Finset ℤ) : Finset ℤ :=
  (A - A).filter fun d => ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A

/-- Verified: D(∅) = ∅. -/
theorem cdf_empty_eq : cdf (∅ : Finset ℤ) = ∅ := by decide

/-- Verified: D({0}) = {0}. -/
theorem cdf_singleton_zero : cdf ({0} : Finset ℤ) = {0} := by decide

/-- Verified: D({5}) = {0}. -/
theorem cdf_singleton_five : cdf ({5} : Finset ℤ) = {0} := by decide

/-- Verified: D({1,4}) = {0} — no non-trivial 3-AP in a 2-element set. -/
theorem cdf_pair_14 : cdf ({1, 4} : Finset ℤ) = {0} := by decide

/-- Verified: D({0,1,2}) = {-1, 0, 1} — the interval [0,2] has
3 common differences: d=0 (trivial), d=1 (AP 0,1,2), d=-1 (AP 2,1,0). -/
theorem cdf_012 : cdf ({0, 1, 2} : Finset ℤ) = {-1, 0, 1} := by decide

/-- Verified: D({0,1,2,3}) = {-1, 0, 1} — interval [0,3] still has
only 3 common differences since max d is ⌊(n-1)/2⌋ = 1. -/
theorem cdf_0123 : cdf ({0, 1, 2, 3} : Finset ℤ) = {-1, 0, 1} := by decide

/-- Verified: D({0,1,2,3,4}) = {-2,-1,0,1,2} — interval [0,4] gains
d=±2 via the AP (0,2,4). |D| = 5 for n = 5. -/
theorem cdf_01234 : cdf ({0, 1, 2, 3, 4} : Finset ℤ) = {-2, -1, 0, 1, 2} := by decide

end ComputableVerification

/- ## Main Conjecture -/

/-- **Erdős Problem #1097 (Open).**
Is f(n) = O(n^{3/2})? That is, does there exist C such that every
n-element set A of integers satisfies |D(A)| ≤ C · n^{3/2}? -/
def erdos_1097_conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
    (numCommonDiff A : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)

/- ## Upper Bound -/

/-- **Katz–Tao (1999).** f(n) ≤ C · n^{11/6} for some absolute constant C.
This is the best known upper bound on the exponent. -/
axiom katz_tao_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
    (numCommonDiff A : ℝ) ≤ C * (n : ℝ) ^ ((11 : ℝ) / 6)

/- ## Lower Bounds -/

/-- **Erdős–Spencer.** Probabilistic construction: there exist n-element
sets with at least C · n^{3/2} common differences. -/
axiom erdos_spencer_lower :
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ C * (n : ℝ) ^ ((3 : ℝ) / 2)

/-- **Erdős–Ruzsa.** Explicit construction achieving n^{1+c} for some c > 0. -/
axiom erdos_ruzsa_explicit :
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ C * (n : ℝ) ^ (1 + c)

/-- **Lemm (2015).** There exist sets achieving exponent > 1.778. -/
axiom lemm_lower :
  ∃ c : ℝ, c > 1.778 ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c

/-- **AlphaEvolve (2025).** Slight improvement on Lemm's lower bound
using automated search methods. -/
axiom alphaevolve_improvement :
  ∃ c : ℝ, c > 1.77898 ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c

/- ## Bourgain's Sums-Differences Equivalence -/

/-- Restricted sum: { a + b : (a,b) ∈ G }. -/
def restrictedSum (G : Finset (ℤ × ℤ)) : Finset ℤ :=
  G.image fun p => p.1 + p.2

/-- Restricted difference: { a − b : (a,b) ∈ G }. -/
def restrictedDiff (G : Finset (ℤ × ℤ)) : Finset ℤ :=
  G.image fun p => p.1 - p.2

/-- **Bourgain's sums-differences exponent.** The exponent c holds if
|A −_G B| ≤ C · max(|A|, |B|, |A +_G B|)^c for all A, B, G ⊆ A × B. -/
def BourgainExponent (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (A B : Finset ℤ) (G : Finset (ℤ × ℤ)),
      G ⊆ A ×ˢ B →
      ((restrictedDiff G).card : ℝ) ≤
        C * ((max (max A.card B.card) (restrictedSum G).card : ℕ) : ℝ) ^ c

/-- **Chan's Equivalence.** The optimal exponent for common differences
equals the critical Bourgain exponent. This connects the combinatorial
3-AP problem to harmonic analysis and the Kakeya conjecture. -/
axiom chan_equivalence :
  ∀ c : ℝ, c ≥ 1 →
    (∀ (n : ℕ), 0 < n →
      ∃ A : Finset ℤ, A.card = n ∧ (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c) ↔
    ¬BourgainExponent c

/- ## Summary -/

/-- The current state of knowledge: 1.778 < c* ≤ 11/6 ≈ 1.833. -/
theorem current_bounds_summary :
    (∃ c : ℝ, c > 1.778 ∧ ∀ (n : ℕ), 0 < n →
      ∃ A : Finset ℤ, A.card = n ∧ (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
      (numCommonDiff A : ℝ) ≤ C * (n : ℝ) ^ ((11 : ℝ) / 6)) :=
  ⟨lemm_lower, katz_tao_upper⟩
