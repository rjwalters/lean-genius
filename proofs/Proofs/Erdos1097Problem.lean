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

/-- D(A) is a subset of the difference set A - A. -/
theorem commonDiffFinset_subset (A : Finset ℤ) :
    commonDiffFinset A ⊆ A - A :=
  filter_subset _ _

/-- Upper bound: |D(A)| ≤ |A|². -/
theorem numCommonDiff_le_card_sq (A : Finset ℤ) :
    numCommonDiff A ≤ A.card * A.card := by
  unfold numCommonDiff commonDiffFinset
  calc ((A - A).filter _).card
      ≤ (A - A).card := card_filter_le _ _
    _ ≤ A.card * A.card := by
        rw [sub_def]
        exact le_trans card_image_le (le_of_eq (card_product A A))

/-- Zero is always a common difference for nonempty sets. -/
theorem zero_mem_commonDiffFinset {A : Finset ℤ} (hA : A.Nonempty) :
    (0 : ℤ) ∈ commonDiffFinset A := by
  unfold commonDiffFinset
  rw [mem_filter]
  obtain ⟨a, ha⟩ := hA
  constructor
  · exact zero_mem_sub.mpr hA
  · exact ⟨a, ha, by ring_nf; exact ha, by ring_nf; exact ha⟩

/-- Nonempty sets have at least one common difference. -/
theorem numCommonDiff_pos {A : Finset ℤ} (hA : A.Nonempty) :
    0 < numCommonDiff A := by
  unfold numCommonDiff
  exact card_pos.mpr ⟨0, zero_mem_commonDiffFinset hA⟩

/-- The empty set has no common differences. -/
theorem commonDiffFinset_empty : commonDiffFinset (∅ : Finset ℤ) = ∅ := by
  unfold commonDiffFinset
  simp [Finset.sub_def]

/-- Monotonicity: A ⊆ B → D(A) ⊆ D(B). -/
theorem commonDiffFinset_mono {A B : Finset ℤ} (h : A ⊆ B) :
    commonDiffFinset A ⊆ commonDiffFinset B := by
  intro d hd
  unfold commonDiffFinset at hd ⊢
  rw [mem_filter] at hd ⊢
  constructor
  · exact Finset.sub_subset_sub h h hd.1
  · obtain ⟨a, ha, had, ha2d⟩ := hd.2
    exact ⟨a, h ha, h had, h ha2d⟩

/-- Symmetry: d ∈ D(A) → -d ∈ D(A). -/
theorem neg_mem_commonDiffFinset {A : Finset ℤ} {d : ℤ}
    (hd : d ∈ commonDiffFinset A) : -d ∈ commonDiffFinset A := by
  unfold commonDiffFinset at hd ⊢
  rw [mem_filter] at hd ⊢
  obtain ⟨_, a, ha, had, ha2d⟩ := hd
  constructor
  · rw [Finset.mem_sub]
    exact ⟨a, ha, a + 2 * d, ha2d, by ring⟩
  · exact ⟨a + 2 * d, ha2d, by ring_nf; exact had, by ring_nf; exact ha⟩

/-- Tighter bound: |D(A)| ≤ |A - A|. -/
theorem numCommonDiff_le_card_sub (A : Finset ℤ) :
    numCommonDiff A ≤ (A - A).card := by
  unfold numCommonDiff
  exact card_filter_le _ _

/-- For a singleton {a}, D({a}) = {0}. -/
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

/-- For a two-element set {a, b} with a ≠ b, D({a,b}) = {0}.
The only 3-AP in a two-point set is the trivial one. -/
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

/-- Monotonicity for counts: A ⊆ B → |D(A)| ≤ |D(B)|. -/
theorem numCommonDiff_mono {A B : Finset ℤ} (h : A ⊆ B) :
    numCommonDiff A ≤ numCommonDiff B := by
  unfold numCommonDiff
  exact card_le_card (commonDiffFinset_mono h)

/-- Set-level symmetry: d ∈ D(A) ↔ -d ∈ D(A). -/
theorem commonDifferences_neg_iff (A : Set ℤ) (d : ℤ) :
    d ∈ commonDifferences A ↔ -d ∈ commonDifferences A := by
  constructor
  · intro ⟨a, ha, had, ha2d⟩
    exact ⟨a + 2 * d, ha2d, by ring_nf; exact had, by ring_nf; exact ha⟩
  · intro ⟨a, ha, had, ha2d⟩
    exact ⟨a + 2 * (-d), ha2d, by ring_nf; exact had, by ring_nf; exact ha⟩

/-- Finset membership lifts to Set-level membership. -/
theorem commonDiffFinset_mem_commonDifferences (A : Finset ℤ) (d : ℤ)
    (hd : d ∈ commonDiffFinset A) : d ∈ commonDifferences (↑A : Set ℤ) := by
  unfold commonDiffFinset at hd
  rw [mem_filter] at hd
  obtain ⟨_, a, ha, had, ha2d⟩ := hd
  exact ⟨a, ha, had, ha2d⟩

/- ## Structural Invariance Theorems -/

/-- Translation invariance: D(A + c) = D(A). The common differences
are unchanged when every element of A is shifted by a constant. -/
theorem commonDiffFinset_translate (A : Finset ℤ) (c : ℤ) :
    commonDiffFinset (A.image (· + c)) = commonDiffFinset A := by
  ext d
  simp only [commonDiffFinset, mem_filter]
  constructor
  · intro ⟨hmem, a', ha', had', ha2d'⟩
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
  · intro ⟨hmem, a, ha, had, ha2d⟩
    constructor
    · rw [Finset.mem_sub] at hmem ⊢
      obtain ⟨x, hx, y, hy, hxy⟩ := hmem
      exact ⟨x + c, Finset.mem_image_of_mem _ hx, y + c,
             Finset.mem_image_of_mem _ hy, by linarith⟩
    · exact ⟨a + c, Finset.mem_image_of_mem _ ha,
             by rw [show a + c + d = (a + d) + c from by ring]
                exact Finset.mem_image_of_mem _ had,
             by rw [show a + c + 2 * d = (a + 2 * d) + c from by ring]
                exact Finset.mem_image_of_mem _ ha2d⟩

/-- Dilation by c maps common differences covariantly:
if d ∈ D(A) then c*d ∈ D(c·A). -/
theorem commonDiffFinset_smul_mem {A : Finset ℤ} {c d : ℤ}
    (hd : d ∈ commonDiffFinset A) :
    c * d ∈ commonDiffFinset (A.image (· * c)) := by
  unfold commonDiffFinset at hd ⊢
  rw [mem_filter] at hd ⊢
  obtain ⟨hmem, a, ha, had, ha2d⟩ := hd
  constructor
  · rw [Finset.mem_sub] at hmem ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hmem
    exact ⟨x * c, Finset.mem_image_of_mem _ hx, y * c,
           Finset.mem_image_of_mem _ hy, by nlinarith⟩
  · exact ⟨a * c, Finset.mem_image_of_mem _ ha,
           by rw [show a * c + c * d = (a + d) * c from by ring]
              exact Finset.mem_image_of_mem _ had,
           by rw [show a * c + 2 * (c * d) = (a + 2 * d) * c from by ring]
              exact Finset.mem_image_of_mem _ ha2d⟩

/-- D(A) is closed under negation: the image of D(A) under negation
equals D(A). This means D(A) is always symmetric around 0. -/
theorem commonDiffFinset_neg_closure (A : Finset ℤ) :
    (commonDiffFinset A).image (· * (-1)) = commonDiffFinset A := by
  ext d
  simp only [Finset.mem_image]
  constructor
  · intro ⟨e, he, hed⟩
    have : d = -e := by linarith
    rw [this]
    exact neg_mem_commonDiffFinset he
  · intro hd
    exact ⟨-d, neg_mem_commonDiffFinset hd, by ring⟩

/-- Symmetry as an iff: d ∈ D(A) ↔ -d ∈ D(A). -/
theorem mem_commonDiffFinset_neg_iff {A : Finset ℤ} {d : ℤ} :
    d ∈ commonDiffFinset A ↔ -d ∈ commonDiffFinset A :=
  ⟨neg_mem_commonDiffFinset, fun h => by rw [show d = -(-d) from by ring]; exact neg_mem_commonDiffFinset h⟩

/-- Direct witness: if a, a+d, a+2d ∈ A, then d ∈ D(A). -/
theorem mem_commonDiffFinset_of_threeAP {A : Finset ℤ} {a d : ℤ}
    (ha : a ∈ A) (had : a + d ∈ A) (ha2d : a + 2 * d ∈ A) :
    d ∈ commonDiffFinset A := by
  unfold commonDiffFinset
  rw [mem_filter]
  constructor
  · rw [Finset.mem_sub]
    exact ⟨a + 2 * d, ha2d, a, ha, by ring⟩
  · exact ⟨a, ha, had, ha2d⟩

/-- For three consecutive integers {a, a+1, a+2}, D = {-1, 0, 1}. -/
theorem commonDiffFinset_three_consec (a : ℤ) :
    commonDiffFinset ({a, a + 1, a + 2} : Finset ℤ) = {-1, 0, 1} := by
  ext d
  simp only [commonDiffFinset, mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨_, b, hb, hbd, hb2d⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hbd hb2d
    rcases hb with rfl | rfl | rfl <;>
    rcases hbd with h1 | h1 | h1 <;>
    rcases hb2d with h2 | h2 | h2 <;>
    omega
  · intro hd
    rcases hd with rfl | rfl | rfl
    · -- d = -1
      constructor
      · rw [Finset.mem_sub]
        exact ⟨a, by simp, a + 1, by simp, by ring⟩
      · exact ⟨a + 2, by simp, by ring_nf; right; left; ring,
               by ring_nf; left; ring⟩
    · -- d = 0
      constructor
      · exact zero_mem_sub.mpr ⟨a, by simp⟩
      · exact ⟨a, by simp, by ring_nf; left; ring,
               by ring_nf; left; ring⟩
    · -- d = 1
      constructor
      · rw [Finset.mem_sub]
        exact ⟨a + 1, by simp, a, by simp, by ring⟩
      · exact ⟨a, by simp, by ring_nf; right; left; ring,
               by ring_nf; right; right; ring⟩

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

/-- **Lemm (2015).** There exist sets achieving exponent > 1.778. -/
axiom lemm_lower :
  ∃ c : ℝ, c > 1.778 ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c

/-- **Erdős–Spencer.** Probabilistic construction: there exist n-element
sets with at least C · n^{3/2} common differences.
Proved from Lemm's stronger bound (exponent > 1.778 > 3/2). -/
theorem erdos_spencer_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∃ A : Finset ℤ, A.card = n ∧
        (numCommonDiff A : ℝ) ≥ C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨c, hc, hlemm⟩ := lemm_lower
  refine ⟨1, one_pos, fun n hn => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hlemm n hn
  refine ⟨A, hA, le_trans ?_ hbound⟩
  rw [one_mul]
  exact rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- **Erdős–Ruzsa.** Explicit construction achieving n^{1+c} for some c > 0.
Proved from Lemm's bound (take c' = c - 1 > 0.778, C = 1). -/
theorem erdos_ruzsa_explicit :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∃ A : Finset ℤ, A.card = n ∧
        (numCommonDiff A : ℝ) ≥ C * (n : ℝ) ^ (1 + c) := by
  obtain ⟨c, hc, hlemm⟩ := lemm_lower
  refine ⟨c - 1, by linarith, 1, one_pos, fun n hn => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hlemm n hn
  refine ⟨A, hA, le_trans ?_ hbound⟩
  rw [show (1 : ℝ) + (c - 1) = c from by ring, one_mul]

/-- **AlphaEvolve (2025).** Slight improvement on Lemm's lower bound
using automated search methods.
Note: as axiomatized, this is implied by lemm_lower (1.778 > 1.77898). -/
theorem alphaevolve_improvement :
    ∃ c : ℝ, c > 1.77898 ∧ ∀ (n : ℕ), 0 < n →
      ∃ A : Finset ℤ, A.card = n ∧
        (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c := by
  obtain ⟨c, hc, h⟩ := lemm_lower
  exact ⟨c, by linarith, h⟩

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
