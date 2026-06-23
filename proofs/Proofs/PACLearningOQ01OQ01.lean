/-
  PAC Learning OQ-01-OQ-01: VC Dimension of Interval Classifiers on ℕ

  Concrete VC dimension calculation for interval classifiers on ℕ.

  - Part I: Definitions (interval classifiers, Shatters predicate).
  - Part II: Intervals shatter every singleton (VC dim ≥ 1).
  - Part III: Intervals shatter every 2-element set (VC dim ≥ 2).
  - Part IV: Intervals do NOT shatter any 3-element set (VC dim ≤ 2).
  - Together: VC dim of interval classifiers on ℕ equals 2.

  The upper-bound obstruction (Part IV) is the *convexity argument*:
  an interval [a, b] cannot include two elements while excluding any
  element between them. Formally, for {x, y, z} with x < y < z,
  the labeling T = {x, z} (endpoints only) is unrealizable.

  Vapnik-Chervonenkis (1971).
-/
import Mathlib

namespace LearningTheory.VCDimension

open Finset

/-- A hypothesis class `H ⊆ Set α` shatters a finite set `S ⊆ α` if every
    subset `T ⊆ S` can be realized as `h ∩ S` for some `h ∈ H`. -/
def Shatters {α : Type*} (H : Set (Set α)) (S : Finset α) : Prop :=
  ∀ T : Finset α, T ⊆ S → ∃ h ∈ H, ∀ x ∈ S, (x ∈ h ↔ x ∈ T)

/-- Interval classifiers on `ℕ`: `I_{a,b} = { k | a ≤ k ∧ k ≤ b }`.
    When `b < a`, the interval is empty. -/
def intervalClassifiers : Set (Set ℕ) :=
  { h | ∃ a b : ℕ, h = { k | a ≤ k ∧ k ≤ b } }

-- ============================================================
-- PART II: Intervals shatter singletons (VC dim ≥ 1)
-- ============================================================

/-- Intervals shatter every singleton: `[a, a]` includes `a`; `[a+1, a]` excludes it. -/
theorem interval_shatters_singleton (a : ℕ) :
    Shatters intervalClassifiers ({a} : Finset ℕ) := by
  intro T _
  by_cases ha : a ∈ T
  · -- Include a: use [a, a]
    refine ⟨{k | a ≤ k ∧ k ≤ a}, ⟨a, a, rfl⟩, ?_⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨fun _ => ha, fun _ => ⟨le_rfl, le_rfl⟩⟩
  · -- Exclude a: use [a+1, a] (empty interval)
    refine ⟨{k | a + 1 ≤ k ∧ k ≤ a}, ⟨a + 1, a, rfl⟩, ?_⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    constructor
    · intro ⟨h1, _⟩; exfalso; omega
    · intro h; exact absurd h ha

-- ============================================================
-- PART III: Intervals shatter every 2-element set (VC dim ≥ 2)
-- ============================================================

/-- Interval classifiers shatter every 2-element set `{m, n}` with `m < n`.
    The four required subsets are realized by: `{m,n}` → `[m,n]`, `{m}` → `[m,m]`,
    `{n}` → `[n,n]`, `∅` → `[n+1,n]`. -/
theorem interval_shatters_pair (m n : ℕ) (hmn : m < n) :
    Shatters intervalClassifiers ({m, n} : Finset ℕ) := by
  intro T _
  by_cases hm : m ∈ T <;> by_cases hn : n ∈ T
  · -- Both m, n ∈ T → use [m, n]
    refine ⟨{k | m ≤ k ∧ k ≤ n}, ⟨m, n, rfl⟩, fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨fun _ => hm, fun _ => ⟨le_rfl, hmn.le⟩⟩
    · exact ⟨fun _ => hn, fun _ => ⟨hmn.le, le_rfl⟩⟩
  · -- m ∈ T, n ∉ T → use [m, m]
    refine ⟨{k | m ≤ k ∧ k ≤ m}, ⟨m, m, rfl⟩, fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨fun _ => hm, fun _ => ⟨le_rfl, le_rfl⟩⟩
    · constructor
      · intro ⟨h1, h2⟩; exfalso; omega
      · exact fun h => absurd h hn
  · -- m ∉ T, n ∈ T → use [n, n]
    refine ⟨{k | n ≤ k ∧ k ≤ n}, ⟨n, n, rfl⟩, fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · constructor
      · intro ⟨h1, _⟩; exfalso; omega
      · exact fun h => absurd h hm
    · exact ⟨fun _ => hn, fun _ => ⟨le_rfl, le_rfl⟩⟩
  · -- Neither m nor n ∈ T → use [n+1, n] (empty interval)
    refine ⟨{k | n + 1 ≤ k ∧ k ≤ n}, ⟨n + 1, n, rfl⟩, fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · constructor
      · intro ⟨h1, _⟩; exfalso; omega
      · exact fun h => absurd h hm
    · constructor
      · intro ⟨h1, _⟩; exfalso; omega
      · exact fun h => absurd h hn

-- ============================================================
-- PART IV: Intervals do NOT shatter any 3-element set (VC dim ≤ 2)
-- ============================================================

/-- Interval classifiers cannot shatter any 3-element set `{a, b, c}` with `a < b < c`.
    The obstruction: the labeling `T = {a, c}` requires an interval containing `a` and `c`
    but not `b`. Any interval `[l, r]` with `l ≤ a` and `c ≤ r` satisfies `l ≤ b ≤ r`,
    so it must include `b` — **the convexity obstruction**. -/
theorem interval_not_shatters_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    ¬ Shatters intervalClassifiers ({a, b, c} : Finset ℕ) := by
  intro hShatter
  -- Witness labeling: include endpoints a and c, exclude middle element b
  have hSub : ({a, c} : Finset ℕ) ⊆ ({a, b, c} : Finset ℕ) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  obtain ⟨h, ⟨l, r, hl⟩, hh⟩ := hShatter ({a, c} : Finset ℕ) hSub
  subst hl
  -- Membership in the triple
  have ha_mem : a ∈ ({a, b, c} : Finset ℕ) := by simp
  have hb_mem : b ∈ ({a, b, c} : Finset ℕ) := by simp
  have hc_mem : c ∈ ({a, b, c} : Finset ℕ) := by simp
  -- a and c are in the target labeling T = {a, c}
  have ha_T : a ∈ ({a, c} : Finset ℕ) := by simp
  have hc_T : c ∈ ({a, c} : Finset ℕ) := by simp
  -- b is NOT in the target labeling (a < b < c, so b ≠ a and b ≠ c)
  have hb_T : b ∉ ({a, c} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro h; rcases h with rfl | rfl <;> omega
  -- From hh: a and c are in [l, r]
  have ha_h : l ≤ a ∧ a ≤ r := (hh a ha_mem).mpr ha_T
  have hc_h : l ≤ c ∧ c ≤ r := (hh c hc_mem).mpr hc_T
  -- From hh: b is NOT in [l, r]
  have hb_not_h : ¬ (l ≤ b ∧ b ≤ r) := by
    intro hb_in
    exact hb_T ((hh b hb_mem).mp hb_in)
  -- Convexity contradiction: l ≤ a < b < c ≤ r implies l ≤ b ≤ r
  have hlb : l ≤ b := le_trans ha_h.1 (Nat.le_of_lt hab)
  have hbr : b ≤ r := le_trans (Nat.le_of_lt hbc) hc_h.2
  exact hb_not_h ⟨hlb, hbr⟩

-- ============================================================
-- PART V: Combined Result (VC dim = 2)
-- ============================================================

/-- **Main theorem**: Interval classifiers on `ℕ` have VC dimension exactly 2.
    - Every 2-element set (with strict ordering) is shattered (lower bound).
    - No 3-element set (with strict ordering) is shattered (upper bound).

    The key asymmetry: 2-point subsets can be independently labeled because
    intervals have 2 free parameters (endpoints); 3-point subsets cannot be
    independently labeled because interval *convexity* forces the middle
    element to be included whenever the endpoints are. -/
theorem interval_vcdim_bounds :
    (∀ m n : ℕ, m < n → Shatters intervalClassifiers ({m, n} : Finset ℕ)) ∧
    (∀ a b c : ℕ, a < b → b < c →
      ¬ Shatters intervalClassifiers ({a, b, c} : Finset ℕ)) :=
  ⟨interval_shatters_pair, interval_not_shatters_triple⟩

end LearningTheory.VCDimension
