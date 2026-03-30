/-
  Erdős Problem #321 — Distinct Subset Sums of Unit Fractions

  Let R(N) be the maximum size of a set A ⊆ {1, ..., N} such that all
  subset sums Σ_{n ∈ S} 1/n are distinct for S ⊆ A.

  Known bounds (Bleicher–Erdős, 1975–1976):
    (N/log N) · Π_{i=3}^{k} log_i N ≤ R(N) ≤ (1/log 2) · log_r N · (N/log N) · Π_{i=3}^{r} log_i N

  where log_i denotes the i-fold iterated logarithm.

  The gap between upper and lower bounds is essentially a single
  iterated logarithm factor.

  Status: OPEN
  Reference: https://erdosproblems.com/321
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos321

open Classical in
noncomputable instance {α : Type*} (p : α → Prop) : DecidablePred p :=
  fun _ => Classical.dec _

/- ## Definitions -/

/-- A subset A ⊆ {1,...,N} has distinct subset sums of reciprocals:
    for any two distinct subsets S, T ⊆ A, Σ_{n∈S} 1/n ≠ Σ_{n∈T} 1/n. -/
def HasDistinctReciprocalSums (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S ≠ T →
    Finset.sum S (fun n => (1 : ℚ) / n) ≠ Finset.sum T (fun n => (1 : ℚ) / n)

/-- Equivalent injective formulation: the function S ↦ Σ_{n∈S} 1/n is
    injective on subsets of A. -/
def HasDistinctReciprocalSums' (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A →
    Finset.sum S (fun n => (1 : ℚ) / n) = Finset.sum T (fun n => (1 : ℚ) / n) → S = T

/-- The two definitions are equivalent. -/
theorem hasDistinctReciprocalSums_iff (A : Finset ℕ) :
    HasDistinctReciprocalSums A ↔ HasDistinctReciprocalSums' A := by
  constructor
  · intro h S T hS hT heq
    by_contra hne
    exact h S T hS hT hne heq
  · intro h S T hS hT hne heq
    exact hne (h S T hS hT heq)

/- ## Structural Properties -/

/-- The empty set trivially has distinct reciprocal sums (vacuously). -/
theorem empty_hasDistinctReciprocalSums : HasDistinctReciprocalSums ∅ := by
  intro S T hS hT hne
  rw [Finset.subset_empty] at hS hT
  subst hS; subst hT
  exact absurd rfl hne

/-- The property is hereditary: subsets of sets with distinct reciprocal sums
    also have distinct reciprocal sums. -/
theorem HasDistinctReciprocalSums.subset {A B : Finset ℕ}
    (hA : HasDistinctReciprocalSums A) (hBA : B ⊆ A) :
    HasDistinctReciprocalSums B := by
  intro S T hS hT hne
  exact hA S T (hS.trans hBA) (hT.trans hBA) hne

/-- Any singleton {n} has distinct reciprocal sums
    (the only subsets are ∅ with sum 0 and {n} with sum 1/n). -/
theorem singleton_hasDistinctReciprocalSums (n : ℕ) (hn : n ≥ 1) :
    HasDistinctReciprocalSums {n} := by
  intro S T hS hT hne
  rw [Finset.subset_singleton_iff] at hS hT
  -- S and T are each ∅ or {n}, and they're different
  rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
  · exact absurd rfl hne
  · simp [Finset.sum_singleton]; positivity
  · simp [Finset.sum_singleton]; positivity
  · exact absurd rfl hne

/-- Subsets of a two-element set {a, b} are: ∅, {a}, {b}, {a, b}. -/
private lemma subset_pair_cases {a b : ℕ} (_hab : a ≠ b) {S : Finset ℕ}
    (hS : S ⊆ {a, b}) : S = ∅ ∨ S = {a} ∨ S = {b} ∨ S = {a, b} := by
  have hmem : ∀ x ∈ S, x = a ∨ x = b := fun x hx =>
    (Finset.mem_insert.mp (hS hx)).imp_right Finset.mem_singleton.mp
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · right; right; right
    exact Finset.Subset.antisymm hS (fun x hx =>
      ((Finset.mem_insert.mp hx).imp_right Finset.mem_singleton.mp).elim
        (fun h => h ▸ ha) (fun h => h ▸ hb))
  · right; left
    exact Finset.Subset.antisymm
      (fun x hx => Finset.mem_singleton.mpr
        ((hmem x hx).resolve_right (fun h => hb (h ▸ hx))))
      (Finset.singleton_subset_iff.mpr ha)
  · right; right; left
    exact Finset.Subset.antisymm
      (fun x hx => Finset.mem_singleton.mpr
        ((hmem x hx).resolve_left (fun h => ha (h ▸ hx))))
      (Finset.singleton_subset_iff.mpr hb)
  · left
    exact Finset.eq_empty_of_forall_notMem fun x hx =>
      (hmem x hx).elim (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx))

/-- Pair {m, n} with m < n has distinct reciprocal sums.
    Since m < n and both ≥ 1, we have 0 < 1/n < 1/m < 1/m + 1/n,
    so all 4 subset sums are distinct. -/
theorem pair_hasDistinctReciprocalSums (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1)
    (hmn : m < n) : HasDistinctReciprocalSums {m, n} := by
  have hmn_ne : m ≠ n := Nat.ne_of_lt hmn
  have hm_pos : (0 : ℚ) < 1 / (m : ℚ) := by positivity
  have hn_pos : (0 : ℚ) < 1 / (n : ℚ) := by positivity
  have hmn_lt : (1 : ℚ) / n < 1 / m :=
    div_lt_div_of_pos_left one_pos (by positivity : (0 : ℚ) < m)
      (by exact_mod_cast hmn : (m : ℚ) < n)
  intro S T hS hT hne heq
  rcases subset_pair_cases hmn_ne hS with rfl | rfl | rfl | rfl <;>
  rcases subset_pair_cases hmn_ne hT with rfl | rfl | rfl | rfl <;>
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_pair hmn_ne] at heq <;>
  first | exact hne rfl | linarith

/- ## R(N) Definition -/

/-- R(N): the maximum size of A ⊆ {1,...,N} with distinct
    reciprocal subset sums. -/
noncomputable def maxDistinctReciprocal (N : ℕ) : ℕ :=
  Finset.sup (Finset.filter
    (fun A => HasDistinctReciprocalSums A ∧ ∀ n ∈ A, 1 ≤ n ∧ n ≤ N)
    (Finset.range (N + 1)).powerset)
    Finset.card

/- ## Known Bounds -/

/-- **Bleicher–Erdős lower bound (1975)**: R(N) ≥ N/log N asymptotically.
    More precisely, R(N) ≥ (N/log N) · Π_{i=3}^{k} log_i N. -/
/-- **Bleicher–Erdős upper bound (1976)**: R(N) ≤ C · (N/log N) · log log N. -/
/-- **Asymptotic form**: R(N) = Θ(N/log N) up to iterated log factors. -/
/- ## Main Conjecture -/

/-- **Erdős Problem #321** (OPEN): Determine the exact asymptotic
    behavior of R(N). The gap between the known upper and lower bounds
    is essentially one iterated logarithm factor.

    Note: This existence statement is tautological — just take f = maxDistinctReciprocal.
    The real problem is to find an explicit closed-form asymptotic for f. -/
theorem erdos_321_asymptotics :
    ∃ f : ℕ → ℝ, ∀ N : ℕ, N ≥ 2 →
      (maxDistinctReciprocal N : ℝ) = f N :=
  ⟨fun N => (maxDistinctReciprocal N : ℝ), fun _ _ => rfl⟩

end Erdos321
