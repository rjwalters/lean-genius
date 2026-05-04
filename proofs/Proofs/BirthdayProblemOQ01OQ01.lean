/-
  Birthday Problem OQ-01-OQ-01: Formal Distribution Analysis of Collision Count

  Open Question: Can the distribution of X (the number of birthday collision
  pairs) be analyzed formally, beyond just E[X]?

  **Answer**: Yes. This file formalizes the key distributional facts:

  1. **Definition**: X(f) = |{(i,j) : i < j, f(i) = f(j)}| for f : Fin n → Fin d
  2. **X = 0 ↔ Injective**: collisionCount f = 0 iff f is injective
  3. **Zero-collision count**: #{f | X(f) = 0} = descFactorial d n
  4. **Probability formula**: Pr(X = 0) = descFactorial(d,n) / d^n
  5. **Indicator decomposition**: X = Σ_{i<j} I_{ij}
  6. **Expected value**: E[X] = C(n,2)/d (with one HARD sorry)

  ## Mathematical Insight

  The birthday problem has two formalizations:
  - BirthdayProblem.lean: Pr(X = 0) via injective function counting
  - BirthdayProblemOQ01.lean: E[X] = C(n,2)/d via linearity of expectation

  This file UNIFIES them by formally defining X and proving both results share
  the same combinatorial foundation. The connections:

    #{f | X(f) = 0} = descFactorial d n   ←→ birthday paradox probability
    Σ_f X(f) = C(n,2) · d^{n-1}           ←→ expected value via counting

  ## Proof Status
  - X = 0 ↔ Injective: PROVED
  - #{f | X(f)=0} = descFactorial: PROVED (via Fintype.card_embedding_eq)
  - Pr(X = 0) formula: PROVED
  - Indicator decomposition: PROVED
  - X ≤ C(n,2): PROVED
  - card {f | f(i)=f(j)} = d^{n-1}: SORRY (core counting lemma)
  - card {(i,j) | i < j} = C(n,2): SORRY (ordered pair count)
  - Σ_f X(f) = C(n,2)·d^{n-1}: SORRY (double counting, depends on above)
  - E[X] = C(n,2)/d: PROVED assuming double counting
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic
import Proofs.BirthdayProblemOQ01

open BirthdayProblemOQ01 BigOperators

namespace BirthdayDistribution

variable {n d : ℕ}

-- ============================================================
-- PART I: Definitions
-- ============================================================

/-- X(f) = number of collision pairs: |{(i,j) : i < j, f(i) = f(j)}|. -/
def collisionCount (f : Fin n → Fin d) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 = f p.2)).card

/-- I_{ij}(f) = 1 if f(i) = f(j), else 0. -/
def collisionIndicator (f : Fin n → Fin d) (i j : Fin n) : ℕ :=
  if f i = f j then 1 else 0

-- ============================================================
-- PART II: X = 0 ↔ Injective
-- ============================================================

/-- X(f) = 0 iff f is injective (no two people share a birthday). -/
theorem collisionCount_eq_zero_iff {f : Fin n → Fin d} :
    collisionCount f = 0 ↔ Function.Injective f := by
  simp only [collisionCount, Finset.card_eq_zero, Finset.filter_eq_empty,
             Finset.mem_univ, forall_true_left, not_and]
  constructor
  · intro h a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd hab (h (a, b) hlt)
    · exact absurd hab.symm (h (b, a) hlt)
  · intro hinj ⟨a, b⟩ hlt heq
    exact absurd (hinj heq) (ne_of_lt hlt)

theorem injective_of_zero {f : Fin n → Fin d} (h : collisionCount f = 0) :
    Function.Injective f := collisionCount_eq_zero_iff.mp h

theorem zero_of_injective {f : Fin n → Fin d} (hf : Function.Injective f) :
    collisionCount f = 0 := collisionCount_eq_zero_iff.mpr hf

-- ============================================================
-- PART III: Zero-Collision Count = descFactorial d n
-- ============================================================

/-- #{f : Fin n → Fin d | X(f) = 0} = Nat.descFactorial d n.

    Proof chain: X(f)=0 ↔ f injective ↔ f is an embedding Fin n ↪ Fin d.
    Fintype.card_embedding_eq counts embeddings as descFactorial d n. -/
theorem card_zero_collision (n d : ℕ) :
    (Finset.univ.filter (fun f : Fin n → Fin d => collisionCount f = 0)).card =
    Nat.descFactorial d n := by
  rw [← Fintype.card_subtype]
  have e1 : {f : Fin n → Fin d // collisionCount f = 0} ≃
            {f : Fin n → Fin d // Function.Injective f} :=
    Equiv.subtypeEquivRight fun _ => collisionCount_eq_zero_iff
  have e2 : {f : Fin n → Fin d // Function.Injective f} ≃ (Fin n ↪ Fin d) :=
    { toFun    := fun ⟨f, hf⟩ => ⟨f, hf⟩
      invFun   := fun e => ⟨e.toFun, e.injective⟩
      left_inv  := fun _ => rfl
      right_inv := fun _ => Function.Embedding.ext fun _ => rfl }
  rw [Fintype.card_congr (e1.trans e2), Fintype.card_embedding_eq,
      Fintype.card_fin, Fintype.card_fin]

/-- Total assignments = d^n. -/
theorem card_all_assignments (n d : ℕ) :
    Fintype.card (Fin n → Fin d) = d ^ n := by
  simp [Fintype.card_fun]

-- ============================================================
-- PART IV: Probability Formula (Birthday Paradox Connection)
-- ============================================================

/-- **Unification**: Pr(X = 0) = descFactorial(d, n) / d^n.

    The collision-count formalization and birthday paradox formalization
    (BirthdayProblem.lean) compute the same probability. -/
theorem zero_collision_fraction (n d : ℕ) (hd : 0 < d) :
    ((Finset.univ.filter (fun f : Fin n → Fin d => collisionCount f = 0)).card : ℚ) /
    (Fintype.card (Fin n → Fin d) : ℚ) =
    (Nat.descFactorial d n : ℚ) / (d : ℚ) ^ n := by
  rw [card_zero_collision, card_all_assignments]
  push_cast; rfl

-- ============================================================
-- PART V: Indicator Decomposition
-- ============================================================

/-- X(f) = Σ_{i < j} I_{ij}(f): collision count as a sum of indicators. -/
theorem collisionCount_eq_sum_indicators (f : Fin n → Fin d) :
    collisionCount f =
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      collisionIndicator f p.1 p.2 := by
  simp only [collisionCount, collisionIndicator, Finset.card_filter, ← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ _
  by_cases h1 : i < j <;> by_cases h2 : f i = f j <;>
    simp [h1, h2, and_comm (a := i < j)]

-- ============================================================
-- PART VI: Distributional Upper Bound
-- ============================================================

/-- The number of ordered pairs (i < j) in Fin n equals C(n, 2). -/
theorem card_ordered_pairs (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card = n.choose 2 := by
  rw [Nat.choose_two_right]
  have h_offDiag : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)).card =
      n * (n - 1) := by
    have hset : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
        (Finset.univ : Finset (Fin n)).offDiag := by
      ext ⟨a, b⟩; simp [Finset.mem_offDiag]
    rw [hset, Finset.card_offDiag, Finset.card_univ, Fintype.card_fin]
  have h_symm : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).card =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)).card :=
    Finset.card_bij (fun p _ => (p.2, p.1))
      (fun ⟨a, b⟩ h => by simp_all)
      (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ _ _ h => by simp [Prod.ext_iff] at h; exact Prod.ext h.2 h.1)
      (fun ⟨a, b⟩ h => ⟨(b, a), by simp_all, by simp⟩)
  have h_disj : Disjoint ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2))
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)) := by
    apply Finset.disjoint_filter.mpr
    intro ⟨a, b⟩ _ h1 h2; exact lt_irrefl a (lt_trans h1 h2)
  have h_union : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) ∪
      (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
    ext ⟨a, b⟩; simp [ne_iff_lt_or_gt]
  rw [h_union, Finset.card_union_of_disjoint h_disj] at h_offDiag
  omega

/-- X(f) ≤ C(n, 2): at most one collision per pair. -/
theorem collisionCount_le_choose_two (f : Fin n → Fin d) :
    collisionCount f ≤ n.choose 2 := by
  unfold collisionCount
  calc (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 = f p.2)).card
      ≤ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro p _; tauto
    _ = n.choose 2 := card_ordered_pairs n

-- ============================================================
-- PART VII: Double Counting and Expected Value
-- ============================================================

/-- **Core counting lemma** (SORRY):
    #{f : Fin n → Fin d | f(i) = f(j)} = d^{n-1} for i ≠ j.

    Proof idea: Biject {f | f(i) = f(j)} with Fin d × (Fin(n-1) → Fin d):
    - Choose the shared value v = f(i) = f(j): d options
    - Assign the remaining n-2 positions freely: d^{n-2} options
    - Total: d · d^{n-2} = d^{n-1}
    The bijection uses the Fin n \ {j} ≃ Fin (n-1) index equivalence. -/
theorem card_funs_shared_birthday (n d : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter (fun f : Fin n → Fin d => f i = f j)).card = d ^ (n - 1) := by
  rw [← Fintype.card_coe]
  rw [show Fintype.card ↥(Finset.univ.filter (fun f : Fin n → Fin d => f i = f j)) =
         Fintype.card ({k : Fin n // k ≠ j} → Fin d) from
    Fintype.card_congr {
      toFun := fun ⟨f, _⟩ ⟨k, _⟩ => f k
      invFun := fun g => ⟨fun k => if h : k = j then g ⟨i, hij⟩ else g ⟨k, h⟩, by
        simp only [dif_neg hij, dif_pos rfl]⟩
      left_inv := fun ⟨f, hfij⟩ => Subtype.ext (funext fun k => by
        by_cases h : k = j
        · subst h; simp [hfij]
        · simp [h])
      right_inv := fun g => funext fun ⟨k, hk⟩ => by simp [hk]
    }]
  rw [Fintype.card_fun, Fintype.card_fin]
  congr 1
  -- Fintype.card {k : Fin n // k ≠ j} = n - 1
  rw [Fintype.card_subtype]
  rw [show Finset.univ.filter (fun k : Fin n => k ≠ j) =
         ({j} : Finset (Fin n)).compl from by ext k; simp [Finset.mem_compl]]
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]

/-- **Σ_f X(f) = C(n,2) · d^{n-1}** (double counting, SORRY):

    Swap the summation order (Fubini for finite sums):
      Σ_f X(f) = Σ_f Σ_{i<j} I_{ij}(f) = Σ_{i<j} Σ_f I_{ij}(f) = Σ_{i<j} d^{n-1} = C(n,2)·d^{n-1} -/
theorem sum_collisionCount (n d : ℕ) :
    ∑ f : Fin n → Fin d, collisionCount f = n.choose 2 * d ^ (n - 1) := by
  simp_rw [collisionCount_eq_sum_indicators]
  rw [Finset.sum_comm]
  have inner_eq : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
      ∑ f : Fin n → Fin d, collisionIndicator f p.1 p.2 = d ^ (n - 1) := by
    intro ⟨p1, p2⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [collisionIndicator, Finset.sum_boole]
    exact card_funs_shared_birthday n d p1 p2 (ne_of_lt hp)
  rw [Finset.sum_congr rfl inner_eq, Finset.sum_const, card_ordered_pairs, smul_eq_mul]

/-- **E[X] = C(n,2)/d** (PROVED assuming sum_collisionCount):

    The mean collision count computed via exact double counting equals
    the formula from BirthdayProblemOQ01 (expectedPairs). -/
theorem mean_collisionCount (n d : ℕ) (hd : 0 < d) :
    (∑ f : Fin n → Fin d, (collisionCount f : ℚ)) / (d : ℚ) ^ n =
    expectedPairs n d := by
  have hdn : (d : ℚ) ^ n ≠ 0 := by positivity
  rw [div_eq_iff hdn, ← Nat.cast_sum]
  push_cast [sum_collisionCount]
  simp only [expectedPairs]
  cases n with
  | zero => simp
  | succ n =>
    push_cast
    rw [Nat.succ_sub_one]
    field_simp
    ring

-- ============================================================
-- PART VIII: Concentration of X
-- ============================================================

/-- The variance and expectation bounds for X are available from OQ01. -/
theorem variance_bounded_by_mean (n d : ℕ) (hd : 1 ≤ d) :
    0 ≤ variancePairs n d ∧ variancePairs n d ≤ expectedPairs n d :=
  ⟨variancePairs_nonneg n d hd, variancePairs_le_expected n d hd⟩

/-- For n ≥ 2 people and d ≥ 1 days, E[X] > 0: we expect at least some collisions. -/
theorem mean_positive (n d : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    0 < expectedPairs n d := expectedPairs_pos n d hd hn

/-- Summary of the distributional knowledge acquired:
    For birthday assignment f : Fin n → Fin d:
    - X(f) ∈ [0, C(n,2)]                              [collisionCount_le_choose_two]
    - Pr(X = 0) = descFactorial d n / d^n              [zero_collision_fraction]
    - E[X] = C(n,2)/d                                  [mean_collisionCount]
    - Var(X) = C(n,2)·(d-1)/d²                        [variancePairs in OQ01]
    - Var(X) ≤ E[X]                                    [variance_bounded_by_mean] -/
theorem distribution_summary : True := trivial

end BirthdayDistribution
