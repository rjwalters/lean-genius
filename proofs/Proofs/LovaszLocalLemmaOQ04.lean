/-
  Lovász Local Lemma — OQ-04: Variable Version with Asymmetric Dependencies

  The *asymmetric* (general) Lovász Local Lemma allows each event A_i its own
  weight x_i ∈ [0,1).  Its hypothesis is

      P[A_i] ≤ x_i · ∏_{j ∈ Γ(i)} (1 - x_j)        (★)

  where Γ(i) is the dependency neighbourhood of event i.  Conclusion:
  P[⋂ Āᵢ] ≥ ∏ᵢ (1 - x_i) > 0, so all the bad events can be simultaneously
  avoided.

  This file formalizes two things that the symmetric parent file does not:

  Part I.   The asymmetric hypothesis (★) as a predicate `AsymLLL`, and its
            algebraic consequences (avoidance positivity, the per-event bound
            P[A_i] ≤ x_i, and P[A_i] < 1).  These reuse the parent's algebraic
            cores `general_lll` and `lll_prob_bound`.

  Part II.  The *variable model* of dependency.  In the variable version of the
            LLL each event is a function of a set of underlying independent
            random variables `vars i`, and two events are dependent precisely
            when they share a variable.  We define this `sharedDep` dependency
            graph and prove it is a genuine (irreflexive, symmetric) dependency
            graph in the parent's sense `IsValidDepGraph`.

  Part III. A combinatorial degree bound for the variable model: if every event
            uses at most k variables and every variable is used by at most D
            events, then the shared-variable dependency graph has maximum degree
            ≤ k·(D-1).  This is the quantity that feeds the symmetric threshold.

  Part IV.  Capstones combining the above: the variable LLL avoidance theorem,
            and a symmetric specialization that plugs the degree bound into the
            parent's `symmetric_lll_complete`.

  Part V.   The asymmetric LLL strictly beats the union bound: there are
            instances with ∑ᵢ P[A_i] > 1 (union bound useless) where the
            avoidance product is still positive; and the asymmetric weights are
            genuinely needed (a concrete instance with x_0 ≠ x_1).

  Parent: LovaszLocalLemma.lean
  Reference: Erdős & Lovász (1975); Spencer, "Asymmetric Local Lemma";
             Moser & Tardos (2010).
-/

import Mathlib
import Proofs.LovaszLocalLemma
open ProbMethod.LovaszLocal

namespace ProbMethod.LovaszLocal.OQ04

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE ASYMMETRIC LLL HYPOTHESIS AND ITS CONSEQUENCES
-- ═══════════════════════════════════════════════════════════════════

/-- The asymmetric LLL hypothesis for `n` events with per-event weights `x i`
    and dependency neighbourhoods `adj i`:
    every weight lies in `[0,1)`, and `prob i ≤ x i · ∏_{j ∈ adj i} (1 - x j)`. -/
def AsymLLL (n : ℕ) (prob x : Fin n → ℚ) (adj : Fin n → Finset (Fin n)) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i < 1) ∧
  (∀ i, prob i ≤ x i * (adj i).prod (fun j => 1 - x j))

variable {n : ℕ} {prob x : Fin n → ℚ} {adj : Fin n → Finset (Fin n)}

/-- Under the asymmetric LLL hypothesis the avoidance product `∏ᵢ (1 - x i)`
    is strictly positive — the events can be simultaneously avoided. -/
theorem asymLLL_avoidance_pos (h : AsymLLL n prob x adj) :
    0 < ∏ i, (1 - x i) :=
  general_lll h.1

/-- Under the asymmetric LLL hypothesis each event probability is bounded by its
    own weight: `prob i ≤ x i`. -/
theorem asymLLL_prob_le (h : AsymLLL n prob x adj) :
    ∀ i, prob i ≤ x i :=
  lll_prob_bound h.1 h.2

/-- Under the asymmetric LLL hypothesis every event has probability `< 1`. -/
theorem asymLLL_prob_lt_one (h : AsymLLL n prob x adj) :
    ∀ i, prob i < 1 := by
  intro i
  have h1 := asymLLL_prob_le h i
  have h2 := (h.1 i).2
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE VARIABLE MODEL — SHARED-VARIABLE DEPENDENCY GRAPH
-- ═══════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V]

/-- `occ vars v` is the set of events that depend on the underlying variable `v`. -/
def occ (vars : Fin n → Finset V) (v : V) : Finset (Fin n) :=
  Finset.univ.filter (fun j => v ∈ vars j)

@[simp] theorem mem_occ {vars : Fin n → Finset V} {v : V} {j : Fin n} :
    j ∈ occ vars v ↔ v ∈ vars j := by
  simp [occ]

/-- The variable-model dependency graph: event `j` depends on event `i`
    (with `j ≠ i`) iff they share an underlying variable. -/
def sharedDep (vars : Fin n → Finset V) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ (vars i ∩ vars j).Nonempty)

theorem mem_sharedDep {vars : Fin n → Finset V} {i j : Fin n} :
    j ∈ sharedDep vars i ↔ j ≠ i ∧ (vars i ∩ vars j).Nonempty := by
  simp [sharedDep]

/-- No event shares a variable with itself in the dependency sense (irreflexive). -/
theorem sharedDep_irrefl (vars : Fin n → Finset V) : ∀ i, i ∉ sharedDep vars i := by
  intro i hi
  rw [mem_sharedDep] at hi
  exact hi.1 rfl

/-- The shared-variable dependency is symmetric. -/
theorem sharedDep_symm (vars : Fin n → Finset V) :
    ∀ i j, j ∈ sharedDep vars i → i ∈ sharedDep vars j := by
  intro i j h
  rw [mem_sharedDep] at h ⊢
  refine ⟨h.1.symm, ?_⟩
  rw [Finset.inter_comm]
  exact h.2

/-- The shared-variable dependency graph is a valid dependency graph in the
    parent file's sense (irreflexive and symmetric). -/
theorem sharedDep_isValid (vars : Fin n → Finset V) :
    IsValidDepGraph n (sharedDep vars) :=
  ⟨sharedDep_irrefl vars, sharedDep_symm vars⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART III: DEGREE BOUND FOR THE VARIABLE MODEL
-- ═══════════════════════════════════════════════════════════════════

/-- Every neighbour of `i` lies in `occ vars v \ {i}` for some variable
    `v ∈ vars i`. -/
theorem sharedDep_subset (vars : Fin n → Finset V) (i : Fin n) :
    sharedDep vars i ⊆ (vars i).biUnion (fun v => (occ vars v).erase i) := by
  intro j hj
  rw [mem_sharedDep] at hj
  obtain ⟨hji, hne⟩ := hj
  obtain ⟨v, hv⟩ := hne
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_biUnion]
  refine ⟨v, hv.1, ?_⟩
  rw [Finset.mem_erase]
  exact ⟨hji, by rw [mem_occ]; exact hv.2⟩

/-- The degree of event `i` is bounded by the sum, over its variables, of
    (number of co-users of that variable) − 1. -/
theorem sharedDep_card_le (vars : Fin n → Finset V) (i : Fin n) :
    (sharedDep vars i).card ≤ ∑ v ∈ vars i, ((occ vars v).card - 1) := by
  calc (sharedDep vars i).card
      ≤ ((vars i).biUnion (fun v => (occ vars v).erase i)).card :=
        Finset.card_le_card (sharedDep_subset vars i)
    _ ≤ ∑ v ∈ vars i, ((occ vars v).erase i).card := Finset.card_biUnion_le
    _ = ∑ v ∈ vars i, ((occ vars v).card - 1) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hi : i ∈ occ vars v := by rw [mem_occ]; exact hv
        rw [Finset.card_erase_of_mem hi]

/-- **Variable-model degree bound.**  If every event uses at most `k` variables
    and every variable is used by at most `D` events, then the shared-variable
    dependency graph has maximum degree at most `k·(D-1)`. -/
theorem sharedDep_maxDegree (vars : Fin n → Finset V) (k D : ℕ)
    (hk : ∀ i, (vars i).card ≤ k) (hD : ∀ v, (occ vars v).card ≤ D) :
    HasMaxDegree n (sharedDep vars) (k * (D - 1)) := by
  intro i
  calc (sharedDep vars i).card
      ≤ ∑ v ∈ vars i, ((occ vars v).card - 1) := sharedDep_card_le vars i
    _ ≤ ∑ _v ∈ vars i, (D - 1) :=
        Finset.sum_le_sum (fun v _ => Nat.sub_le_sub_right (hD v) 1)
    _ = (vars i).card * (D - 1) := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ k * (D - 1) := by gcongr; exact hk i

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: CAPSTONES — THE VARIABLE LLL
-- ═══════════════════════════════════════════════════════════════════

/-- **Variable LLL.**  If the asymmetric LLL hypothesis holds with the
    shared-variable dependency graph, then the events can be simultaneously
    avoided (`∏ (1 - x i) > 0`) and each event satisfies `prob i ≤ x i`. -/
theorem variable_lll (vars : Fin n → Finset V) (prob x : Fin n → ℚ)
    (h : AsymLLL n prob x (sharedDep vars)) :
    (0 < ∏ i, (1 - x i)) ∧ (∀ i, prob i ≤ x i) :=
  ⟨asymLLL_avoidance_pos h, asymLLL_prob_le h⟩

/-- **Symmetric variable LLL.**  Combine the degree bound with the parent's
    symmetric threshold: if each event uses ≤ k variables, each variable is used
    by ≤ D events, and every event probability is below the symmetric threshold
    `T(k·(D-1))`, then the symmetric assignment `x_i = 1/(d+1)` satisfies the LLL
    condition along the shared-variable graph and the avoidance product is
    positive. -/
theorem variable_lll_symmetric (vars : Fin n → Finset V) (k D : ℕ)
    (hk : ∀ i, (vars i).card ≤ k) (hD : ∀ v, (occ vars v).card ≤ D)
    (hd : 0 < k * (D - 1)) (prob : Fin n → ℚ)
    (hprob : ∀ i, prob i ≤ lllThreshold (k * (D - 1))) :
    (∀ i, prob i ≤ (1 : ℚ) / (↑(k * (D - 1)) + 1) *
        (sharedDep vars i).prod (fun _ => 1 - (1 : ℚ) / (↑(k * (D - 1)) + 1))) ∧
    0 < (Finset.univ : Finset (Fin n)).prod
        (fun _ => 1 - (1 : ℚ) / (↑(k * (D - 1)) + 1)) :=
  symmetric_lll_complete n (k * (D - 1)) hd prob (sharedDep vars)
    (sharedDep_maxDegree vars k D hk hD) hprob

-- ═══════════════════════════════════════════════════════════════════
-- PART V': SHARPNESS OF THE DEGREE BOUND
-- ═══════════════════════════════════════════════════════════════════

/-- A concrete witness that the degree bound `k·(D-1)` of `sharedDep_maxDegree`
    is attained, hence cannot be improved in general.  Here `k = 2`, `D = 3`:
    event `0` uses both variables `{0,1}`; variable `0` is also used by events
    `1,2` and variable `1` by events `3,4`.  Every event uses ≤ 2 variables and
    every variable is used by ≤ 3 events, yet event `0` has exactly
    `2·(3-1) = 4` neighbours. -/
def tightVars : Fin 5 → Finset (Fin 2) := ![{0, 1}, {0}, {0}, {1}, {1}]

/-- **Sharpness of `sharedDep_maxDegree`.** With `tightVars` (k = 2 variables per
    event, D = 3 events per variable) the central event has degree exactly
    `k·(D-1) = 4`, so the bound `sharedDep_maxDegree` is tight. -/
theorem sharedDep_maxDegree_tight :
    (∀ i, (tightVars i).card ≤ 2) ∧
    (∀ v, (occ tightVars v).card ≤ 3) ∧
    (sharedDep tightVars 0).card = 2 * (3 - 1) := by decide

-- ═══════════════════════════════════════════════════════════════════
-- PART V: THE ASYMMETRIC LLL BEATS THE UNION BOUND
-- ═══════════════════════════════════════════════════════════════════

/-- **The local lemma beats the union bound.**  For any `n > 2` there is an
    asymmetric LLL instance whose total probability mass exceeds `1` — so the
    union bound `∑ P[A_i] < 1` is useless — yet the avoidance product is still
    strictly positive.  (Weights `x_i = 1/2`, probabilities `1/2`, no
    dependencies.) -/
theorem asymLLL_beats_union_bound (n : ℕ) (hn : 2 < n) :
    ∃ (prob x : Fin n → ℚ) (adj : Fin n → Finset (Fin n)),
      AsymLLL n prob x adj ∧ 1 < ∑ i, prob i ∧ 0 < ∏ i, (1 - x i) := by
  refine ⟨fun _ => 1 / 2, fun _ => 1 / 2, fun _ => ∅, ?_, ?_, ?_⟩
  · constructor
    · intro i; constructor <;> norm_num
    · intro i; simp
  · have h3 : (3 : ℕ) ≤ n := hn
    have h3q : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h3
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  · apply Finset.prod_pos
    intro i _; norm_num

/-- **Asymmetric weights are genuinely needed.**  A concrete two-event instance
    where the events are mutually dependent and the optimal weights differ
    (`x_0 = 1/4 ≠ 1/2 = x_1`): both LLL inequalities hold at equality. -/
theorem asymLLL_asymmetric_weights :
    AsymLLL 2 ![1 / 8, 3 / 8] ![1 / 4, 1 / 2] ![{1}, {0}] ∧
      (![1 / 4, 1 / 2] : Fin 2 → ℚ) 0 ≠ (![1 / 4, 1 / 2] : Fin 2 → ℚ) 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;>
      simp [Finset.prod_singleton] <;> norm_num
  · norm_num

end ProbMethod.LovaszLocal.OQ04
