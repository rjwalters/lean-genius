/-
Erdős Problem #667: Clique Density Exponent c(p,q)

Source: https://erdosproblems.com/667
Status: OPEN

Statement:
For fixed integers p, q ≥ 1, define H(n; p, q) as the largest m such that
every graph on n vertices where every set of p vertices spans at least q
edges must contain a complete graph on m vertices.

Define c(p, q) = lim inf (log H(n; p, q)) / (log n).

Is c(p, q) strictly increasing in q for 1 ≤ q ≤ C(p-1, 2) + 1?

Known results:
- q = 1: reduces to classical Ramsey; 1/(p-1) ≤ c(p,1) ≤ 2/(p+1)
- q = C(p-1,2) + 1: every p-set spans a complete graph, so c(p,q) = 1
- Erdős-Faudree-Rousseau-Schelp: c(p, C(p-1,2)) ≤ 1/2

Reference: [Er97f], https://erdosproblems.com/667

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

open Finset SimpleGraph

namespace Erdos667

/-
## Part I: Graph-Theoretic Foundations

We formalize the edge density condition: every p-subset spans at least q edges.
-/

/-- The number of edges a graph G induces on a subset S of vertices. -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ G.Adj p.1 p.2)).card / 2

/-- A graph satisfies the (p,q)-density condition if every p-element subset
    spans at least q edges. -/
def HasDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℕ) : Prop :=
  ∀ S : Finset V, S.card = p → edgeCount G S ≥ q

/-
## Part II: The Function H(n; p, q)

H(n; p, q) is the largest m such that every n-vertex graph with the
(p,q)-density condition contains a complete subgraph on m vertices.
-/

/-- H(n; p, q): the largest clique size guaranteed in any n-vertex graph
    satisfying the (p,q)-density condition.
    Axiomatized as the precise Ramsey-type extremal function. -/
axiom cliqueGuarantee : ℕ → ℕ → ℕ → ℕ

-- Notation: H(n; p, q) = cliqueGuarantee n p q

/-- H is monotone in n: more vertices can only help. -/
axiom cliqueGuarantee_mono_n (p q n : ℕ) :
    cliqueGuarantee n p q ≤ cliqueGuarantee (n + 1) p q

/-- H is monotone in q: more edges per p-set yields larger cliques. -/
axiom cliqueGuarantee_mono_q (n p q : ℕ) :
    cliqueGuarantee n p q ≤ cliqueGuarantee n p (q + 1)

/-- H(n; p, q) ≤ n: cannot guarantee a clique larger than the graph. -/
axiom cliqueGuarantee_le_n (n p q : ℕ) :
    cliqueGuarantee n p q ≤ n

/-
## Part III: Boundary Values

The function c(p,q) has known values at the endpoints.
-/

/-- When q = C(p-1, 2) + 1, every p-set is a clique, forcing G to be complete.
    Hence H(n; p, q) = n. -/
axiom cliqueGuarantee_max (n p : ℕ) (hp : 2 ≤ p) :
    cliqueGuarantee n p (Nat.choose (p - 1) 2 + 1) = n

/-- When q = 0, there is no constraint, so H(n; p, 0) = 1 trivially
    (every graph has at least one vertex, forming a trivial clique). -/
axiom cliqueGuarantee_zero (n p : ℕ) (hn : 1 ≤ n) :
    cliqueGuarantee n p 0 = 1

/-- Extended monotonicity: H(n; p, q1) ≤ H(n; p, q2) for q1 ≤ q2. -/
theorem cliqueGuarantee_mono_q_general (n p q1 q2 : ℕ) (h : q1 ≤ q2) :
    cliqueGuarantee n p q1 ≤ cliqueGuarantee n p q2 := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (cliqueGuarantee_mono_q n p _)

/-- H(n; p, q) ≥ 1 for any non-empty graph.
    Proved: H(n,p,0) = 1 and H is monotone in q, so H(n,p,q) ≥ 1 for all q.
    (Previously axiomatized; now derived from cliqueGuarantee_zero + monotonicity.) -/
theorem cliqueGuarantee_pos (n p q : ℕ) (hn : 1 ≤ n) :
    1 ≤ cliqueGuarantee n p q := by
  have h0 : cliqueGuarantee n p 0 = 1 := cliqueGuarantee_zero n p hn
  have hmono := cliqueGuarantee_mono_q_general n p 0 q (Nat.zero_le q)
  linarith

/-
## Part IV: The Exponent c(p, q)

c(p, q) = lim inf (log H(n; p, q)) / (log n) as n tends to infinity.
-/

/-- c(p, q) = lim inf log(H(n;p,q)) / log(n).
    Axiomatized as a rational-valued function. -/
axiom cpq : ℕ → ℕ → ℚ

/-- c(p,q) ≥ 0 (H(n;p,q) ≥ 1 for all n). -/
axiom cpq_nonneg (p q : ℕ) : 0 ≤ cpq p q

/-- c(p,q) ≤ 1 (H(n;p,q) ≤ n for all n). -/
axiom cpq_le_one (p q : ℕ) : cpq p q ≤ 1

/-- c is weakly increasing in q (from monotonicity of H in q). -/
axiom cpq_mono_q (p q : ℕ) : cpq p q ≤ cpq p (q + 1)

/-
## Part V: Known Bounds

Established results on c(p,q).
-/

/-- c(p, 1) ≥ 1/(p-1) (Ramsey lower bound). -/
axiom cpq_lower_ramsey (p : ℕ) (hp : 2 ≤ p) :
    (1 : ℚ) / ((p : ℚ) - 1) ≤ cpq p 1

/-- c(p, 1) ≤ 2/(p+1) (Ramsey upper bound). -/
axiom cpq_upper_ramsey (p : ℕ) (hp : 2 ≤ p) :
    cpq p 1 ≤ (2 : ℚ) / ((p : ℚ) + 1)

/-- c(p, C(p-1,2)+1) = 1: at maximum density, full clique is guaranteed. -/
axiom cpq_at_max (p : ℕ) (hp : 2 ≤ p) :
    cpq p (Nat.choose (p - 1) 2 + 1) = 1

/-- Erdos-Faudree-Rousseau-Schelp: c(p, C(p-1,2)) ≤ 1/2.
    The second-to-last value of q already forces c ≤ 1/2. -/
axiom efrs_bound (p : ℕ) (hp : 3 ≤ p) :
    cpq p (Nat.choose (p - 1) 2) ≤ (1 : ℚ) / 2

/-
## Part VI: Proved Consequences

Theorems derived from the axiomatized facts.
-/

/-- c(p,q) increases from the Ramsey value to 1 as q ranges from 1 to C(p-1,2)+1.
    Specifically: c(p,1) ≤ 1 and c(p, C(p-1,2)+1) = 1 for p ≥ 2. -/
theorem cpq_range (p : ℕ) (hp : 2 ≤ p) :
    cpq p 1 ≤ 1 ∧ cpq p (Nat.choose (p - 1) 2 + 1) = 1 :=
  ⟨cpq_le_one p 1, cpq_at_max p hp⟩

/-- The EFRS bound implies a gap: c(p, C(p-1,2)) < c(p, C(p-1,2)+1) for p ≥ 3.
    This is a strict increase at the last step. -/
theorem cpq_strict_at_top (p : ℕ) (hp : 3 ≤ p) :
    cpq p (Nat.choose (p - 1) 2) < cpq p (Nat.choose (p - 1) 2 + 1) := by
  have h1 := efrs_bound p hp
  have h2 := cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp)
  rw [h2]
  linarith

/-- For p ≥ 3, the Ramsey lower bound gives c(p,1) > 0. -/
theorem cpq_pos_at_one (p : ℕ) (hp : 3 ≤ p) : (0 : ℚ) < cpq p 1 := by
  have h := cpq_lower_ramsey p (le_trans (by omega : 2 ≤ 3) hp)
  have : (0 : ℚ) < (1 : ℚ) / ((p : ℚ) - 1) := by
    apply div_pos
    · exact one_pos
    · have : (p : ℚ) ≥ 3 := by exact_mod_cast hp
      linarith
  linarith

/-- Weak monotonicity extended: c(p, q1) ≤ c(p, q2) for q1 ≤ q2. -/
theorem cpq_mono_q_general (p q1 q2 : ℕ) (h : q1 ≤ q2) :
    cpq p q1 ≤ cpq p q2 := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (cpq_mono_q p _)

/-- The Ramsey bound interval: for p ≥ 2, c(p,1) lies in [1/(p-1), 2/(p+1)]. -/
theorem cpq_ramsey_interval (p : ℕ) (hp : 2 ≤ p) :
    (1 : ℚ) / ((p : ℚ) - 1) ≤ cpq p 1 ∧ cpq p 1 ≤ (2 : ℚ) / ((p : ℚ) + 1) :=
  ⟨cpq_lower_ramsey p hp, cpq_upper_ramsey p hp⟩

/-
## Part VII: Small Cases

For small values of p, we can compute the range of q and verify structure.
-/

/-- For p = 3: C(2,2) + 1 = 2. So q ranges over {1, 2}.
    c(3,2) = 1 (the graph must be complete). -/
theorem p3_max : cpq 3 (Nat.choose 2 2 + 1) = 1 := cpq_at_max 3 (by omega)

/-- For p = 3: the conjecture reduces to c(3,1) < c(3,2) = 1. -/
theorem p3_strict : cpq 3 1 < cpq 3 2 := by
  have h2 : cpq 3 2 = 1 := by
    have : Nat.choose 2 2 + 1 = 2 := by native_decide
    rw [← this]; exact cpq_at_max 3 (by omega)
  rw [h2]
  have := cpq_upper_ramsey 3 (by omega)
  have : (2 : ℚ) / ((3 : ℚ) + 1) = 1 / 2 := by norm_num
  linarith

/-- For p = 4: C(3,2) + 1 = 4. So q ranges over {1, 2, 3, 4}.
    c(4,4) = 1. -/
theorem p4_max : cpq 4 (Nat.choose 3 2 + 1) = 1 := cpq_at_max 4 (by omega)

/-- For p = 4: EFRS gives c(4,3) ≤ 1/2, and c(4,4) = 1. -/
theorem p4_efrs : cpq 4 (Nat.choose 3 2) ≤ (1 : ℚ) / 2 :=
  efrs_bound 4 (by omega)

/-- For p = 4: strict increase at the top: c(4,3) < c(4,4) = 1. -/
theorem p4_strict_at_top : cpq 4 (Nat.choose 3 2) < cpq 4 (Nat.choose 3 2 + 1) :=
  cpq_strict_at_top 4 (by omega)

/-- For p = 5: C(4,2) + 1 = 7. So q ranges over {1, 2, 3, 4, 5, 6, 7}.
    c(5,7) = 1. -/
theorem p5_max : cpq 5 (Nat.choose 4 2 + 1) = 1 := cpq_at_max 5 (by omega)

/-- For p = 5: EFRS gives c(5,6) ≤ 1/2. -/
theorem p5_efrs : cpq 5 (Nat.choose 4 2) ≤ (1 : ℚ) / 2 :=
  efrs_bound 5 (by omega)

/-- For p = 5: strict increase at the top: c(5,6) < c(5,7) = 1. -/
theorem p5_strict_at_top : cpq 5 (Nat.choose 4 2) < cpq 5 (Nat.choose 4 2 + 1) :=
  cpq_strict_at_top 5 (by omega)

/-- For p = 5: the Ramsey lower bound gives c(5,1) ≥ 1/4. -/
theorem p5_ramsey_lower : (1 : ℚ) / 4 ≤ cpq 5 1 := by
  have h := cpq_lower_ramsey 5 (by omega)
  norm_num at h ⊢
  exact h

/-- For p = 5: the Ramsey upper bound gives c(5,1) ≤ 1/3. -/
theorem p5_ramsey_upper : cpq 5 1 ≤ (1 : ℚ) / 3 := by
  have h := cpq_upper_ramsey 5 (by omega)
  norm_num at h ⊢
  exact h

/-- For p = 4: Ramsey bounds give c(4,1) ∈ [1/3, 2/5]. -/
theorem p4_ramsey_lower : (1 : ℚ) / 3 ≤ cpq 4 1 := by
  have h := cpq_lower_ramsey 4 (by omega)
  norm_num at h ⊢; exact h

theorem p4_ramsey_upper : cpq 4 1 ≤ (2 : ℚ) / 5 := by
  have h := cpq_upper_ramsey 4 (by omega)
  norm_num at h ⊢; exact h

/-- For p = 3: cpq_strict already proves the FULL conjecture for p=3
    (there is only one step: q goes from 1 to 2). -/
theorem erdos667_holds_for_p3 :
    ∀ q, 1 ≤ q → q < Nat.choose 2 2 + 1 → cpq 3 q < cpq 3 (q + 1) := by
  intro q hq1 hq_lt
  have hq_eq : q = 1 := by
    have : Nat.choose 2 2 + 1 = 2 := by native_decide
    omega
  subst hq_eq
  exact p3_strict

/-
## Part VIII: The Main Conjecture (Erdos Problem 667)
-/

/-- Erdos Problem 667 (OPEN): c(p, q) is strictly increasing in q for
    1 ≤ q ≤ C(p-1, 2) + 1. -/
def ErdosProblem667 : Prop :=
    ∀ (p : ℕ) (_ : 3 ≤ p),
      ∀ (q : ℕ), 1 ≤ q → q < Nat.choose (p - 1) 2 + 1 →
        cpq p q < cpq p (q + 1)

/-- A weaker version: c(p,q) is non-constant (already known for the endpoints). -/
theorem erdos667_weak_evidence (p : ℕ) (hp : 3 ≤ p) :
    cpq p 1 < cpq p (Nat.choose (p - 1) 2 + 1) := by
  have h := cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp)
  rw [h]
  have := cpq_upper_ramsey p (le_trans (by omega : 2 ≤ 3) hp)
  have hp' : (p : ℚ) ≥ 3 := by exact_mod_cast hp
  have : (2 : ℚ) / ((p : ℚ) + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℚ) < (p : ℚ) + 1)]
    linarith
  linarith

/-
## Part IX: Structural Consequences

General results about the gap structure of c(p,q).
-/

/-- The total gap: for p ≥ 3, c(p,1) is bounded away from c(p,q_max) = 1.
    Specifically, c(p,q_max) - c(p,1) ≥ 1 - 2/(p+1). -/
theorem cpq_total_gap (p : ℕ) (hp : 3 ≤ p) :
    1 - (2 : ℚ) / ((p : ℚ) + 1) ≤
    cpq p (Nat.choose (p - 1) 2 + 1) - cpq p 1 := by
  have h1 := cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp)
  have h2 := cpq_upper_ramsey p (le_trans (by omega : 2 ≤ 3) hp)
  linarith

/-- The gap is positive: c(p,q_max) - c(p,1) > 0 for p ≥ 3. -/
theorem cpq_gap_pos (p : ℕ) (hp : 3 ≤ p) :
    (0 : ℚ) < cpq p (Nat.choose (p - 1) 2 + 1) - cpq p 1 := by
  linarith [erdos667_weak_evidence p hp]

/-- For p ≥ 3, there exists at least one strict step in c(p,·).
    The EFRS bound ensures c(p, C(p-1,2)) < c(p, C(p-1,2)+1) = 1. -/
theorem erdos667_at_least_one_strict_step (p : ℕ) (hp : 3 ≤ p) :
    ∃ q, 1 ≤ q ∧ q ≤ Nat.choose (p - 1) 2 ∧ cpq p q < cpq p (q + 1) := by
  exact ⟨Nat.choose (p - 1) 2,
    Nat.one_le_iff_ne_zero.mpr (by
      intro h
      have := Nat.choose_pos (by omega : 2 ≤ p - 1)
      simp [h] at this),
    le_refl _,
    cpq_strict_at_top p hp⟩

/-- Summary of known results for c(p,q). -/
theorem erdos667_summary (p : ℕ) (hp : 3 ≤ p) :
    -- c(p,1) is in the Ramsey interval
    ((1 : ℚ) / ((p : ℚ) - 1) ≤ cpq p 1 ∧ cpq p 1 ≤ (2 : ℚ) / ((p : ℚ) + 1)) ∧
    -- c(p,q_max) = 1
    cpq p (Nat.choose (p - 1) 2 + 1) = 1 ∧
    -- c is weakly increasing
    (∀ q, cpq p q ≤ cpq p (q + 1)) ∧
    -- There is a gap at the top
    cpq p (Nat.choose (p - 1) 2) < cpq p (Nat.choose (p - 1) 2 + 1) := by
  refine ⟨cpq_ramsey_interval p (le_trans (by omega : 2 ≤ 3) hp),
          cpq_at_max p (le_trans (by omega : 2 ≤ 3) hp),
          fun q => cpq_mono_q p q,
          cpq_strict_at_top p hp⟩

end Erdos667
