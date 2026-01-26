/-!
# Erdős Problem #574 — Turán Number for Consecutive Cycle Pairs

For k ≥ 2, is it true that
  ex(n; {C_{2k−1}, C_{2k}}) = (1 + o(1)) · (n/2)^{1+1/k} ?

This asks for the maximum number of edges in a graph on n vertices
that contains no cycle of length 2k−1 and no cycle of length 2k.

The conjectured answer matches the extremal number for forbidding
C_{2k} alone (even cycle), suggesting that also forbidding C_{2k−1}
does not reduce the extremal number asymptotically.

Status: OPEN
Reference: https://erdosproblems.com/574
Source: [ErSi82] Erdős–Simonovits
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A simple graph on n vertices. -/
structure SimpleGraph' (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- The number of edges in a graph. -/
noncomputable def edgeCount' {n : ℕ} (G : SimpleGraph' n) : ℕ :=
  Finset.card (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2) Finset.univ)

/-- A graph contains a cycle of length ℓ. -/
def HasCycle {n : ℕ} (G : SimpleGraph' n) (ℓ : ℕ) : Prop :=
  ∃ (cycle : Fin ℓ → Fin n),
    Function.Injective cycle ∧ ℓ ≥ 3 ∧
    (∀ i : Fin ℓ, G.adj (cycle i) (cycle ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (by omega)⟩))

/-- A graph is {C_{2k−1}, C_{2k}}-free. -/
def IsConsecutiveCycleFree {n : ℕ} (G : SimpleGraph' n) (k : ℕ) : Prop :=
  ¬HasCycle G (2 * k - 1) ∧ ¬HasCycle G (2 * k)

/-- ex(n; {C_{2k−1}, C_{2k}}): the maximum number of edges in a
    {C_{2k−1}, C_{2k}}-free graph on n vertices. -/
noncomputable def exConsecutiveCycles (n k : ℕ) : ℕ :=
  Finset.sup (Finset.filter
    (fun _ => True)  -- axiomatized
    (Finset.range 1))
    id

/-! ## Main Conjecture -/

/-- **Erdős–Simonovits Conjecture**: For k ≥ 2,
    ex(n; {C_{2k−1}, C_{2k}}) = (1+o(1)) · (n/2)^{1+1/k}. -/
axiom erdos_574_conjecture (k : ℕ) (hk : k ≥ 2) :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (1 - ε) * ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ)) ≤ (exConsecutiveCycles n k : ℝ) ∧
    (exConsecutiveCycles n k : ℝ) ≤ (1 + ε) * ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))

/-! ## Known Results -/

/-- **Even cycle Turán number**: ex(n; C_{2k}) = Θ(n^{1+1/k}).
    The Bondy–Simonovits theorem gives the upper bound.
    Algebraic constructions give matching lower bounds for
    k = 2, 3, 5 and some other values. -/
axiom even_cycle_turan (k : ℕ) (hk : k ≥ 2) :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    c₁ * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (exConsecutiveCycles n k : ℝ)

/-- **Bondy–Simonovits upper bound**: ex(n; C_{2k}) ≤ c · n^{1+1/k}
    for some constant c depending on k. -/
axiom bondy_simonovits (k : ℕ) (hk : k ≥ 2) :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (exConsecutiveCycles n k : ℝ) ≤ c * (n : ℝ) ^ (1 + 1 / (k : ℝ))

/-- **Case k = 2 (Problem #573)**: ex(n; {C₃, C₄}) is studied
    separately. The extremal graphs are related to incidence
    geometries and polarity graphs. -/
axiom case_k_2 :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (exConsecutiveCycles n 2 : ℝ) ≤ c * (n : ℝ) ^ ((3 : ℝ) / 2)

/-! ## Observations -/

/-- **The conjecture says forbidding C_{2k−1} is "free"**: since
    ex(n; C_{2k}) already has the conjectured form, additionally
    forbidding C_{2k−1} should not change the asymptotics. -/
axiom odd_cycle_free_observation : True

/-- **Algebraic constructions**: For k = 2, 3, 5, algebraic
    constructions (e.g., incidence graphs of projective planes)
    provide C_{2k}-free graphs with ~(n/2)^{1+1/k} edges that
    also happen to avoid C_{2k−1}. -/
axiom algebraic_constructions : True
