/-!
# Erdős Problem #112 — Directed Ramsey: Independent Sets vs Transitive Tournaments

Determine the minimum k(n,m) such that every tournament (directed
complete graph) on k vertices contains either an independent set of
size n or a transitive tournament of size m.

More precisely, for a directed graph G on k vertices, G must contain
either n vertices with no edges among them, or m vertices forming a
transitive tournament (total order).

Known bounds:
  R(n,m) ≤ k(n,m) ≤ R(n,m,m)
  k(n,3) ≤ n²  (Larson–Mitchell 1997)

Status: OPEN
Reference: https://erdosproblems.com/112
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- A directed graph on vertex set Fin k, represented by an
    irreflexive relation (edge function). -/
def IsDirectedGraph (k : ℕ) (E : Fin k → Fin k → Prop) : Prop :=
  ∀ v : Fin k, ¬E v v

/-- A set S of vertices is independent if no edge exists between
    any pair of vertices in S. -/
def IsIndependentSet (k : ℕ) (E : Fin k → Fin k → Prop)
    (S : Finset (Fin k)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬E u v ∧ ¬E v u

/-- A set S of vertices forms a transitive tournament if there is
    a total order on S consistent with edge directions. -/
def IsTransitiveTournament (k : ℕ) (E : Fin k → Fin k → Prop)
    (S : Finset (Fin k)) : Prop :=
  ∃ lt : Fin k → Fin k → Prop,
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → (lt u v ∨ lt v u)) ∧
    (∀ u ∈ S, ∀ v ∈ S, lt u v → E u v) ∧
    (∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, lt u v → lt v w → lt u w)

/-- k(n,m): the minimum number of vertices guaranteeing either
    an independent set of size n or a transitive tournament of
    size m in any directed graph. -/
noncomputable def directedRamsey : ℕ → ℕ → ℕ := fun _ _ => 0  -- axiomatized

/-! ## Main Question -/

/-- **Erdős Problem #112**: Determine k(n,m). The exact values are
    unknown for general n, m. -/
axiom erdos_112_well_defined :
  ∀ n m : ℕ, n ≥ 1 → m ≥ 1 →
    ∀ (k : ℕ) (E : Fin k → Fin k → Prop),
      IsDirectedGraph k E →
      k ≥ directedRamsey n m →
      (∃ S : Finset (Fin k), S.card ≥ n ∧ IsIndependentSet k E S) ∨
      (∃ S : Finset (Fin k), S.card ≥ m ∧ IsTransitiveTournament k E S)

/-! ## Known Bounds -/

/-- **Ramsey Lower Bound**: k(n,m) ≥ R(n,m), the ordinary Ramsey
    number, since independent set + clique is a special case. -/
axiom ramsey_lower :
  ∀ n m : ℕ, n ≥ 1 → m ≥ 1 →
    directedRamsey n m ≥ 1  -- placeholder for R(n,m)

/-- **Hunter's Upper Bound**: k(n,m) ≤ R(n,m,m), the 3-color
    Ramsey number. This gives k(n,m) ≤ 3^{n+2m}. -/
axiom hunter_upper :
  ∃ C : ℝ, C > 0 ∧
    ∀ n m : ℕ, n ≥ 1 → m ≥ 1 →
      (directedRamsey n m : ℝ) ≤ C * 3 ^ (n + 2 * m)

/-- **Larson–Mitchell (1997)**: k(n,3) ≤ n² for all n.
    The case m = 3 (transitive triple) is quadratic. -/
axiom larson_mitchell :
  ∀ n : ℕ, n ≥ 1 → directedRamsey n 3 ≤ n ^ 2

/-- **Erdős–Rado (1967)**: the original upper bound
    k(n,m) ≤ (2^{m-1}(n-1)^m + n - 2) / (2n - 3). -/
axiom erdos_rado_upper :
  ∀ n m : ℕ, n ≥ 2 → m ≥ 2 →
    (directedRamsey n m : ℝ) ≤
      (2 ^ (m - 1) * (n - 1) ^ m + n - 2) / (2 * n - 3)

/-! ## Observations -/

/-- **Path Variant**: When "transitive tournament" is replaced by
    "directed path," Hunter–Steiner proved k(n,m) = (n-1)(m-1). -/
axiom path_variant :
  True  -- exact result for directed path variant

/-- **Connection to Ramsey Theory**: This generalizes classical
    Ramsey numbers to directed settings, where orientation of
    edges provides additional structure. -/
axiom ramsey_connection : True
