/-
# Erdős Problem #574 — Turán Number for Consecutive Cycle Pairs

For k ≥ 2, is it true that
  ex(n; {C_{2k−1}, C_{2k}}) = (1 + o(1)) · (n/2)^{1+1/k} ?

This asks for the maximum number of edges in a graph on n vertices
that contains no cycle of length 2k−1 and no cycle of length 2k.

The conjectured answer matches the extremal number for forbidding
C_{2k} alone (even cycle), suggesting that also forbidding C_{2k−1}
does not reduce the extremal number asymptotically.

Status: OPEN (the matching *upper* bound is the open content, and is at
least as hard as the exact even-cycle constant ex(n; C_{2k}), itself
open for general k).

## What is proved here (unconditional, 0 axioms, 0 sorries)

The *lower-bound* half is not conjectural: the dense C_{2k}-free graphs
furnished by incidence geometry (projective planes / generalized
polygons; Wenger 1991, Lazebnik–Ustimenko–Woldar 1995) are **bipartite**,
hence contain **no odd cycle at all**, hence are automatically
C_{2k−1}-free. Forbidding the odd cycle is therefore "free" on the
lower-bound side — as a theorem, not as evidence.

This file formalizes that structural core:

* `bipartite_not_hasCycle_odd` — a bipartite graph has no cycle of any
  odd length (a 2-colouring alternates along a closed walk, so the walk
  length must be even).
* `bipartite_no_odd_consecutive` — consequently a bipartite graph
  contains no C_{2k−1}, for every k ≥ 1.
* `bipartite_evenFree_consecutiveFree` — a bipartite, C_{2k}-free graph
  is `{C_{2k−1}, C_{2k}}`-free; the even-cycle condition is the only real
  constraint. This is exactly why the lower bound for
  ex(n; {C_{2k−1}, C_{2k}}) transfers, with no loss, from ex(n; C_{2k}).

Reference: https://erdosproblems.com/574
Source: [ErSi82] Erdős–Simonovits
-/

import Mathlib

/- ## Definitions -/

/-- A simple graph on n vertices. -/
structure SimpleGraph' (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

open Classical in
/-- The number of edges in a graph. -/
noncomputable def edgeCount' {n : ℕ} (G : SimpleGraph' n) : ℕ :=
  Finset.card (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2) Finset.univ)

/-- A graph contains a cycle of length ℓ. -/
def HasCycle {n : ℕ} (G : SimpleGraph' n) (ℓ : ℕ) : Prop :=
  ∃ (cycle : Fin ℓ → Fin n),
    Function.Injective cycle ∧ ℓ ≥ 3 ∧
    (∀ i : Fin ℓ, G.adj (cycle i) (cycle ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (by have := i.isLt; omega)⟩))

/-- A graph is {C_{2k−1}, C_{2k}}-free. -/
def IsConsecutiveCycleFree {n : ℕ} (G : SimpleGraph' n) (k : ℕ) : Prop :=
  ¬HasCycle G (2 * k - 1) ∧ ¬HasCycle G (2 * k)

/-- `ex(n; {C_{2k−1}, C_{2k}})`: the maximum number of edges in a
    `{C_{2k−1}, C_{2k}}`-free graph on `n` vertices, as the supremum of the
    achievable edge counts. The defining set is bounded above by `n * n`
    (`edgeCount'_le`) and nonempty (the empty graph is cycle-free), so the
    supremum is attained. -/
noncomputable def exConsecutiveCycles (n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph' n, IsConsecutiveCycleFree G k ∧ edgeCount' G = m}

/-- A graph is **bipartite**: its vertices admit a 2-colouring with no
    monochromatic edge. -/
def IsBipartite {n : ℕ} (G : SimpleGraph' n) : Prop :=
  ∃ c : Fin n → Bool, ∀ u v, G.adj u v → c u ≠ c v

/- ## The odd-cycle constraint is free on bipartite graphs -/

/-- Iterating Boolean negation `m` times flips the bit iff `m` is odd. -/
private lemma not_iterate_eq (m : ℕ) (b : Bool) :
    (fun x => !x)^[m] b = if Even m then b else !b := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hk : Even k <;> simp [hk, Nat.even_add_one, Bool.not_not]

/-- **Bipartite graphs have no odd cycle.**

    A proper 2-colouring alternates along every closed walk, so a closed
    walk that returns to its start must have even length. Hence a
    bipartite graph contains no cycle of odd length. (Injectivity of the
    cycle is irrelevant; only the closed-walk adjacencies are used.) -/
theorem bipartite_not_hasCycle_odd {n : ℕ} (G : SimpleGraph' n)
    (hG : IsBipartite G) {ℓ : ℕ} (hodd : Odd ℓ) : ¬ HasCycle G ℓ := by
  rintro ⟨cycle, _hinj, hℓ3, hcyc⟩
  obtain ⟨c, hc⟩ := hG
  have hℓpos : 0 < ℓ := by omega
  -- the closed walk, indexed by ℕ via wrap-around
  set w : ℕ → Fin n := fun j => cycle ⟨j % ℓ, Nat.mod_lt _ hℓpos⟩ with hw
  -- consecutive walk vertices are adjacent
  have hadj : ∀ j : ℕ, G.adj (w j) (w (j + 1)) := by
    intro j
    simp only [hw]
    have h1 : (j + 1) % ℓ = (j % ℓ + 1) % ℓ := by
      rw [Nat.add_mod j 1 ℓ, Nat.mod_eq_of_lt (show 1 < ℓ by omega)]
    have key := hcyc ⟨j % ℓ, Nat.mod_lt _ hℓpos⟩
    have hfin : (⟨(j % ℓ + 1) % ℓ, Nat.mod_lt _ hℓpos⟩ : Fin ℓ)
        = ⟨(j + 1) % ℓ, Nat.mod_lt _ hℓpos⟩ := Fin.ext h1.symm
    rw [hfin] at key
    exact key
  -- the colouring flips at each step
  have hflip : ∀ j : ℕ, c (w (j + 1)) = !(c (w j)) := by
    intro j
    have hne := hc _ _ (hadj j)
    generalize c (w j) = a at hne ⊢
    generalize c (w (j + 1)) = b at hne ⊢
    cases a <;> cases b <;> simp_all
  -- closed form for the colour along the walk
  have hiter : ∀ j : ℕ, c (w j) = (fun x => !x)^[j] (c (w 0)) := by
    intro j
    induction j with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ← ih, hflip k]
  -- the walk closes up after ℓ steps
  have hclose : w ℓ = w 0 := by
    simp only [hw]
    congr 1
    apply Fin.ext
    simp [Nat.mod_self, Nat.zero_mod]
  have hnotEven : ¬ Even ℓ := by
    rw [Nat.even_iff]; rw [Nat.odd_iff] at hodd; omega
  have h0 := hiter ℓ
  rw [hclose, not_iterate_eq, if_neg hnotEven] at h0
  -- h0 : c (w 0) = !(c (w 0)), impossible
  have hbad : c (w 0) ≠ !(c (w 0)) := by
    generalize c (w 0) = b
    cases b <;> simp
  exact hbad h0

/-- **A bipartite graph contains no `C_{2k-1}`** (the odd member of the
    consecutive pair), for every `k ≥ 1`. -/
theorem bipartite_no_odd_consecutive {n : ℕ} (G : SimpleGraph' n)
    (hG : IsBipartite G) (k : ℕ) (hk : 1 ≤ k) : ¬ HasCycle G (2 * k - 1) := by
  apply bipartite_not_hasCycle_odd G hG
  exact ⟨k - 1, by omega⟩

/-- **The lower-bound transfer.** A bipartite, `C_{2k}`-free graph is
    automatically `{C_{2k-1}, C_{2k}}`-free: on bipartite witnesses, the
    even-cycle condition already implies the full consecutive-pair
    constraint. This is the structural reason the lower bound for
    `ex(n; {C_{2k-1}, C_{2k}})` matches that of `ex(n; C_{2k})` —
    forbidding the odd cycle costs nothing. -/
theorem bipartite_evenFree_consecutiveFree {n : ℕ} (G : SimpleGraph' n)
    (hG : IsBipartite G) (k : ℕ) (hk : 1 ≤ k)
    (hev : ¬ HasCycle G (2 * k)) : IsConsecutiveCycleFree G k :=
  ⟨bipartite_no_odd_consecutive G hG k hk, hev⟩

/- ## The lower-bound transfer at the level of the extremal function -/

/-- Every graph on `Fin n` has at most `n * n` edges (the edge set is a subset
    of `Fin n × Fin n`). A crude bound, but enough to make the supremum
    defining `exConsecutiveCycles` well-behaved. -/
lemma edgeCount'_le {n : ℕ} (G : SimpleGraph' n) : edgeCount' G ≤ n * n := by
  classical
  calc edgeCount' G
      ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_filter_le _ _
    _ = n * n := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- The set of edge counts achievable by `{C_{2k−1}, C_{2k}}`-free graphs is
    bounded above (by `n * n`), so `exConsecutiveCycles` is a genuine maximum. -/
lemma bddAbove_consecutiveFree_edgeCounts (n k : ℕ) :
    BddAbove {m : ℕ | ∃ G : SimpleGraph' n, IsConsecutiveCycleFree G k ∧ edgeCount' G = m} := by
  refine ⟨n * n, ?_⟩
  rintro m ⟨G, _, rfl⟩
  exact edgeCount'_le G

/-- **The extremal function dominates every admissible graph.** Any
    `{C_{2k−1}, C_{2k}}`-free graph's edge count is at most
    `exConsecutiveCycles n k`. -/
theorem edgeCount_le_exConsecutive {n k : ℕ} (G : SimpleGraph' n)
    (h : IsConsecutiveCycleFree G k) : edgeCount' G ≤ exConsecutiveCycles n k :=
  le_csSup (bddAbove_consecutiveFree_edgeCounts n k) ⟨G, h, rfl⟩

/-- **Numeric form of the lower-bound transfer.** A bipartite, `C_{2k}`-free
    graph contributes its full edge count to the extremal number
    `exConsecutiveCycles n k` — forbidding the odd cycle `C_{2k−1}` costs nothing
    even at the level of the extremal *function*, not merely cycle-freeness.
    This is the formal bridge from `ex(n; C_{2k})` lower bounds (realised by
    bipartite incidence graphs) to `ex(n; {C_{2k−1}, C_{2k}})`. -/
theorem bipartite_evenFree_le_ex {n k : ℕ} (G : SimpleGraph' n)
    (hG : IsBipartite G) (hk : 1 ≤ k) (hev : ¬ HasCycle G (2 * k)) :
    edgeCount' G ≤ exConsecutiveCycles n k :=
  edgeCount_le_exConsecutive G (bipartite_evenFree_consecutiveFree G hG k hk hev)

/- ## Main Conjecture (OPEN) -/

/- **Erdős–Simonovits Conjecture**: For k ≥ 2,
    ex(n; {C_{2k−1}, C_{2k}}) = (1+o(1)) · (n/2)^{1+1/k}.
    The matching upper bound is open. -/

/- ## Known Results -/

/- **Even cycle Turán number**: ex(n; C_{2k}) = Θ(n^{1+1/k}).
    The Bondy–Simonovits theorem gives the upper bound.
    Algebraic (bipartite) constructions give matching lower bounds for
    k = 2, 3, 5 and some other values; being bipartite, they are also
    C_{2k−1}-free — see `bipartite_evenFree_consecutiveFree`. -/

/- ## Observations -/

/- **The conjecture says forbidding C_{2k−1} is "free"**: since
    ex(n; C_{2k}) already has the conjectured form, additionally
    forbidding C_{2k−1} should not change the asymptotics. On the
    lower-bound side this is now a theorem (the bipartite witnesses have
    no odd cycle); the open content is the matching upper bound. -/
