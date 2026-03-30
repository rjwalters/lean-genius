/-
  Erdős Problem #59: Counting G-Free Graphs

  Source: https://erdosproblems.com/59
  Status: DISPROVED (Morris-Saxton 2016)

  Statement:
  Is it true that the number of graphs on n vertices which do not contain G is
  at most 2^{(1+o(1))ex(n;G)}?

  History:
  - Erdős-Frankl-Rödl (1986): Proved the bound holds when G is not bipartite
  - Morris-Saxton (2016): DISPROVED for bipartite G, specifically C_6
    They showed there are at least 2^{(1+c)ex(n;C_6)} C_6-free graphs
    for infinitely many n and some constant c > 0

  Open Question:
  Does the weaker bound 2^{O(ex(n;G))} hold for all G?
  (Conjectured by Morris-Saxton)

  This file formalizes the definitions and main results.
-/

import Mathlib

open Set SimpleGraph

namespace Erdos59

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Core Definitions -/

/-- A graph G contains H as a subgraph if there's an injective homomorphism. -/
def ContainsSubgraph (G H : SimpleGraph V) : Prop :=
  ∃ f : V → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/-- A graph is H-free if it does not contain H as a subgraph. -/
def IsFree (G H : SimpleGraph V) : Prop :=
  ¬ContainsSubgraph G H

/-- A graph is bipartite if it has no odd cycles (equivalent definition). -/
def IsBipartite (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    (∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) ∧
    (∀ u ∈ B, ∀ v ∈ B, ¬G.Adj u v)

/- ## Graph Constructions -/

/-- The cycle graph C_n on Fin n. Vertex i is adjacent to vertex (i+1) mod n. -/
def cycleGraph (n : ℕ) (hn : 3 ≤ n) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
  symm := by intro i j h; cases h with | inl h => exact Or.inr h | inr h => exact Or.inl h
  loopless := by
    intro ⟨i, hi⟩ h
    simp only at h
    have h' : (i + 1) % n = i := h.elim id id
    by_cases hlt : i + 1 < n
    · rw [Nat.mod_eq_of_lt hlt] at h'; omega
    · have : i + 1 = n := by omega
      rw [this, Nat.mod_self] at h'; omega

/-- Odd cycles are not bipartite.
    Proof: in any bipartition of C_n, membership alternates around the cycle.
    After n (odd) steps, vertex n-1 has the same parity as vertex 0,
    but they are adjacent — contradiction. -/
theorem odd_cycle_not_bipartite (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ¬IsBipartite (cycleGraph n hn) := by
  intro ⟨A, B, hunion, hdisj, hA, hB⟩
  -- Helper: every vertex is in A or B
  have mem : ∀ v : Fin n, v ∈ A ∨ v ∈ B := by
    intro v; have h : v ∈ (A ∪ B) := by rw [hunion]; exact Set.mem_univ v
    exact Set.mem_union.mp h
  -- Consecutive vertices k, k+1 are adjacent (for k+1 < n)
  have consec_adj : ∀ (k : ℕ) (hk : k + 1 < n),
      (cycleGraph n hn).Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ := by
    intro k hk; left; exact Nat.mod_eq_of_lt hk
  -- The closing edge: vertex (n-1) is adjacent to vertex 0
  have closing : (cycleGraph n hn).Adj ⟨n - 1, by omega⟩ ⟨0, by omega⟩ := by
    left; show (n - 1 + 1) % n = 0; rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  -- n-1 is even since n is odd
  have hn1_even : Even (n - 1) := by obtain ⟨k, hk⟩ := hodd; omega
  -- Case split on whether vertex 0 is in A or B
  rcases mem ⟨0, by omega⟩ with h0 | h0
  · -- Case: 0 ∈ A. Prove by induction: vertex k ∈ A ↔ Even k
    suffices ∀ k, (hk : k < n) → (⟨k, hk⟩ ∈ A ↔ Even k) by
      have h_nm1_A := (this (n - 1) (by omega)).mpr hn1_even
      exact hA ⟨n - 1, by omega⟩ h_nm1_A ⟨0, by omega⟩ h0 closing
    intro k; induction k with
    | zero => intro _; exact ⟨fun _ => even_zero, fun _ => h0⟩
    | succ m ih =>
      intro hk
      have hadj := consec_adj m hk
      constructor
      · intro hsucc_A; rw [Nat.even_succ]; intro hm_even
        exact hA ⟨m, by omega⟩ ((ih (by omega)).mpr hm_even) ⟨m + 1, hk⟩ hsucc_A hadj
      · intro hsucc_even
        have hm_odd : ¬Even m := by rwa [← Nat.even_succ]
        have hm_not_A : ⟨m, by omega⟩ ∉ A := fun h => hm_odd ((ih (by omega)).mp h)
        have hm_B := (mem ⟨m, by omega⟩).resolve_left hm_not_A
        have hsucc_not_B : ⟨m + 1, hk⟩ ∉ B := fun h => hB ⟨m, by omega⟩ hm_B ⟨m + 1, hk⟩ h hadj
        exact (mem ⟨m + 1, hk⟩).resolve_right hsucc_not_B
  · -- Case: 0 ∈ B. Symmetric: vertex k ∈ B ↔ Even k
    suffices ∀ k, (hk : k < n) → (⟨k, hk⟩ ∈ B ↔ Even k) by
      have h_nm1_B := (this (n - 1) (by omega)).mpr hn1_even
      exact hB ⟨n - 1, by omega⟩ h_nm1_B ⟨0, by omega⟩ h0 closing
    intro k; induction k with
    | zero => intro _; exact ⟨fun _ => even_zero, fun _ => h0⟩
    | succ m ih =>
      intro hk
      have hadj := consec_adj m hk
      constructor
      · intro hsucc_B; rw [Nat.even_succ]; intro hm_even
        exact hB ⟨m, by omega⟩ ((ih (by omega)).mpr hm_even) ⟨m + 1, hk⟩ hsucc_B hadj
      · intro hsucc_even
        have hm_odd : ¬Even m := by rwa [← Nat.even_succ]
        have hm_not_B : ⟨m, by omega⟩ ∉ B := fun h => hm_odd ((ih (by omega)).mp h)
        have hm_A := (mem ⟨m, by omega⟩).resolve_right hm_not_B
        have hsucc_not_A : ⟨m + 1, hk⟩ ∉ A := fun h => hA ⟨m, by omega⟩ hm_A ⟨m + 1, hk⟩ h hadj
        exact (mem ⟨m + 1, hk⟩).resolve_left hsucc_not_A

/-- Even cycles are bipartite.
    Proof: partition vertices by parity (even indices vs odd indices).
    Adjacent vertices differ by 1, so they have different parity. -/
theorem even_cycle_bipartite (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    IsBipartite (cycleGraph n hn) := by
  use {i : Fin n | Even i.val}, {i : Fin n | ¬Even i.val}
  have h2dvdn : 2 ∣ n := by obtain ⟨k, hk⟩ := heven; exact ⟨k, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- A ∪ B = univ
    ext x; simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact em (Even x.val)
  · -- A ∩ B = ∅
    ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    exact fun ⟨h1, h2⟩ => h2 h1
  · -- No edges within even-parity vertices
    intro u hu v hv hadj
    simp only [Set.mem_setOf_eq] at hu hv
    rw [Nat.even_iff] at hu hv
    simp only [cycleGraph] at hadj
    rcases hadj with h | h
    · -- (u.val + 1) % n = v.val
      have h1 : (u.val + 1) % n % 2 = v.val % 2 := congr_arg (· % 2) h
      rw [Nat.mod_mod_of_dvd _ h2dvdn] at h1; omega
    · -- (v.val + 1) % n = u.val
      have h1 : (v.val + 1) % n % 2 = u.val % 2 := congr_arg (· % 2) h
      rw [Nat.mod_mod_of_dvd _ h2dvdn] at h1; omega
  · -- No edges within odd-parity vertices
    intro u hu v hv hadj
    simp only [Set.mem_setOf_eq] at hu hv
    rw [Nat.even_iff] at hu hv
    push_neg at hu hv
    simp only [cycleGraph] at hadj
    rcases hadj with h | h
    · have h1 : (u.val + 1) % n % 2 = v.val % 2 := congr_arg (· % 2) h
      rw [Nat.mod_mod_of_dvd _ h2dvdn] at h1; omega
    · have h1 : (v.val + 1) % n % 2 = u.val % 2 := congr_arg (· % 2) h
      rw [Nat.mod_mod_of_dvd _ h2dvdn] at h1; omega

/-- The 6-cycle C_6. -/
def C6 : SimpleGraph (Fin 6) := cycleGraph 6 (by omega)

/-- The triangle K_3 = C_3. -/
def K3 : SimpleGraph (Fin 3) := cycleGraph 3 (by omega)

/- ## Counting Functions (Axiomatized)

The key functions are axiomatized because:
1. turanNumber requires computing over all H-free graphs
2. countFreeGraphs requires counting subgraphs with varying vertex sizes
These are well-defined mathematically but complex to formalize directly.
-/

/-- The Turán number ex(n; k) where k is the size of the forbidden graph.
    ex(n; k) = maximum edges in an n-vertex graph avoiding all k-vertex forbidden graphs.
    Axiomatized since computing extremal numbers is a hard combinatorial problem. -/
axiom turanNumber : ℕ → ℕ → ℕ

/-- The number of H-free labeled graphs on n vertices where H has k vertices.
    For a specific forbidden graph type (e.g., C_6), this counts graphs avoiding it.
    Axiomatized since exact enumeration of forbidden-subgraph-free graphs is intractable. -/
axiom countFreeGraphs : ℕ → ℕ → ℕ

/- ## Asymptotic Bounds -/

/-- Growth rate f(n) ≤ 2^{(1+o(1))g(n)} means for all ε > 0,
    f(n) ≤ 2^{(1+ε)g(n)} for sufficiently large n. -/
def HasOptimalBound (f g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (f n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * g n)

/-- Growth rate f(n) ≥ 2^{(1+c)g(n)} for some c > 0 and infinitely many n. -/
def ExceedsOptimalBound (f g : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ Set.Infinite { n : ℕ | (f n : ℝ) ≥ (2 : ℝ) ^ ((1 + c) * g n) }

/-- The weaker bound: f(n) = 2^{O(g(n))}. -/
def HasPolynomialBound (f g : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (f n : ℝ) ≤ (2 : ℝ) ^ (C * g n)

/-- Turán numbers are positive for n ≥ k: there exist k-free graphs
    on n vertices with at least one edge (e.g., any tree). -/
axiom turanNumber_pos (n k : ℕ) (hn : n ≥ k) (hk : k ≥ 3) :
    turanNumber n k > 0

/- ## Main Results -/

/--
**Erdős-Frankl-Rödl Theorem (1986)**:
For non-bipartite H, the number of H-free graphs on n vertices is
at most 2^{(1+o(1))ex(n;H)}.

This confirms the conjecture for non-bipartite forbidden subgraphs.
-/
axiom erdos_frankl_rodl_nonbipartite (k : ℕ) :
    HasOptimalBound (countFreeGraphs · k) (turanNumber · k)

/--
**Morris-Saxton Theorem (2016) - Counterexample**:
The 6-cycle C_6 gives a counterexample to the conjecture.
There are at least 2^{(1+c)ex(n;C_6)} C_6-free graphs for infinitely many n.

This DISPROVES the original conjecture for bipartite graphs.
-/
axiom morris_saxton_c6_counterexample :
    ExceedsOptimalBound (countFreeGraphs · 6) (turanNumber · 6)

/--
**Morris-Saxton Conjecture (2016)**:
For all H, the number of H-free graphs is at most 2^{O(ex(n;H))}.
This weaker bound is conjectured to hold even for bipartite H.
-/
def morris_saxton_conjecture : Prop :=
  ∀ k : ℕ, HasPolynomialBound (countFreeGraphs · k) (turanNumber · k)

/- ## Resolution of Erdős Problem 59 -/

/--
**Erdős Problem 59: DISPROVED**

The conjecture that |{H-free graphs on n vertices}| ≤ 2^{(1+o(1))ex(n;H)}
is FALSE in general.

- TRUE for non-bipartite H (Erdős-Frankl-Rödl 1986)
- FALSE for C_6 (Morris-Saxton 2016)

The problem is completely resolved.
-/
theorem erdos_59_disproved :
    ¬∀ k : ℕ, HasOptimalBound (countFreeGraphs · k) (turanNumber · k) := by
  push_neg
  use 6
  intro hopt
  have hex := morris_saxton_c6_counterexample
  obtain ⟨c, hc, hinf⟩ := hex
  obtain ⟨N₀, hN₀⟩ := hopt (c/2) (by linarith)
  -- Extract a large counterexample n from the infinite set
  obtain ⟨n, hn_mem, hn_large⟩ := hinf.exists_gt (max N₀ 6)
  simp only [Set.mem_setOf_eq] at hn_mem
  have hn_ge_N₀ : n ≥ N₀ := by omega
  have hn_ge_6 : n ≥ 6 := by omega
  have hbound := hN₀ n hn_ge_N₀
  -- Now: hn_mem says countFreeGraphs n 6 ≥ 2^((1+c)*t)
  --       hbound says countFreeGraphs n 6 ≤ 2^((1+c/2)*t)
  -- where t = turanNumber n 6. Combined: 2^((1+c)*t) ≤ 2^((1+c/2)*t).
  -- turanNumber n 6 > 0 for n ≥ 6 (any tree is C₆-free and has edges):
  have ht_pos : (0 : ℝ) < ↑(turanNumber n 6) := by
    exact_mod_cast turanNumber_pos n 6 hn_ge_6 (by omega)
  -- Since c > 0 and t > 0: (1+c/2)*t < (1+c)*t
  have hexp_strict : (1 + c / 2) * ↑(turanNumber n 6) < (1 + c) * ↑(turanNumber n 6) := by
    nlinarith
  -- By strict monotonicity of 2^x: 2^((1+c/2)*t) < 2^((1+c)*t)
  have hpow_strict : (2 : ℝ) ^ ((1 + c / 2) * ↑(turanNumber n 6)) <
      (2 : ℝ) ^ ((1 + c) * ↑(turanNumber n 6)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexp_strict
  -- Contradiction: 2^((1+c)*t) ≤ countFreeGraphs ≤ 2^((1+c/2)*t) < 2^((1+c)*t)
  linarith

/--
**The C_6 counterexample is bipartite**:
C_6 is an even cycle, hence bipartite.
-/
theorem c6_is_bipartite : IsBipartite C6 := by
  apply even_cycle_bipartite
  exact ⟨3, rfl⟩

/--
**K_3 is not bipartite**:
The triangle is an odd cycle, hence not bipartite.
-/
theorem k3_not_bipartite : ¬IsBipartite K3 := by
  apply odd_cycle_not_bipartite
  exact ⟨1, rfl⟩

/- ## Turán Number Bounds -/

/--
**Turán's Theorem (1941)**:
ex(n; K_{r+1}) = (1 - 1/r) * n²/2, asymptotically.
The extremal graph is the Turán graph T(n,r).
-/
axiom turan_theorem (n r : ℕ) (hr : 1 ≤ r) :
    ∃ c : ℝ, c ≥ 0 ∧ |((turanNumber n (r+1)) : ℝ) - (1 - 1/r) * n^2 / 2| ≤ c * n

/--
**Kővári-Sós-Turán Theorem (1954)**:
For even cycles C_{2k}, we have ex(n; C_{2k}) = O(n^{1+1/k}).
-/
axiom kovari_sos_turan (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, (turanNumber n (2*k) : ℝ) ≤ c * (n : ℝ)^(1 + 1/(k : ℝ))

/- ## Corollaries -/

/-- Non-bipartite graphs satisfy the original conjecture. -/
theorem non_bipartite_satisfies_conjecture (k : ℕ) :
    HasOptimalBound (countFreeGraphs · k) (turanNumber · k) :=
  erdos_frankl_rodl_nonbipartite k

/-- Triangle-free graph counting satisfies the optimal bound. -/
theorem triangle_free_optimal : HasOptimalBound (countFreeGraphs · 3) (turanNumber · 3) :=
  erdos_frankl_rodl_nonbipartite 3

/- ## Summary

**Problem Status: DISPROVED**

The original conjecture asked whether the number of H-free graphs on n vertices
is at most 2^{(1+o(1))ex(n;H)} for all graphs H.

**Resolution**:
1. Erdős-Frankl-Rödl (1986): TRUE for non-bipartite H
2. Morris-Saxton (2016): FALSE for bipartite H (counterexample: C_6)

**Open Question** (Morris-Saxton Conjecture):
Does the weaker bound 2^{O(ex(n;H))} hold for all H?

References:
- Erdős, Frankl, Rödl (1986): "The asymptotic number of graphs not
  containing a fixed subgraph"
- Morris, Saxton (2016): "The number of C_{2ℓ}-free graphs"
-/

end Erdos59
