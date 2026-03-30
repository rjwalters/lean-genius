/-
Erdős Problem #1105: Anti-Ramsey Numbers for Cycles and Paths

**Problem Statement (OPEN)**

The anti-Ramsey number AR(n,G) is the maximum number of colors in an edge-coloring
of K_n that contains no rainbow copy of G (where all edges have distinct colors).

**For cycles (C_k):** Is it true that
  AR(n, C_k) = ((k-2)/2 + 1/(k-1)) * n + O(1)?

**For paths (P_k):** If n ≥ k ≥ 5, is
  AR(n, P_k) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋, ε = 1 for odd k, ε = 2 for even k?

**Known Results:**
- Erdős, Simonovits, Sós (1975): AR(n, C₃) = n - 1
- Simonovits, Sós (1984): Path formula for n ≥ ck²
- Yuan (2021): Announced proof for all n ≥ k ≥ 5

**Status:** OPEN

**Reference:** Erdős, Simonovits, Sós (1975) - foundational anti-Ramsey theory

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Finset BigOperators

namespace Erdos1105

/-
# Part 1: Basic Definitions

Define graphs, edge-colorings, and rainbow subgraphs.
-/

-- Simple graph on n vertices (labeled 0 to n-1)
abbrev SimpleGraph (n : ℕ) := Fin n → Fin n → Prop

-- Edge set of a simple graph
def EdgeSet (n : ℕ) (G : SimpleGraph n) : Set (Fin n × Fin n) :=
  {e | e.1 < e.2 ∧ G e.1 e.2}

-- Complete graph K_n
def CompleteGraph (n : ℕ) : SimpleGraph n :=
  fun i j => i ≠ j

-- Number of edges in K_n is C(n,2)
def numEdgesKn (n : ℕ) : ℕ := n.choose 2

-- An edge-coloring assigns colors to edges
def EdgeColoring (n : ℕ) (c : ℕ) := (Fin n × Fin n) → Fin c

-- Number of colors used in a coloring
noncomputable def numColors (n : ℕ) (coloring : (Fin n × Fin n) → ℕ) : ℕ :=
  (Finset.image coloring (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2))).card

/-
# Part 2: Paths and Cycles

Define the path P_k and cycle C_k on k vertices.
-/

-- Path on k vertices: edges {0,1}, {1,2}, ..., {k-2, k-1}
def PathGraph (k : ℕ) : SimpleGraph k :=
  fun i j => (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)

-- Cycle on k vertices: path plus edge {0, k-1}
def CycleGraph (k : ℕ) : SimpleGraph k :=
  fun i j => PathGraph k i j ∨ (i.val = 0 ∧ j.val = k - 1) ∨ (j.val = 0 ∧ i.val = k - 1)

-- Number of edges in path P_k
def numEdgesPath (k : ℕ) : ℕ := k - 1

-- Number of edges in cycle C_k
def numEdgesCycle (k : ℕ) : ℕ := k

/-
# Part 3: Rainbow Subgraphs

A subgraph is rainbow if all its edges have distinct colors.
-/

-- A copy of H in G is a subset of vertices isomorphic to H
structure GraphEmbedding (n k : ℕ) (H : SimpleGraph k) where
  vertices : Fin k → Fin n
  injective : Function.Injective vertices
  preserves_edges : ∀ i j, H i j → (CompleteGraph n) (vertices i) (vertices j)

-- Edges of an embedded copy
def embeddedEdges (n k : ℕ) (H : SimpleGraph k) (emb : GraphEmbedding n k H) :
    Set (Fin n × Fin n) :=
  {e | ∃ i j : Fin k, H i j ∧ i < j ∧ e = (emb.vertices i, emb.vertices j)}

-- A copy is rainbow if all edge colors are distinct
def IsRainbow (n : ℕ) (coloring : (Fin n × Fin n) → ℕ)
    (k : ℕ) (H : SimpleGraph k) (emb : GraphEmbedding n k H) : Prop :=
  ∀ e₁ e₂ : Fin k × Fin k, H e₁.1 e₁.2 → H e₂.1 e₂.2 →
    e₁ ≠ e₂ →
    coloring (emb.vertices e₁.1, emb.vertices e₁.2) ≠
    coloring (emb.vertices e₂.1, emb.vertices e₂.2)

-- A coloring avoids rainbow H if no embedded copy is rainbow
def AvoidsRainbow (n : ℕ) (coloring : (Fin n × Fin n) → ℕ)
    (k : ℕ) (H : SimpleGraph k) : Prop :=
  ∀ emb : GraphEmbedding n k H, ¬IsRainbow n coloring k H emb

/-
# Part 4: Anti-Ramsey Numbers

AR(n, G) is the max colors in a rainbow-G-free coloring of K_n.
-/

-- The anti-Ramsey number
noncomputable def antiRamsey (n k : ℕ) (H : SimpleGraph k) : ℕ :=
  sSup {c : ℕ | ∃ coloring : (Fin n × Fin n) → ℕ,
    numColors n coloring = c ∧ AvoidsRainbow n coloring k H}

-- AR(n, C_k) for cycles
noncomputable def arCycle (n k : ℕ) : ℕ := antiRamsey n k (CycleGraph k)

-- AR(n, P_k) for paths
noncomputable def arPath (n k : ℕ) : ℕ := antiRamsey n k (PathGraph k)

/-
# Part 5: The Cycle Conjecture

Conjecture: AR(n, C_k) = ((k-2)/2 + 1/(k-1)) * n + O(1)
-/

-- The conjectured coefficient for cycles
noncomputable def cycleCoeff (k : ℕ) : ℝ :=
  (k - 2 : ℝ) / 2 + 1 / (k - 1 : ℝ)

-- The cycle conjecture (asymptotic form)
def CycleConjecture : Prop :=
  ∀ k ≥ 3, ∃ C : ℝ, ∀ n : ℕ, n ≥ k →
    |((arCycle n k : ℝ) - cycleCoeff k * n)| ≤ C

-- Known: AR(n, C_3) = n - 1
axiom ar_triangle : ∀ n ≥ 3, arCycle n 3 = n - 1

-- Coefficient for k=3: (3-2)/2 + 1/(3-1) = 1/2 + 1/2 = 1
-- So AR(n, C_3) ≈ n, which matches n - 1

/-
# Part 6: The Path Conjecture

Conjecture: AR(n, P_k) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋, ε = 1 for odd k, ε = 2 for even k.
-/

-- The ℓ parameter for paths
def pathL (k : ℕ) : ℕ := (k - 1) / 2

-- The ε parameter (1 for odd k, 2 for even k)
def pathEpsilon (k : ℕ) : ℕ := if k % 2 = 1 then 1 else 2

-- First term in the path formula
def pathTerm1 (k : ℕ) : ℕ := (k - 2).choose 2 + 1

-- Second term in the path formula
def pathTerm2 (n k : ℕ) : ℕ :=
  let ℓ := pathL k
  (ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + pathEpsilon k

-- Conjectured exact formula for AR(n, P_k)
def pathFormula (n k : ℕ) : ℕ := max (pathTerm1 k) (pathTerm2 n k)

-- The path conjecture
def PathConjecture : Prop :=
  ∀ n k : ℕ, n ≥ k → k ≥ 5 → arPath n k = pathFormula n k

-- Simonovits-Sós (1984): holds for n ≥ ck²
/-
# Part 7: Lower and Upper Bounds

General bounds on anti-Ramsey numbers.
-/

-- Constant coloring uses exactly 1 color when n ≥ 2
private lemma numColors_const_one (n : ℕ) (hn : n ≥ 2) :
    numColors n (fun _ => (0 : ℕ)) = 1 := by
  unfold numColors
  set S := Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2) with hS_def
  have hne : S.Nonempty := by
    use (⟨0, by omega⟩, ⟨1, by omega⟩)
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_lt_mk]
    omega
  have himg : S.image (fun _ => (0 : ℕ)) = {0} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_singleton]
    exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨hne.choose, hne.choose_spec, h.symm⟩⟩
  rw [himg, Finset.card_singleton]

-- Constant coloring avoids rainbow for graphs with ≥ 2 directed edge pairs
private lemma const_avoids_rainbow (n k : ℕ) (H : SimpleGraph k)
    (hedge : ∃ i j : Fin k, H i j ∧ H j i ∧ i ≠ j) :
    AvoidsRainbow n (fun _ => (0 : ℕ)) k H := by
  intro emb h_rainbow
  obtain ⟨i, j, hij, hji, hne⟩ := hedge
  exact absurd rfl (h_rainbow (i, j) (j, i) hij hji (fun h => hne (congr_arg Prod.fst h)))

-- Lower bound: AR(n, H) ≥ 1 for n ≥ 2 and H with symmetric edges
-- (Eliminates oversimplified ar_lower_bound axiom which was false for n < 2)
theorem ar_lower_bound (n k : ℕ) (H : SimpleGraph k)
    (hn : n ≥ 2)
    (hedge : ∃ i j : Fin k, H i j ∧ H j i ∧ i ≠ j) :
    antiRamsey n k H ≥ 1 := by
  unfold antiRamsey
  have hmem : 1 ∈ {c : ℕ | ∃ coloring : (Fin n × Fin n) → ℕ,
    numColors n coloring = c ∧ AvoidsRainbow n coloring k H} :=
    ⟨fun _ => 0, numColors_const_one n hn, const_avoids_rainbow n k H hedge⟩
  have hbdd : BddAbove {c : ℕ | ∃ coloring : (Fin n × Fin n) → ℕ,
    numColors n coloring = c ∧ AvoidsRainbow n coloring k H} :=
    ⟨n * n, fun c ⟨coloring, hc_eq, _⟩ => by
      rw [← hc_eq]; unfold numColors
      calc (Finset.image coloring _).card
          ≤ (Finset.univ.filter _).card := Finset.card_image_le
        _ ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = n * n := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]⟩
  exact le_csSup hbdd hmem

-- Helper: n.choose 2 * 2 + n = n * n (subtraction-free form)
private lemma choose_two_add_eq (n : ℕ) : n.choose 2 * 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_mul,
        show m * 2 + m.choose 2 * 2 + (m + 1) =
             (m.choose 2 * 2 + m) + (m * 2 + 1) from by ring, ih]
    ring

-- Helper: |{(i,j) : Fin n × Fin n | i < j}| = C(n,2)
-- Proof via trichotomy: every pair is in exactly one of {i<j}, {i=j}, {i>j}
private lemma card_edges_eq_choose (n : ℕ) :
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)).card = n.choose 2 := by
  set S_lt := Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)
  set S_gt := Finset.univ.filter (fun e : Fin n × Fin n => e.2 < e.1)
  set S_eq := Finset.univ.filter (fun e : Fin n × Fin n => e.1 = e.2)
  -- Pairwise disjointness
  have hdisj_lt_eq : Disjoint S_lt S_eq := by
    rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
    simp only [S_lt, S_eq, Finset.mem_filter] at h1 h2; exact absurd h2.2 (ne_of_lt h1.2)
  have hdisj_lt_gt : Disjoint S_lt S_gt := by
    rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
    simp only [S_lt, S_gt, Finset.mem_filter] at h1 h2
    exact absurd (lt_trans h1.2 h2.2) (lt_irrefl _)
  have hdisj_eq_gt : Disjoint S_eq S_gt := by
    rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
    simp only [S_eq, S_gt, Finset.mem_filter] at h1 h2; exact absurd h1.2 (ne_of_gt h2.2)
  -- Union = Finset.univ (trichotomy)
  have hunion : S_lt ∪ S_eq ∪ S_gt = Finset.univ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, S_lt, S_eq, S_gt, Finset.mem_filter, Finset.mem_univ, true_and,
               iff_true]
    rcases lt_trichotomy a b with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  -- |S_lt| = |S_gt| via Prod.swap bijection
  have hswap : S_lt.card = S_gt.card := by
    apply Finset.card_bij (fun e _ => (e.2, e.1))
    · intro ⟨a, b⟩ ha
      simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; exact ha
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro ⟨a, b⟩ hb
      exact ⟨(b, a), by
        simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact hb, rfl⟩
  -- |S_eq| = n (diagonal)
  have hdiag : S_eq.card = n := by
    suffices h : S_eq = Finset.univ.image (fun x : Fin n => (x, x)) by
      rw [h, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_fin]
    ext ⟨a, b⟩; simp [S_eq, Finset.mem_image, Prod.mk.injEq, eq_comm]
  -- |Fin n × Fin n| = n²
  have htotal : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  -- Combine: 2 * |S_lt| + n = n * n
  have h_count : S_lt.card * 2 + n = n * n := by
    have hdisj_outer : Disjoint (S_lt ∪ S_eq) S_gt := by
      rw [Finset.disjoint_left]; intro x hx hgt
      rcases Finset.mem_union.mp hx with hlt | heq
      · exact (Finset.disjoint_left.mp hdisj_lt_gt) hlt hgt
      · exact (Finset.disjoint_left.mp hdisj_eq_gt) heq hgt
    have h3 : (S_lt ∪ S_eq ∪ S_gt).card = S_lt.card + S_eq.card + S_gt.card := by
      rw [Finset.card_union_of_disjoint hdisj_outer,
          Finset.card_union_of_disjoint hdisj_lt_eq]
    rw [hunion, htotal] at h3; linarith [hdiag, hswap]
  -- n.choose 2 * 2 + n = n * n, so S_lt.card = n.choose 2
  linarith [choose_two_add_eq n]

-- Helper: numColors ≤ numEdgesKn
private lemma numColors_le_edges (n : ℕ) (coloring : (Fin n × Fin n) → ℕ) :
    numColors n coloring ≤ numEdgesKn n := by
  unfold numColors numEdgesKn
  exact le_trans Finset.card_image_le (le_of_eq (card_edges_eq_choose n))

-- Upper bound: AR(n, G) ≤ |E(K_n)| = C(n,2)
theorem ar_upper_bound (n k : ℕ) (H : SimpleGraph k) :
    antiRamsey n k H ≤ numEdgesKn n := by
  unfold antiRamsey
  rcases Set.eq_empty_or_nonempty {c : ℕ | ∃ coloring : (Fin n × Fin n) → ℕ,
    numColors n coloring = c ∧ AvoidsRainbow n coloring k H} with h | h
  · -- Empty set: sSup ∅ = 0 ≤ numEdgesKn n
    rw [h]; simp
  · -- Nonempty: each element ≤ numEdgesKn n, so sSup ≤ numEdgesKn n
    exact csSup_le h (fun c ⟨coloring, hc, _⟩ => hc ▸ numColors_le_edges n coloring)

-- Monotonicity in n
/-
# Part 8: Connection to Turán Numbers

Anti-Ramsey numbers relate to extremal graph theory.
-/

-- Turán number ex(n, H): max edges in H-free graph on n vertices
open Classical in
noncomputable def turan (n k : ℕ) (H : SimpleGraph k) : ℕ :=
  sSup {e : ℕ | ∃ G : SimpleGraph n,
    (∀ emb : GraphEmbedding n k H, False) ∧ e = (Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2)).card}

-- AR(n, H) ≥ ex(n, H) + 1 (give H-free graph rainbow, one color for complement)
/-
# Part 9: Special Cases

Known exact values and special cases.
-/

-- AR(n, C_3) = n - 1 (Erdős-Simonovits-Sós 1975)
-- Already stated above as ar_triangle

-- AR(n, P_3) = 1 (trivial: any 2-coloring avoids rainbow path)
/-
# Part 10: Problem Status

The problem remains OPEN for general cycles and the full path range.
-/

-- The problem is open
def erdos_1105_status : String := "OPEN"

-- Main formal statement for cycles
theorem erdos_1105_cycle_statement :
    CycleConjecture ↔
    ∀ k ≥ 3, ∃ C : ℝ, ∀ n : ℕ, n ≥ k →
      |((arCycle n k : ℝ) - cycleCoeff k * n)| ≤ C := by
  rfl

-- Main formal statement for paths
theorem erdos_1105_path_statement :
    PathConjecture ↔
    ∀ n k : ℕ, n ≥ k → k ≥ 5 → arPath n k = pathFormula n k := by
  rfl

/-
# Summary

**Problem:** Determine exact formulas for anti-Ramsey numbers AR(n, C_k) and AR(n, P_k).

**Known:**
- AR(n, C_3) = n - 1 (Erdős-Simonovits-Sós 1975)
- Path formula for n ≥ ck² (Simonovits-Sós 1984)
- Yuan (2021) announced proof for all n ≥ k ≥ 5

**Open:**
- General cycle formula for all k
- Full verification of path formula

**Difficulty:** Requires careful analysis of rainbow-free colorings and extremal structures.
-/

end Erdos1105
