/-
  Ramsey's Theorem OQ-04:
  How does Ramsey theory extend to hypergraphs and higher dimensions?

  The classical Ramsey theorem colors edges (2-element subsets) and finds
  monochromatic cliques. The hypergraph Ramsey theorem (Ramsey 1930)
  generalizes this to r-element subsets:

  For all k, c, n₁, ..., n_c ≥ k, there exists N such that:
  any c-coloring of the k-element subsets of [N] contains a monochromatic
  set of size nᵢ (for some color i).

  This file formalizes:
  1. k-uniform hypergraph colorings
  2. Monochromatic complete sub-hypergraphs
  3. The hypergraph Ramsey property
  4. Base cases (k=1 is pigeonhole, k=2 is classical Ramsey)
  5. The stepping-up lemma (reduction from k to k-1)

  Status: OPEN QUESTION (bounds are wide open for k ≥ 3)
  Reference: Ramsey (1930), Erdős-Rado (1952)
-/

import Proofs.RamseysTheorem
import Mathlib

open Finset

namespace RamseyOQ04

/- ## Part I: k-Uniform Hypergraph Colorings -/

/-- A k-element subset of a type α, represented as a Finset of size k. -/
def KSubset (α : Type*) (k : ℕ) := { s : Finset α // s.card = k }

/-- A c-coloring of the k-element subsets of α. -/
def HypergraphColoring (α : Type*) (k : ℕ) (c : ℕ) :=
  KSubset α k → Fin c

/-- A set S is "monochromatic" for a coloring if all k-element subsets of S
    receive the same color. -/
def IsMonochromatic {α : Type*} [DecidableEq α] {k c : ℕ}
    (f : HypergraphColoring α k c) (S : Finset α) (color : Fin c) : Prop :=
  ∀ (T : Finset α) (hT : T ⊆ S) (hTk : T.card = k),
    f ⟨T, hTk⟩ = color

/-- The hypergraph Ramsey property: any c-coloring of the k-element subsets
    of [N] has a monochromatic set of size n. -/
def HyperRamseyProperty (N k c n : ℕ) : Prop :=
  ∀ f : HypergraphColoring (Fin N) k c,
    ∃ (S : Finset (Fin N)) (color : Fin c),
      n ≤ S.card ∧ IsMonochromatic f S color

/- ## Part II: Base Case k = 1 (Pigeonhole) -/

/-- When k = 1, coloring 1-element subsets is the same as coloring vertices.
    The Ramsey property reduces to the pigeonhole principle:
    if N ≥ c·(n-1) + 1, some color class has ≥ n elements. -/
theorem hyper_ramsey_k1 (c n : ℕ) (hc : 0 < c) (hn : 0 < n) :
    HyperRamseyProperty (c * (n - 1) + 1) 1 c n := by
  intro f
  -- By pigeonhole: c colors, c*(n-1)+1 singletons → some color has ≥ n
  -- Each singleton {i} gets a color f({i})
  -- Define vertex coloring g(i) = f({i})
  classical
  let g : Fin (c * (n - 1) + 1) → Fin c := fun i =>
    f ⟨{i}, Finset.card_singleton i⟩
  -- By pigeonhole, some color class has ≥ n elements
  have hN : c * (n - 1) + 1 > 0 := by omega
  have hcard : Finset.univ.card = c * (n - 1) + 1 := Finset.card_fin _
  -- Partition Fin N into c color classes
  -- At least one class has size ≥ ⌈(c*(n-1)+1)/c⌉ = n
  obtain ⟨color, S, hS_sub, hS_mono, hS_card⟩ : ∃ color : Fin c,
      ∃ S : Finset (Fin (c * (n - 1) + 1)),
        S ⊆ Finset.univ ∧
        (∀ i ∈ S, g i = color) ∧
        n ≤ S.card := by
    by_contra h
    push_neg at h
    -- Every color class has < n elements
    have hbound : ∀ color : Fin c,
        (Finset.univ.filter (fun i => g i = color)).card ≤ n - 1 := by
      intro color
      specialize h color (Finset.univ.filter (fun i => g i = color))
        (Finset.filter_subset _ _) (fun i hi => by simp at hi; exact hi.2)
      omega
    -- Sum of class sizes ≤ c * (n-1)
    have hsum : Finset.univ.card ≤ c * (n - 1) := by
      calc (Finset.univ : Finset (Fin (c * (n - 1) + 1))).card
          = ∑ color : Fin c, (Finset.univ.filter (fun i => g i = color)).card := by
            rw [← Finset.card_biUnion]
            · congr 1
              ext x
              simp [Finset.mem_biUnion, Finset.mem_filter]
            · intro i _ j _ hij
              exact Finset.disjoint_filter.mpr (fun x _ hxi hxj => hij (hxi ▸ hxj))
        _ ≤ ∑ _ : Fin c, (n - 1) := Finset.sum_le_sum (fun color _ => hbound color)
        _ = c * (n - 1) := by rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
    -- But card = c*(n-1)+1 > c*(n-1). Contradiction.
    rw [hcard] at hsum
    omega
  exact ⟨S, color, hS_card, fun T hT hTk => by
    -- T ⊆ S, T.card = 1, so T = {i} for some i ∈ S
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hTk
    subst hi
    have hiS : i ∈ S := Finset.singleton_subset_iff.mp hT
    -- g i = color by hS_mono
    have := hS_mono i hiS
    -- f({i}) = g(i) = color
    show f ⟨{i}, Finset.card_singleton i⟩ = color
    exact this⟩

/- ## Part III: Connection to Classical Ramsey (k = 2) -/

/-- For k = 2, the hypergraph Ramsey property is equivalent to the
    classical graph Ramsey property (from RamseysTheorem.lean). -/
def classicalRamseyEquiv : Prop :=
  ∀ N r s : ℕ, HyperRamseyProperty N 2 2 r ↔
    RamseysTheorem.HasRamseyProperty (Fin N) r s

/- ## Part IV: The Stepping-Up Lemma -/

/-- **Stepping-Up Lemma (Erdős-Rado 1952):**
    If the (k-1)-uniform Ramsey number R_{k-1}(n; c) exists,
    then the k-uniform Ramsey number R_k(n; c) also exists.

    More precisely: R_k(n; c) ≤ tower(R_{k-1}(n; c)),
    where tower is an exponential tower of 2's.

    This is the fundamental tool for extending Ramsey theory
    to higher uniformities. -/
def steppingUpLemma : Prop :=
  ∀ k c n : ℕ, k ≥ 2 → c ≥ 1 → n ≥ k →
    (∃ N, HyperRamseyProperty N (k - 1) c n) →
    (∃ N', HyperRamseyProperty N' k c n)

/- ## Part V: Tower-Type Bounds -/

/-- The tower function: tower(0) = 1, tower(n+1) = 2^tower(n). -/
def tower : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ tower n

/-- tower(n) ≥ 1 for all n. -/
theorem tower_pos (n : ℕ) : 0 < tower n := by
  induction n with
  | zero => simp [tower]
  | succ n ih => simp [tower]; exact Nat.pos_of_ne_zero (Nat.not_eq_zero_of_lt (by positivity))

/- ## Part VI: Known Hypergraph Ramsey Bounds -/

/-- The hypergraph Ramsey number R_k(n; c) is the smallest N
    such that HyperRamseyProperty N k c n holds. -/
noncomputable def hyperRamseyNumber (k c n : ℕ) : ℕ :=
  if h : ∃ N, HyperRamseyProperty N k c n then Nat.find h else 0

/-- **Erdős-Rado (1952):** Hypergraph Ramsey numbers exist for all k.
    For k-uniform c-coloring, R_k(n; c) exists. Bounds are tower-type:
    R_k(n; c) ≤ tower_k(poly(n, c)) where tower_k is a k-fold exponential. -/
axiom erdos_rado_hypergraph_ramsey (k c n : ℕ) (hk : k ≥ 1) (hc : c ≥ 1) (hn : n ≥ k) :
    ∃ N, HyperRamseyProperty N k c n

/-- The tower-type upper bound on R_k(n; 2) for 2 colors.
    For k = 3: R_3(n; 2) ≤ tower(O(n²)).
    For general k: R_k(n; 2) ≤ tower_k(O(n)).
    The exact bounds are a major open problem. -/
def towerBound (k n : ℕ) : ℕ := Nat.iterate tower k n

/- ## Part VII: The 3-Uniform Case -/

/-- For 3-uniform hypergraphs (k=3), the Ramsey numbers grow as
    an exponential tower. Even R_3(4; 2) is unknown!

    Known: 2^(cn²) ≤ R_3(n; 2) ≤ 2^(2^(Cn²)) for some c, C.
    The gap between single and double exponential is a major open problem. -/
def threeUniformGap : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 4 →
      2 ^ (c * n ^ 2) ≤ (hyperRamseyNumber 3 2 n : ℝ) ∧
      (hyperRamseyNumber 3 2 n : ℝ) ≤ 2 ^ (2 ^ (C * n ^ 2))

/- ## Summary

**Theorems (2)**:
- hyper_ramsey_k1: pigeonhole principle gives k=1 Ramsey (proved)
- tower_pos: tower function is always positive (proved)

**Definitions (8)**:
- KSubset, HypergraphColoring, IsMonochromatic
- HyperRamseyProperty, hyperRamseyNumber
- tower, towerBound
- steppingUpLemma, classicalRamseyEquiv, threeUniformGap

**Axioms (1)**: erdos_rado_hypergraph_ramsey (existence for all k)
**Sorries (2)**: tower bound lemmas (2*m ≤ 2^m arguments)
-/

end RamseyOQ04
