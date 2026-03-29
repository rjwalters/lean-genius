/-
  Aristotle targets for Erdős Problem #895
  Routine supporting lemmas for automated proof search.
  See Erdos895Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjecture (Barber's theorem on independent additive triples)
  - NOT the counterexample construction (n=17, requires SAT-like reasoning)
  - Routine graph theory and combinatorics from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos895Aristotle

open Finset SimpleGraph

/-
  Routine: Mantel's theorem — a triangle-free graph on n vertices
  has at most n^2/4 edges. This is a classical result (1907).
  Mathlib has SimpleGraph.IsCliqueFree and edge counting machinery.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Routine: Triangle-free implies no 3-clique
theorem triangleFree_isCliqueFree_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) : ∀ (s : Finset V), s.card = 3 → ¬G.IsClique s := by
  intro s hs hcl
  exact hG s hs hcl

-- Routine: In a triangle-free graph, the neighborhood of any vertex is independent
-- This is a fundamental graph theory fact: if N(v) had an edge {a,b},
-- then {v, a, b} would form a triangle.
theorem triangleFree_neighborhood_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    ∀ a b : V, G.Adj v a → G.Adj v b → a ≠ b → ¬G.Adj a b := by
  intro a b hva hvb hab hfab
  -- {v, a, b} forms a triangle, contradicting CliqueFree 3
  apply hG {v, a, b}
  · -- card = 3
    rw [Finset.card_insert_of_not_mem (by simp [G.ne_of_adj hva, hab]),
        Finset.card_insert_of_not_mem (by simp [hab]),
        Finset.card_singleton]
  · -- is clique
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | exact hva | exact hva.symm |
              exact hvb | exact hvb.symm | exact hfab | exact hfab.symm

-- Routine: A sum-free set in {1,...,n} has size at most n/2
-- The odd numbers form a sum-free set of size ⌈n/2⌉, and this is optimal.
theorem sumFree_card_bound (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n + 1))
    (hpos : ∀ x ∈ S, x > 0)
    (hsf : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    S.card ≤ (n + 1) / 2 := by
  sorry

-- Routine: The set of odd numbers in {1,...,n} is sum-free
-- Because odd + odd = even, and all elements are odd.
theorem odd_set_sumFree (n : ℕ) :
    let S := (Finset.range (n + 1)).filter (fun x => x > 0 ∧ x % 2 = 1)
    ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S := by
  intro S a ha b hb
  simp only [S, Finset.mem_filter, Finset.mem_range] at ha hb ⊢
  intro ⟨_, ⟨_, hmod⟩⟩
  omega

-- Routine: Cardinality of odd numbers in {1,...,n}
-- There are ⌈n/2⌉ odd numbers in {1,...,n}.
theorem odd_count_in_range (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun x => x > 0 ∧ x % 2 = 1)).card = (n + 1) / 2 := by
  -- Bijection: positive odd x ↦ (x-1)/2 maps into [0, (n+1)/2), injectively
  set S := (Finset.range (n + 1)).filter (fun x => x > 0 ∧ x % 2 = 1)
  apply le_antisymm
  · -- ≤: inject into [0, (n+1)/2)
    calc S.card
      = (S.image (fun x => (x - 1) / 2)).card := by
          apply (Finset.card_image_of_injOn _).symm
          intro a ha b hb hab
          simp only [S, Finset.mem_filter, Finset.mem_range] at ha hb; omega
      _ ≤ (Finset.range ((n + 1) / 2)).card := by
          apply Finset.card_le_card; intro k hk
          simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_range] at hk ⊢
          obtain ⟨x, ⟨_, _, _⟩, rfl⟩ := hk; omega
      _ = (n + 1) / 2 := Finset.card_range _
  · -- ≥: inject [0, (n+1)/2) into S via k ↦ 2k+1
    calc (n + 1) / 2
      = (Finset.range ((n + 1) / 2)).card := (Finset.card_range _).symm
      _ = ((Finset.range ((n + 1) / 2)).image (fun k => 2 * k + 1)).card := by
          apply (Finset.card_image_of_injOn _).symm
          intro a _ b _ hab; omega
      _ ≤ S.card := by
          apply Finset.card_le_card; intro x hx
          simp only [Finset.mem_image, Finset.mem_range, S, Finset.mem_filter] at hx ⊢
          obtain ⟨k, hk, rfl⟩ := hx; omega

-- Routine: If a, b, a+b are all in {0,...,n-1} then a+b < n
-- Simple arithmetic used in Fin-based additive triple definitions.
theorem additive_triple_bound (n : ℕ) (a b : ℕ) (ha : a < n) (hb : b < n)
    (hab : a + b < n) (hpa : a > 0) (hpb : b > 0) :
    a + b > 0 ∧ a + b < n := by
  exact ⟨by omega, hab⟩

-- Routine: Independent set in complement has clique in original
-- If S is independent in G, then S is a clique in Gᶜ.
theorem independent_is_complement_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hind : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬G.Adj a b) :
    Gᶜ.IsClique (S : Set V) := by
  intro a ha b hb hab
  simp only [SimpleGraph.compl_adj]
  exact ⟨hab, hind a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab⟩

-- Routine: Schur's theorem for 2 colors — S(2) = 4
-- Any 2-coloring of {1,2,3,4,5} contains a monochromatic Schur triple.
-- This is a finite check (decidable).
theorem schur_two_colors :
    ∀ c : Fin 5 → Fin 2,
    ∃ a b : Fin 5, a.val > 0 ∧ b.val > 0 ∧ a.val + b.val < 5 ∧
      c a = c b ∧ c a = c ⟨a.val + b.val, by omega⟩ := by
  native_decide

-- Routine: Pigeonhole — if n items are colored with k colors,
-- some color class has at least ⌈n/k⌉ items.
theorem pigeonhole_coloring (n k : ℕ) (hk : k > 0) (c : Fin n → Fin k) :
    ∃ color : Fin k, ((Finset.univ.filter (fun i => c i = color)).card : ℕ) * k ≥ n := by
  -- Pigeonhole: if ∀ color, |fiber| * k < n, then n = ∑ |fiber| < n, contradiction
  by_contra h; push_neg at h
  have h_each : ∀ color : Fin k, (Finset.univ.filter (fun i => c i = color)).card * k < n :=
    fun color => (h color)
  have h_sum : n = ∑ color : Fin k, (Finset.univ.filter (fun i => c i = color)).card := by
    rw [← Finset.card_univ (α := Fin n)]
    rw [← Finset.card_biUnion (fun i _ j _ hij => Finset.disjoint_filter.mpr
      (fun v _ h1 h2 => hij (h1 ▸ h2)))]
    congr 1; ext i; simp
  have h_bound : (∑ color : Fin k, (Finset.univ.filter (fun i => c i = color)).card) * k < n * k := by
    rw [Finset.sum_mul]
    calc ∑ color ∈ Finset.univ, (Finset.univ.filter (fun i => c i = color)).card * k
      < ∑ _ ∈ (Finset.univ : Finset (Fin k)), n :=
        Finset.sum_lt_sum (fun color _ => le_of_lt (h_each color))
          ⟨⟨0, hk⟩, Finset.mem_univ _, h_each ⟨0, hk⟩⟩
      _ = n * k := by simp [Finset.card_fin]
  linarith [h_sum]

end Erdos895Aristotle
