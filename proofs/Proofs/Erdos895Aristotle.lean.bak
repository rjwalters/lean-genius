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
  have : (Finset.range (n + 1)).filter (fun x => x > 0 ∧ x % 2 = 1) =
      (Finset.range ((n + 1) / 2)).image (fun k => 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hlt, hpos, hodd⟩
      exact ⟨x / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, by omega, by omega⟩
  rw [this, Finset.card_image_of_injective _ (by intro a b h; omega), Finset.card_range]

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
  sorry

end Erdos895Aristotle
