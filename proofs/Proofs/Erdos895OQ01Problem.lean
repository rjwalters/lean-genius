/-
  Erdős Problem #895, Open Question 1: Hajnal's Independent Hindman Set Conjecture

  Parent: erdos-895 (Erdős-Hajnal-Barber). For n ≥ 18, every triangle-free
  graph on {1,...,n} contains three mutually independent vertices a, b, a+b.

  Hajnal's Generalization (OPEN as of 2026): Every sufficiently large triangle-free
  graph on {1,...,n} contains an *independent Hindman set*: a base B ⊆ V(G)
  with |B| ≥ 2 such that all vertices whose index is a nonempty finite sub-sum
  of B are mutually non-adjacent.

  Hierarchy:
    hajnalConjecture (OPEN, this file)
      ↓ k=2 special case
    Erdős-Barber theorem (proved by Barber 2015, n ≥ 18, parent entry erdos-895)

  The k=2 base case of Hajnal IS the parent: FS({a,b}) = {a, b, a+b}, and
  independence of FS({a,b}) means a, b, a+b is an independent additive triple.

  This file proves:
  1. hindmanSet structural properties (all sorry-free)
  2. Hajnal conjecture as an axiom (OPEN)
  3. The k=2 case: Hajnal base {a,b} with a+b < n → independent additive triple
  4. Independence number lower bound α(G) ≥ √n for triangle-free graphs
     (Case 1 proved; Case 2 has one HARD sorry for greedy algorithm)
-/
import Mathlib

namespace Erdos895OQ01Problem

open Finset SimpleGraph

-- ## Core Definitions ##

abbrev GraphOnInterval (n : ℕ) := SimpleGraph (Fin n)

def IsTriangleFree {n : ℕ} (G : GraphOnInterval n) : Prop :=
  ∀ a b c : Fin n, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)

def IsAdditiveTriple {n : ℕ} (a b c : Fin n) : Prop :=
  (a.val : ℕ) + b.val = c.val ∧ a.val > 0 ∧ b.val > 0

def HasIndependentAdditiveTriple {n : ℕ} (G : GraphOnInterval n) : Prop :=
  ∃ a b c : Fin n, IsAdditiveTriple a b c ∧
    ¬G.Adj a b ∧ ¬G.Adj b c ∧ ¬G.Adj a c

/-- All finite nonempty sub-sums of a base set (Hindman's FS-set) -/
def hindmanSet (base : Finset ℕ) : Set ℕ :=
  {s : ℕ | ∃ T : Finset ℕ, T ⊆ base ∧ T.Nonempty ∧ T.sum id = s}

-- ## Section 1: Hindman Set Properties (all sorry-free) ##

/-- Every base element is in its own hindmanSet (singleton subsums) -/
theorem hindmanSet_mem_self (a : ℕ) (base : Finset ℕ) (ha : a ∈ base) :
    a ∈ hindmanSet base :=
  ⟨{a}, Finset.singleton_subset_iff.mpr ha, Finset.singleton_nonempty _, by simp⟩

/-- hindmanSet is monotone in the base -/
theorem hindmanSet_mono {base₁ base₂ : Finset ℕ} (h : base₁ ⊆ base₂) :
    hindmanSet base₁ ⊆ hindmanSet base₂ :=
  fun _ ⟨T, hT_sub, hT_ne, hT_sum⟩ => ⟨T, hT_sub.trans h, hT_ne, hT_sum⟩

/-- Left element of a 2-element base is in its hindmanSet -/
theorem hindmanSet_pair_left (a b : ℕ) : a ∈ hindmanSet ({a, b} : Finset ℕ) :=
  hindmanSet_mem_self a _ (Finset.mem_insert_self a _)

/-- Right element of a 2-element base is in its hindmanSet -/
theorem hindmanSet_pair_right (a b : ℕ) (hab : a ≠ b) : b ∈ hindmanSet ({a, b} : Finset ℕ) :=
  hindmanSet_mem_self b _ (by simp)

/-- The sum a+b is in hindmanSet({a,b}) for distinct a ≠ b -/
theorem hindmanSet_pair_sum (a b : ℕ) (hab : a ≠ b) :
    a + b ∈ hindmanSet ({a, b} : Finset ℕ) :=
  ⟨({a, b} : Finset ℕ),
   le_refl _,
   ⟨a, Finset.mem_insert_self a _⟩,
   by rw [Finset.sum_pair hab]; rfl⟩

-- ## Section 2: Hajnal Conjecture (OPEN) ##

/-- Hajnal's conjecture: every large triangle-free graph contains an independent Hindman set -/
def hajnalConjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ G : GraphOnInterval n, IsTriangleFree G →
    ∃ base : Finset (Fin n), base.card ≥ 2 ∧
      ∀ s t : Fin n,
        s.val ∈ hindmanSet (base.image (·.val)) →
        t.val ∈ hindmanSet (base.image (·.val)) →
        s ≠ t → ¬G.Adj s t

/-- Hajnal's conjecture is OPEN as of 2026 (axiomatized for structural exploration) -/
axiom hajnal_conjecture : hajnalConjecture

-- ## Section 3: The k=2 Reduction: Hajnal Base {a,b} → Independent Additive Triple ##

/-- For a Hajnal base {a, b} where a+b fits in Fin n, the three vertices
    a, b, a+b form an independent additive triple.
    This is the formal sense in which Hajnal (k=2 case) GENERALIZES Erdős-Barber. -/
theorem hajnal_k2_gives_additive_triple {n : ℕ} (G : GraphOnInterval n)
    (a b : Fin n) (hab : a ≠ b) (ha : a.val > 0) (hb : b.val > 0)
    (hsum : a.val + b.val < n)
    (hindep : ∀ s t : Fin n,
      s.val ∈ hindmanSet (({a, b} : Finset (Fin n)).image (·.val)) →
      t.val ∈ hindmanSet (({a, b} : Finset (Fin n)).image (·.val)) →
      s ≠ t → ¬G.Adj s t) :
    HasIndependentAdditiveTriple G := by
  let d : Fin n := ⟨a.val + b.val, hsum⟩
  have hadd : IsAdditiveTriple a b d := ⟨rfl, ha, hb⟩
  have hab_val : a.val ≠ b.val := Fin.val_ne_of_ne hab
  have had_val : a.val ≠ d.val := by simp [d]; omega
  have hbd_val : b.val ≠ d.val := by simp [d]; omega
  -- The image of {a,b} under (·.val) equals {a.val, b.val}
  have hbase_eq : (({a, b} : Finset (Fin n)).image (·.val)) = ({a.val, b.val} : Finset ℕ) := by
    simp [Finset.image_insert, Finset.image_singleton]
  rw [hbase_eq] at hindep
  -- Each of a, b, d has its .val in the hindmanSet
  have ha_in : a.val ∈ hindmanSet ({a.val, b.val} : Finset ℕ) := hindmanSet_pair_left _ _
  have hb_in : b.val ∈ hindmanSet ({a.val, b.val} : Finset ℕ) :=
    hindmanSet_pair_right _ _ hab_val
  have hd_in : d.val ∈ hindmanSet ({a.val, b.val} : Finset ℕ) := by
    show a.val + b.val ∈ hindmanSet ({a.val, b.val} : Finset ℕ)
    exact hindmanSet_pair_sum _ _ hab_val
  -- a ≠ d and b ≠ d (their .vals differ)
  have had : a ≠ d := by intro h; exact had_val (congr_arg Fin.val h)
  have hbd : b ≠ d := by intro h; exact hbd_val (congr_arg Fin.val h)
  -- Apply the independence condition to get all three non-adjacencies
  exact ⟨a, b, d, hadd,
    hindep a b ha_in hb_in hab,
    hindep b d hb_in hd_in hbd,
    hindep a d ha_in hd_in had⟩

-- ## Section 4: Triangle-Free Independence Bound (α(G) ≥ √n) ##

/-- In a triangle-free graph, no two distinct neighbors of the same vertex are adjacent -/
theorem triangleFree_nbhd_independent {n : ℕ} (G : GraphOnInterval n)
    (hG : IsTriangleFree G) (v u w : Fin n)
    (hvu : G.Adj v u) (hvw : G.Adj v w) : ¬G.Adj u w :=
  fun huw => hG v u w ⟨hvu, huw, hvw⟩

/-- Case 1: a high-degree vertex provides an independent set of size ≥ √n.
    In a triangle-free graph, N(v) is independent; if |N(v)| ≥ √n we are done. -/
theorem triangleFree_indep_high_deg {n : ℕ} (G : GraphOnInterval n) [DecidableRel G.Adj]
    (hG : IsTriangleFree G) (v : Fin n) (hdeg : (G.neighborFinset v).card ≥ Nat.sqrt n) :
    ∃ S : Finset (Fin n), S.card ≥ Nat.sqrt n ∧
      ∀ a b : Fin n, a ∈ S → b ∈ S → a ≠ b → ¬G.Adj a b :=
  ⟨G.neighborFinset v, hdeg, fun a b ha hb _ => by
    rw [SimpleGraph.mem_neighborFinset] at ha hb
    exact triangleFree_nbhd_independent G hG v a b ha hb⟩

/-- Greedy lower bound: if all vertices have degree ≤ Δ, then α(G) ≥ ⌈n/(Δ+1)⌉.
    Proof: pick vertex v₁, add to S, remove N[v₁] (≤ Δ+1 vertices), repeat.
    HARD sorry: requires well-founded induction on the remaining vertex set. -/
private theorem indep_from_bounded_deg {n : ℕ} (G : GraphOnInterval n) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : ∀ v : Fin n, (G.neighborFinset v).card ≤ Δ) :
    ∃ S : Finset (Fin n), n ≤ S.card * (Δ + 1) ∧
      ∀ a b : Fin n, a ∈ S → b ∈ S → a ≠ b → ¬G.Adj a b := by
  sorry  -- HARD: greedy independent set by induction on remaining vertex set

/-- Every triangle-free graph on n vertices has an independent set of size ≥ √n.
    Proof:
    • Case 1 (∃v, deg(v) ≥ √n): N(v) is independent with |N(v)| ≥ √n (proved here)
    • Case 2 (∀v, deg(v) < √n): greedy gives n ≤ |S|·√n; since (√n)² ≤ n we get |S| ≥ √n -/
theorem triangleFree_independence_bound {n : ℕ} (G : GraphOnInterval n) [DecidableRel G.Adj]
    (hG : IsTriangleFree G) :
    ∃ S : Finset (Fin n), S.card ≥ Nat.sqrt n ∧
      ∀ a b : Fin n, a ∈ S → b ∈ S → a ≠ b → ¬G.Adj a b := by
  by_cases h : ∃ v : Fin n, (G.neighborFinset v).card ≥ Nat.sqrt n
  · obtain ⟨v, hv⟩ := h
    exact triangleFree_indep_high_deg G hG v hv
  · push_neg at h
    -- All degrees < √n, hence ≤ √n - 1
    have hΔ : ∀ v : Fin n, (G.neighborFinset v).card ≤ Nat.sqrt n - 1 := by
      intro v; have hv := h v; omega
    obtain ⟨S, hS, hindep⟩ := indep_from_bounded_deg G (Nat.sqrt n - 1) hΔ
    refine ⟨S, ?_, hindep⟩
    rcases Nat.eq_zero_or_pos (Nat.sqrt n) with hk | hk
    · omega  -- √n = 0 means n = 0, trivial
    · -- hS : n ≤ S.card * (√n - 1 + 1) = S.card * √n
      have h1 : Nat.sqrt n - 1 + 1 = Nat.sqrt n := by omega
      rw [h1] at hS
      -- Nat.sqrt_le' gives (√n)^2 ≤ n, i.e. √n * √n ≤ n
      have hkk : Nat.sqrt n * Nat.sqrt n ≤ n := by
        have := Nat.sqrt_le' n; rwa [pow_two] at this
      -- √n * √n ≤ n ≤ S.card * √n  →  √n ≤ S.card
      exact Nat.le_of_mul_le_mul_right (hkk.trans hS) hk

end Erdos895OQ01Problem
