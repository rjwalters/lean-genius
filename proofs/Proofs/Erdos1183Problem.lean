/-
# Erdős Problem #1183 — Monochromatic Union/Intersection-Closed Families

A problem of Erdős and Ulam [Er78, p.39].

**Definition f(n):** Let f(n) be the maximum integer such that in any 2-coloring
of the subsets of {1,…,n} there is always a monochromatic family of at least f(n)
sets which is closed under taking unions and intersections.

**Definition F(n):** Let F(n) be defined similarly, except that we only require
the family be closed under taking unions.

**Questions:**
1. Estimate f(n). It is trivially at least ⌈(n+1)/2⌉ via nested chains.
2. Estimate F(n). Is it true that F(n) ≥ n^{ω(n)} for some ω(n) → ∞,
   and F(n) < (1+o(1))^n?

**Known Results:**
- f(n) ≥ ⌈(n+1)/2⌉ (trivial, from chains in the powerset lattice).
- Howorka proved F(n) > n^{ω(n)} when the coloring assigns the same
  color to all subsets of the same size (referenced without proof in [Er78]).

**Status: OPEN.**

Reference: [Er78, p.39], https://erdosproblems.com/1183
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace Erdos1183

open Finset

/-! ## Part I: Basic Definitions -/

/-- A 2-coloring of all subsets of Fin n. -/
def SubsetColoring (n : ℕ) := Finset (Fin n) → Fin 2

/-- A family of finite subsets is union-closed. -/
def IsUnionClosed {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- A family of finite subsets is intersection-closed. -/
def IsInterClosed {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F

/-- A family is a sublattice: closed under union and intersection. -/
def IsSublattice {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  IsUnionClosed F ∧ IsInterClosed F

/-- A family is monochromatic under a coloring. -/
def IsMonochromatic {n : ℕ} (χ : SubsetColoring n)
    (F : Finset (Finset (Fin n))) (c : Fin 2) : Prop :=
  ∀ A ∈ F, χ A = c

/-- A chain: any two elements are comparable by ⊆. -/
def IsChain {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A

/-! ## Part II: Chains Are Sublattices -/

/-- In a chain, union of two elements equals the larger one. -/
theorem chain_union_mem {n : ℕ} {F : Finset (Finset (Fin n))} (hF : IsChain F)
    {A B : Finset (Fin n)} (hA : A ∈ F) (hB : B ∈ F) :
    A ∪ B ∈ F := by
  rcases hF A hA B hB with h | h
  · rwa [Finset.union_eq_right.mpr h]
  · rwa [Finset.union_eq_left.mpr h]

/-- In a chain, intersection of two elements equals the smaller one. -/
theorem chain_inter_mem {n : ℕ} {F : Finset (Finset (Fin n))} (hF : IsChain F)
    {A B : Finset (Fin n)} (hA : A ∈ F) (hB : B ∈ F) :
    A ∩ B ∈ F := by
  rcases hF A hA B hB with h | h
  · rwa [Finset.inter_eq_left.mpr h]
  · rwa [Finset.inter_eq_right.mpr h]

/-- Every chain is a sublattice. -/
theorem chain_isSublattice {n : ℕ} {F : Finset (Finset (Fin n))} (hF : IsChain F) :
    IsSublattice F :=
  ⟨fun A hA B hB => chain_union_mem hF hA hB,
   fun A hA B hB => chain_inter_mem hF hA hB⟩

/-! ## Part III: The Standard Chain -/

/-- The initial segment: {i ∈ Fin n | i < k} for k : Fin (n + 1). -/
def initialSeg (n : ℕ) (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k.val)

/-- Initial segments are nested: j ≤ k implies initialSeg j ⊆ initialSeg k. -/
theorem initialSeg_mono {n : ℕ} {j k : Fin (n + 1)} (h : j ≤ k) :
    initialSeg n j ⊆ initialSeg n k := by
  intro x hx
  simp only [initialSeg, Finset.mem_filter, Finset.mem_univ, true_and] at *
  omega

/-- The standard chain: image of initialSeg over Fin (n + 1). -/
def stdChain (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.image (initialSeg n)

/-- The standard chain is a chain. -/
theorem stdChain_isChain (n : ℕ) : IsChain (stdChain n) := by
  intro A hA B hB
  simp only [stdChain, Finset.mem_image, Finset.mem_univ, true_and] at hA hB
  obtain ⟨j, rfl⟩ := hA
  obtain ⟨k, rfl⟩ := hB
  rcases le_or_lt j k with h | h
  · left; exact initialSeg_mono h
  · right; exact initialSeg_mono (le_of_lt h)

/-- Initial segments are injective: distinct indices give distinct sets. -/
theorem initialSeg_injective (n : ℕ) : Function.Injective (initialSeg n) := by
  intro j k hjk
  by_contra hne
  wlog h : j < k with
  | _ => exact this n k j hjk.symm (Ne.symm hne) (lt_of_le_of_ne (le_of_not_lt h) (Ne.symm hne))
  -- j < k, but initialSeg j = initialSeg k
  -- The element ⟨j.val, ...⟩ : Fin n is in initialSeg k but not initialSeg j
  have hj_lt_n : j.val < n := by omega
  have : (⟨j.val, hj_lt_n⟩ : Fin n) ∈ initialSeg n k := by
    simp only [initialSeg, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  rw [← hjk] at this
  simp only [initialSeg, Finset.mem_filter, Finset.mem_univ, true_and] at this
  omega

/-- The standard chain has exactly n+1 elements. -/
theorem stdChain_card (n : ℕ) : (stdChain n).card = n + 1 := by
  simp only [stdChain]
  rw [Finset.card_image_of_injective _ (initialSeg_injective n)]
  exact Finset.card_fin (n + 1)

/-! ## Part IV: Pigeonhole on the Chain -/

/-- In any 2-coloring of a set S, some color class has ≥ ⌈|S|/2⌉ elements. -/
theorem exists_mono_color_class {α : Type*} [DecidableEq α]
    (S : Finset α) (χ : α → Fin 2) :
    ∃ c : Fin 2, (S.filter (fun x => χ x = c)).card ≥ (S.card + 1) / 2 := by
  -- The two color classes partition S
  have hpart : (S.filter (fun x => χ x = 0)).card +
      (S.filter (fun x => χ x = 1)).card = S.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        fin_cases (χ x)
        · left; exact ⟨hx, rfl⟩
        · right; exact ⟨hx, rfl⟩
    · exact Finset.disjoint_filter.mpr (fun x _ h0 h1 => by simp_all)
  -- By pigeonhole one of them has ≥ half
  by_contra h
  push_neg at h
  have h₀ := h 0
  have h₁ := h 1
  omega

/-! ## Part V: The Main Lower Bound -/

/-- **Trivial lower bound (chain argument):** For any 2-coloring of the subsets
    of Fin n, there exists a monochromatic sublattice of size ≥ ⌈(n+1)/2⌉.

    Proof: The standard chain ∅ ⊂ {0} ⊂ {0,1} ⊂ ... ⊂ Fin n has n+1 elements.
    By pigeonhole, at least ⌈(n+1)/2⌉ share a color. Any subfamily of a chain
    is a sublattice (union = max, intersection = min under ⊆). -/
theorem erdos1183_chain_bound (n : ℕ) (χ : SubsetColoring n) :
    ∃ F : Finset (Finset (Fin n)),
      IsSublattice F ∧
      (∃ c : Fin 2, IsMonochromatic χ F c) ∧
      F.card ≥ (n + 2) / 2 := by
  obtain ⟨c, hc⟩ := exists_mono_color_class (stdChain n) χ
  refine ⟨(stdChain n).filter (fun x => χ x = c), ?_, ⟨c, ?_⟩, ?_⟩
  · -- The filtered chain is a sublattice
    apply chain_isSublattice
    intro A hA B hB
    simp only [Finset.mem_filter] at hA hB
    exact stdChain_isChain n A hA.1 B hB.1
  · -- Monochromatic
    intro A hA
    simp only [Finset.mem_filter] at hA
    exact hA.2
  · -- Size bound: ⌈(n+1)/2⌉ = (n + 2) / 2
    rw [stdChain_card] at hc
    linarith

/-- F(n) bound follows since every sublattice is union-closed. -/
theorem erdos1183_F_chain_bound (n : ℕ) (χ : SubsetColoring n) :
    ∃ F : Finset (Finset (Fin n)),
      IsUnionClosed F ∧
      (∃ c : Fin 2, IsMonochromatic χ F c) ∧
      F.card ≥ (n + 2) / 2 := by
  obtain ⟨F, ⟨hU, _⟩, hM, hS⟩ := erdos1183_chain_bound n χ
  exact ⟨F, hU, hM, hS⟩

/-! ## Part VI: Abstract Definitions and Bounds

The previous version used `sInf` for the definitions of f(n) and F(n), which gave
the infimum (= 0) of a downward-closed set. The correct definition uses `sSup`:
f(n) is the *largest* k such that every 2-coloring admits a monochromatic
sublattice of size ≥ k.
-/

/-- The set of achievable lower bounds for sublattice Ramsey numbers:
    k is achievable if EVERY 2-coloring admits a monochromatic sublattice of size ≥ k. -/
def achievableSublattice (n : ℕ) : Set ℕ :=
  { k : ℕ | ∀ (χ : SubsetColoring n),
    ∃ F : Finset (Finset (Fin n)), IsSublattice F ∧
      (∃ c : Fin 2, IsMonochromatic χ F c) ∧ F.card ≥ k }

/-- The set of achievable lower bounds for union-closed Ramsey numbers. -/
def achievableUnionClosed (n : ℕ) : Set ℕ :=
  { k : ℕ | ∀ (χ : SubsetColoring n),
    ∃ F : Finset (Finset (Fin n)), IsUnionClosed F ∧
      (∃ c : Fin 2, IsMonochromatic χ F c) ∧ F.card ≥ k }

/-- The achievable sublattice set is bounded above (any family has ≤ 2^n elements). -/
theorem achievableSublattice_bddAbove (n : ℕ) : BddAbove (achievableSublattice n) := by
  refine ⟨(Finset.univ : Finset (Finset (Fin n))).card, fun k hk => ?_⟩
  obtain ⟨F, _, _, hcard⟩ := hk (fun _ => 0)
  exact le_trans hcard (Finset.card_le_card (Finset.subset_univ F))

/-- The achievable union-closed set is bounded above. -/
theorem achievableUnionClosed_bddAbove (n : ℕ) : BddAbove (achievableUnionClosed n) := by
  refine ⟨(Finset.univ : Finset (Finset (Fin n))).card, fun k hk => ?_⟩
  obtain ⟨F, _, _, hcard⟩ := hk (fun _ => 0)
  exact le_trans hcard (Finset.card_le_card (Finset.subset_univ F))

/-- f(n): the largest k such that every 2-coloring of P(Fin n) admits
    a monochromatic sublattice of size ≥ k. -/
noncomputable def erdos1183_f (n : ℕ) : ℕ :=
  sSup (achievableSublattice n)

/-- F(n): the largest k such that every 2-coloring of P(Fin n) admits
    a monochromatic union-closed family of size ≥ k. -/
noncomputable def erdos1183_F (n : ℕ) : ℕ :=
  sSup (achievableUnionClosed n)

/-- **f(n) ≥ ⌈(n+1)/2⌉** by the chain argument (Part V). -/
theorem erdos1183_f_lower_bound (n : ℕ) : erdos1183_f n ≥ (n + 2) / 2 := by
  unfold erdos1183_f
  exact le_csSup (achievableSublattice_bddAbove n) (fun χ => erdos1183_chain_bound n χ)

/-- Every achievable sublattice bound is also achievable for union-closed families,
    since every sublattice is union-closed. -/
theorem achievableSublattice_subset_unionClosed (n : ℕ) :
    achievableSublattice n ⊆ achievableUnionClosed n := by
  intro k hk χ
  obtain ⟨F, ⟨hU, _⟩, hM, hS⟩ := hk χ
  exact ⟨F, hU, hM, hS⟩

/-- F(n) ≥ f(n), since every sublattice is union-closed. -/
theorem erdos1183_F_ge_f (n : ℕ) : erdos1183_F n ≥ erdos1183_f n := by
  unfold erdos1183_f erdos1183_F
  apply csSup_le_csSup (achievableUnionClosed_bddAbove n)
  · -- achievableSublattice n is nonempty: 0 is achievable (empty family works)
    refine ⟨0, fun χ => ⟨∅, ⟨?_, ?_⟩, ⟨0, ?_⟩, Nat.zero_le _⟩⟩
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
  · exact achievableSublattice_subset_unionClosed n

/-- **Trivial upper bound:** f(n) ≤ 2^n, since any monochromatic family is a
    subset of `Finset.univ : Finset (Finset (Fin n))` of cardinality 2^n. -/
theorem erdos1183_f_upper_bound (n : ℕ) : erdos1183_f n ≤ 2 ^ n := by
  unfold erdos1183_f
  apply csSup_le
  · -- nonempty: 0 is achievable (every family has size ≥ 0)
    refine ⟨0, fun χ => ⟨∅, ⟨?_, ?_⟩, ⟨0, ?_⟩, Nat.zero_le _⟩⟩
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
  · intro k hk
    obtain ⟨F, _, _, hcard⟩ := hk (fun _ => 0)
    have h1 : F.card ≤ (Finset.univ : Finset (Finset (Fin n))).card :=
      Finset.card_le_card (Finset.subset_univ F)
    have h2 : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    omega

/-- F(n) ≤ 2^n by the same containment argument. -/
theorem erdos1183_F_upper_bound (n : ℕ) : erdos1183_F n ≤ 2 ^ n := by
  unfold erdos1183_F
  apply csSup_le
  · -- nonempty: 0 is achievable
    refine ⟨0, fun χ => ⟨∅, ?_, ⟨0, ?_⟩, Nat.zero_le _⟩⟩
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
    · intro A hA; exact absurd hA (Finset.not_mem_empty A)
  · intro k hk
    obtain ⟨F, _, _, hcard⟩ := hk (fun _ => 0)
    have h1 : F.card ≤ (Finset.univ : Finset (Finset (Fin n))).card :=
      Finset.card_le_card (Finset.subset_univ F)
    have h2 : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    omega

/-- Open conjecture: f(n) is at most linear in n. Erdős had no conjecture
    for the growth rate. Stated as a Prop (not axiom) since unresolved. -/
def erdos1183_f_growth_conjecture : Prop :=
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, erdos1183_f n ≤ C * (n + 1)

/-- Open conjecture: F(n) is superpolynomial, i.e., F(n) ≥ n^{ω(n)} with ω → ∞.
    Howorka proved this for same-size colorings [Er78]. General case open.
    Stated as a Prop (not axiom) since unresolved. -/
def erdos1183_F_superpolynomial_conjecture : Prop :=
    ∃ ω : ℕ → ℕ, (∀ M, ∃ N, ∀ n, n ≥ N → ω n ≥ M) ∧
      ∀ n : ℕ, 2 ≤ n → erdos1183_F n ≥ n ^ ω n

end Erdos1183
