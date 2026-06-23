/-
Ramsey Theory for Hypergraphs and Higher Dimensions

Source: Open question from ramseys-theorem gallery proof
Status: AXIOMATIZED (1 axiom for k≥2 stepping-up, k=1 proved via pigeonhole, 0 sorries)

Extends Ramsey's theorem from 2-uniform (edges/graphs) to k-uniform hypergraphs.
The classical Ramsey theorem colors edges (2-element subsets); the hypergraph
extension colors k-element subsets.

Hypergraph Ramsey Theorem (Ramsey 1930, general form):
  For any k, r, n₁, ..., nᵣ, there exists N such that for any r-coloring
  of the k-element subsets of {1, ..., N}, there exists a color i and a
  monochromatic set of size nᵢ.

The k=2 case is the classical Ramsey theorem. The k=1 case is the pigeonhole
principle. Higher k values require significantly larger Ramsey numbers.
-/

import Mathlib

open Finset

namespace HypergraphRamsey

variable {α : Type*}

/-! ## Part I: Definitions for k-Uniform Hypergraph Coloring -/

/-- A k-element subset of a finset. -/
def kSubsets (s : Finset α) (k : ℕ) [DecidableEq α] : Finset (Finset α) :=
  s.powersetCard k

/-- An r-coloring of k-element subsets. -/
def Coloring (s : Finset α) (k : ℕ) (r : ℕ) [DecidableEq α] : Type :=
  kSubsets s k → Fin r

/-- A subset is monochromatic for a coloring if all its k-element subsets have the same color. -/
def IsMonochromatic [DecidableEq α] (s t : Finset α) (k : ℕ) (c : Coloring s k r)
    (color : Fin r) (ht : t ⊆ s) : Prop :=
  ∀ e ∈ kSubsets t k, ∀ (he : e ∈ kSubsets s k), c ⟨e, he⟩ = color

/-- The hypergraph Ramsey property: for any r-coloring of k-subsets of an N-element set,
    there exists a monochromatic subset of size n. -/
def HypergraphRamseyProperty (k r n N : ℕ) : Prop :=
  ∀ (S : Finset ℕ), S.card = N →
    ∀ (c : kSubsets S k → Fin r),
      ∃ (T : Finset ℕ) (i : Fin r), T ⊆ S ∧ T.card ≥ n ∧
        ∀ e ∈ kSubsets T k, ∀ (he : e ∈ kSubsets S k), c ⟨e, he⟩ = i

/-! ## Part II: Special Cases -/

/-- k = 1 is the pigeonhole principle: coloring singletons with r colors
    among enough elements forces some color to appear many times. -/
theorem k1_is_pigeonhole : HypergraphRamseyProperty 1 r n N →
    ∀ (S : Finset ℕ), S.card = N →
      ∀ (c : kSubsets S 1 → Fin r),
        ∃ (T : Finset ℕ) (i : Fin r), T ⊆ S ∧ T.card ≥ n ∧
          ∀ e ∈ kSubsets T 1, ∀ he, c ⟨e, he⟩ = i :=
  fun h => h

/-- k = 2 case: this is the classical Ramsey theorem.
    HypergraphRamseyProperty 2 2 n N recovers the 2-color graph Ramsey theorem. -/
theorem classical_ramsey_is_k2 (n₁ n₂ N : ℕ)
    (hN : HypergraphRamseyProperty 2 2 (max n₁ n₂) N) :
    ∀ (S : Finset ℕ), S.card = N →
      ∀ (c : kSubsets S 2 → Fin 2),
        ∃ (T : Finset ℕ), T ⊆ S ∧ T.card ≥ max n₁ n₂ ∧
          (∀ e ∈ kSubsets T 2, ∀ he, c ⟨e, he⟩ = 0) ∨
          (∀ e ∈ kSubsets T 2, ∀ he, c ⟨e, he⟩ = 1) := by
  intro S hS c
  obtain ⟨T, i, hTS, hTn, hmono⟩ := hN S hS c
  exact ⟨T, hTS, hTn, by fin_cases i <;> [left; right] <;> exact hmono⟩

/-! ## Part III: The Hypergraph Ramsey Theorem -/

/-- Helper: {x} is a 1-subset of S when x ∈ S. -/
theorem singleton_mem_kSubsets {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) :
    ({x} : Finset ℕ) ∈ kSubsets S 1 := by
  simp [kSubsets, Finset.mem_powersetCard, Finset.singleton_subset_iff, hx]

/-- The k=1 case of the hypergraph Ramsey theorem is the pigeonhole principle:
    any r-coloring of singletons from an (r·(n-1)+1)-element set has a
    monochromatic subset of size n. -/
theorem pigeonhole_ramsey (r n : ℕ) (hr : r ≥ 1) (hn : n ≥ 1) :
    HypergraphRamseyProperty 1 r n (r * (n - 1) + 1) := by
  intro S hS c
  -- Convert singleton coloring to element coloring
  let color : ℕ → Fin r := fun x =>
    if h : x ∈ S then c ⟨{x}, singleton_mem_kSubsets h⟩ else ⟨0, by omega⟩
  -- Define fibers (color classes)
  let fiber := fun (i : Fin r) => S.filter (fun x => color x = i)
  -- Pigeonhole: some fiber has ≥ n elements
  suffices hpig : ∃ i : Fin r, n ≤ (fiber i).card by
    obtain ⟨i, hi⟩ := hpig
    refine ⟨fiber i, i, Finset.filter_subset _ _, hi, ?_⟩
    -- Monochromatic: all 1-subsets of the fiber have color i
    intro e he_T he_S
    -- e is a singleton {x} with x in the fiber
    have he_sub := (Finset.mem_powersetCard.mp he_T).1
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp he_T).2
    have hxT := he_sub (Finset.mem_singleton_self x)
    rw [Finset.mem_filter] at hxT
    -- c({x}) = color(x) = i
    show c ⟨{x}, he_S⟩ = i
    have : c ⟨{x}, he_S⟩ = color x := by
      show c ⟨{x}, he_S⟩ = dite (x ∈ S) (fun h => c ⟨{x}, singleton_mem_kSubsets h⟩) _
      rw [dif_pos hxT.1]
    rw [this, hxT.2]
  -- Prove pigeonhole claim by contradiction
  by_contra hall
  push_neg at hall
  -- Sum of fiber sizes = |S|
  have hpart : S = Finset.univ.biUnion fiber := by
    ext x; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, fiber]
    exact ⟨fun h => ⟨color x, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r))) fiber := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter, fiber]
    intro x ⟨_, hci⟩ ⟨_, hcj⟩
    exact hij (hci.symm.trans hcj)
  have hsum : S.card = ∑ i : Fin r, (fiber i).card := by
    rw [hpart, Finset.card_biUnion hdisj]
  have hle : ∑ i : Fin r, (fiber i).card ≤ r * (n - 1) := by
    calc ∑ i : Fin r, (fiber i).card
        ≤ ∑ _ : Fin r, (n - 1) :=
          Finset.sum_le_sum (fun i _ => by have := hall i; omega)
      _ = r * (n - 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  omega

/-- For k ≥ 2, the Ramsey property follows from iterated stepping-up (Erdős–Rado).
    The full inductive proof requires the asymmetric multi-parameter recursion:
    R_k(s₁,...,sᵣ) ≤ R_{k-1}(R_k(s₁-1,...), ..., R_k(...,sᵣ-1)) + 1.
    This is left as an axiom pending the stepping-up formalization. -/
axiom hypergraph_ramsey_k2 (k r n : ℕ) (hk : k ≥ 2) (hr : r ≥ 1) (hn : n ≥ k) :
    ∃ N, HypergraphRamseyProperty k r n N

/-- The Hypergraph Ramsey Theorem (Ramsey 1930, full generality):
    For any k ≥ 1, r ≥ 1, n ≥ k, there exists N such that any r-coloring
    of k-subsets of an N-element set contains a monochromatic n-element subset.
    The k=1 case is proved (pigeonhole); k ≥ 2 uses the stepping-up axiom. -/
theorem hypergraph_ramsey_exists (k r n : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) (hn : n ≥ k) :
    ∃ N, HypergraphRamseyProperty k r n N := by
  rcases eq_or_lt_of_le hk with rfl | hk2
  · exact ⟨r * (n - 1) + 1, pigeonhole_ramsey r n hr (by omega)⟩
  · exact hypergraph_ramsey_k2 k r n (by omega) hr hn

/-! ## Part IV: Growth Rate -/

/-- Tower function: iterated exponentiation. Hypergraph Ramsey numbers grow
    as towers of exponentials, with height depending on k. -/
def tower : ℕ → ℕ → ℕ
  | _, 0 => 1
  | b, n + 1 => b ^ tower b n

/-- Tower(2, 1) = 2. -/
theorem tower_2_1 : tower 2 1 = 2 := by simp [tower]

/-- Tower(2, 2) = 4. -/
theorem tower_2_2 : tower 2 2 = 4 := by simp [tower]

/-- The tower function grows strictly. -/
theorem tower_strictMono (b : ℕ) (hb : b ≥ 2) : StrictMono (tower b) := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hmn) with rfl | hlt
    · -- m = n case: tower b n < tower b (n+1) = b ^ tower b n
      simp only [tower]
      calc tower b n < 2 ^ tower b n := Nat.lt_two_pow (tower b n)
        _ ≤ b ^ tower b n := Nat.pow_le_pow_left (by omega) (tower b n)
    · -- m < n case: use IH
      exact lt_trans (ih hlt) (by
        simp only [tower]
        calc tower b n < 2 ^ tower b n := Nat.lt_two_pow _
          _ ≤ b ^ tower b n := Nat.pow_le_pow_left (by omega) _)

/-! ## Part V: Infrastructure for Proving the Hypergraph Ramsey Theorem

The axiom `hypergraph_ramsey_exists` can be proved by well-founded induction
on (k, n) using the **stepping-up lemma**:

  R(k+1, r, n) ≤ R(k, r, R(k+1, r, n-1)) + 1

Base cases:
  1. n ≤ k: vacuously true (N = n, no k-subsets or only one)
  2. k = 1: pigeonhole principle (N = r*(n-1) + 1)

The stepping-up argument: Fix vertex v in [N]. The original (k+1)-coloring
induces a k-coloring on [N]\{v} via c'(T) = c(T ∪ {v}). By k-Ramsey, get
monochromatic M-set S. Restrict to S and apply (k+1, n-1)-Ramsey. If the
colors match, S ∪ {v} is the desired n-set.
-/

/-- kSubsets of S has cardinality Nat.choose |S| k. -/
theorem kSubsets_card [DecidableEq α] (s : Finset α) (k : ℕ) :
    (kSubsets s k).card = s.card.choose k := by
  simp [kSubsets, Finset.card_powersetCard]

/-- k-subsets are monotone: if T ⊆ S then kSubsets T k ⊆ kSubsets S k. -/
theorem kSubsets_subset [DecidableEq α] {s t : Finset α} (h : t ⊆ s) (k : ℕ) :
    kSubsets t k ⊆ kSubsets s k := by
  simp only [kSubsets]
  exact Finset.powersetCard_mono h

/-- A k-subset of T is a k-subset of S when T ⊆ S. -/
theorem kSubsets_mem_of_subset [DecidableEq α] {s t : Finset α} {e : Finset α}
    (h : t ⊆ s) (he : e ∈ kSubsets t k) : e ∈ kSubsets s k :=
  kSubsets_subset h k he

/-- When s.card < k, there are no k-subsets of s. -/
theorem kSubsets_eq_empty_of_lt [DecidableEq α] {s : Finset α} {k : ℕ}
    (h : s.card < k) : kSubsets s k = ∅ := by
  ext e; simp only [kSubsets, Finset.mem_powersetCard, Finset.not_mem_empty, iff_false]
  intro ⟨he_sub, he_card⟩
  exact absurd (le_trans (Finset.card_le_card he_sub) h.le) (by omega)

/-- Tower(b, n) is positive when b ≥ 1. -/
theorem tower_pos (b : ℕ) (hb : b ≥ 1) (n : ℕ) : tower b n ≥ 1 := by
  induction n with
  | zero => simp [tower]
  | succ k _ => simp [tower]; exact Nat.one_le_pow _ b hb

/-- The Ramsey property is monotone in N: larger N also works. -/
theorem ramsey_property_mono {k r n N : ℕ} (N' : ℕ) (hNN : N ≤ N')
    (h : HypergraphRamseyProperty k r n N) :
    HypergraphRamseyProperty k r n N' := by
  intro S hS c
  have hNS : N ≤ S.card := hS ▸ hNN
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_le hNS
  obtain ⟨T, i, hTS', hTn, hmono⟩ := h S' hS'card (fun ⟨e, he⟩ =>
    c ⟨e, kSubsets_mem_of_subset hS'sub he⟩)
  exact ⟨T, Finset.Subset.trans hTS' hS'sub, hTn, fun e he_T _ =>
    hmono e he_T (kSubsets_mem_of_subset hS'sub he_T)⟩

/-- Base case: when n ≤ k, N = n works.
    When n < k: no k-subsets exist, so monochromaticity holds vacuously.
    When n = k: exactly one k-subset (S itself), trivially monochromatic. -/
theorem ramsey_base (k r n : ℕ) (hr : r ≥ 1) (hn : n ≤ k) :
    HypergraphRamseyProperty k r n n := by
  intro S hS c
  by_cases h_nonempty : (kSubsets S k).Nonempty
  · -- n = k case: pick the color of any k-subset (they're all equal to S)
    obtain ⟨e₀, he₀⟩ := h_nonempty
    refine ⟨S, c ⟨e₀, he₀⟩, Subset.rfl, hS.symm.le, fun e _ he_S => ?_⟩
    -- e and e₀ are both k-subsets of S with |S| = n ≤ k, so e = S = e₀
    have h1 := (Finset.mem_powersetCard.mp he_S)
    have h2 := (Finset.mem_powersetCard.mp he₀)
    have : e = S := Finset.eq_of_subset_of_card_le h1.1 (by omega)
    have : e₀ = S := Finset.eq_of_subset_of_card_le h2.1 (by omega)
    simp_all
  · -- n < k case: no k-subsets, vacuously monochromatic
    rw [Finset.not_nonempty_iff_eq_empty] at h_nonempty
    exact ⟨S, ⟨0, hr⟩, Subset.rfl, hS.symm.le, fun e _ he_S =>
      absurd he_S (h_nonempty ▸ Finset.not_mem_empty e)⟩

/-! ## Part VI: Pigeonhole Base Case (k = 1)

For k = 1, coloring singletons is equivalent to coloring elements.
By the pigeonhole principle, if |S| ≥ r*(n-1)+1, some color appears ≥ n times. -/

/-- **Pigeonhole Ramsey**: the k = 1 base case of the Hypergraph Ramsey Theorem.
    When we color elements (= singletons) with r colors, N = r*(n-1)+1 suffices
    to find n elements of the same color. This is the pigeonhole principle. -/
theorem pigeonhole_ramsey (r n : ℕ) (hr : r ≥ 1) (hn : n ≥ 1) :
    HypergraphRamseyProperty 1 r n (r * (n - 1) + 1) := by
  intro S hS c
  -- Singleton membership: for a ∈ S, {a} is a 1-subset of S
  have h_sing : ∀ a ∈ S, {a} ∈ kSubsets S 1 := fun a ha => by
    simp only [kSubsets, Finset.mem_powersetCard]
    exact ⟨Finset.singleton_subset_iff.mpr ha, Finset.card_singleton a⟩
  -- Define element coloring: map each element to the color of its singleton
  let f : ℕ → Fin r := fun a =>
    if h : a ∈ S then c ⟨{a}, h_sing a h⟩ else ⟨0, by omega⟩
  -- Pigeonhole: r • (n-1) < |S| = r*(n-1)+1, so some color fiber has > n-1 elements
  have h_pig : (Finset.univ : Finset (Fin r)).card • (n - 1) < S.card := by
    rw [Finset.card_univ, Fintype.card_fin, hS, smul_eq_mul]; omega
  obtain ⟨i, _, h_fib⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card
    (f := f) (fun _ _ => Finset.mem_univ _) h_pig
  -- The monochromatic set: elements of S whose singleton has color i
  refine ⟨S.filter (f · = i), i, Finset.filter_subset _ _, ?_, ?_⟩
  · -- Size: fiber has > n-1 elements, so ≥ n
    omega
  · -- Monochromaticity: every 1-subset {a} of the filter has color i
    intro e he_T he_S
    -- e is a 1-element subset of our filter, so e = {a} for some a
    simp only [kSubsets, Finset.mem_powersetCard] at he_T
    obtain ⟨he_sub, he_card⟩ := he_T
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp he_card
    -- a is in the color-i filter, so f a = i, so c ⟨{a}, _⟩ = i
    have ha_filt := Finset.singleton_subset_iff.mp he_sub
    have ha_S : a ∈ S := Finset.filter_subset _ _ ha_filt
    have ha_color : f a = i := (Finset.mem_filter.mp ha_filt).2
    -- f a = c ⟨{a}, h_sing a ha_S⟩ when a ∈ S (by dif_pos)
    simp only [f, dif_pos ha_S] at ha_color
    -- Goal: c ⟨{a}, he_S⟩ = i. By proof irrelevance, he_S = h_sing a ha_S
    exact ha_color

end HypergraphRamsey
