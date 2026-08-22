import Mathlib

/-! # Reciprocity pruning for finite neighborhood-pattern systems

This is the abstract monotone engine behind the q=9 marked-pair row
obstruction.  A candidate at `p` is a finite set of proposed neighbors.  One
pruning round removes a candidate containing `q` unless `q` still has some
candidate containing `p`.  Any genuinely reciprocal global choice survives
every round, so an empty pruned fiber certifies impossibility.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Any deletion operator on a finite set reaches a fixed point within the
initial cardinality.  This is the generic finite-descent bound used for
bounded reciprocity pruning. -/
theorem finset_decreasing_iterate_stabilizes
    {β : Type*} [DecidableEq β]
    (f : Finset β → Finset β)
    (hsub : ∀ s, f s ⊆ s)
    (s : Finset β) :
    ∃ n ≤ s.card, (f^[n + 1]) s = (f^[n]) s := by
  by_cases hfix : f s = s
  · exact ⟨0, Nat.zero_le _, by simpa using hfix⟩
  · have hstrict : f s ⊂ s :=
      (Finset.ssubset_iff_subset_ne).2 ⟨hsub s, hfix⟩
    have hcard : (f s).card < s.card := Finset.card_lt_card hstrict
    obtain ⟨n, hn, hstable⟩ :=
      finset_decreasing_iterate_stabilizes f hsub (f s)
    refine ⟨n + 1, by omega, ?_⟩
    rw [show n + 1 + 1 = (n + 1) + 1 by omega,
      Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact hstable
termination_by s.card

/-- Delete every local pattern containing an arc unsupported in the reverse
direction by the current pattern families. -/
def reciprocalPatternPrune {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) : α → Finset (Finset α) :=
  fun p => (F p).filter fun S => ∀ q ∈ S, ∃ T ∈ F q, p ∈ T

/-- Pruning only deletes patterns. -/
theorem reciprocalPatternPrune_subset
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) (p : α) :
    reciprocalPatternPrune F p ⊆ F p := by
  exact Finset.filter_subset _ _

/-- Successive pruning iterates form a decreasing sequence, fiber by fiber. -/
theorem iterate_reciprocalPatternPrune_succ_subset
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) (n : ℕ) (p : α) :
    (reciprocalPatternPrune^[n + 1]) F p ⊆
      (reciprocalPatternPrune^[n]) F p := by
  rw [Function.iterate_succ_apply']
  exact reciprocalPatternPrune_subset ((reciprocalPatternPrune^[n]) F) p

/-- A pattern system is a pruning fixed point exactly when every proposed arc
has reverse support somewhere in the opposite fiber. -/
theorem reciprocalPatternPrune_eq_self_iff
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) :
    reciprocalPatternPrune F = F ↔
      ∀ p S, S ∈ F p → ∀ q ∈ S, ∃ T ∈ F q, p ∈ T := by
  constructor
  · intro heq p S hS q hq
    have hmem : S ∈ reciprocalPatternPrune F p := by
      rw [heq]
      exact hS
    exact (Finset.mem_filter.mp hmem).2 q hq
  · intro hsupported
    funext p
    ext S
    constructor
    · exact fun hS => (Finset.mem_filter.mp hS).1
    · intro hS
      exact Finset.mem_filter.mpr ⟨hS, hsupported p S hS⟩

/-- A reciprocal choice from `F` remains available after one pruning round. -/
theorem reciprocal_choice_mem_prune
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) (C : α → Finset α)
    (hmem : ∀ p, C p ∈ F p)
    (hrecip : ∀ p q, q ∈ C p ↔ p ∈ C q) :
    ∀ p, C p ∈ reciprocalPatternPrune F p := by
  intro p
  rw [reciprocalPatternPrune, Finset.mem_filter]
  refine ⟨hmem p, ?_⟩
  intro q hq
  exact ⟨C q, hmem q, (hrecip p q).mp hq⟩

/-- A reciprocal global choice survives every finite number of pruning
rounds. -/
theorem reciprocal_choice_mem_iterate_prune
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) (C : α → Finset α)
    (hmem : ∀ p, C p ∈ F p)
    (hrecip : ∀ p q, q ∈ C p ↔ p ∈ C q) :
    ∀ n p, C p ∈ (reciprocalPatternPrune^[n]) F p := by
  intro n
  induction n with
  | zero =>
      intro p
      simpa using hmem p
  | succ n ih =>
      intro p
      rw [Function.iterate_succ_apply']
      exact reciprocal_choice_mem_prune
        ((reciprocalPatternPrune^[n]) F) C ih hrecip p

/-- Emptying one pattern fiber after finitely many rounds rules out every
reciprocal global selection. -/
theorem no_reciprocal_choice_of_iterate_prune_eq_empty
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α))
    (n : ℕ) (p : α)
    (hempty : (reciprocalPatternPrune^[n]) F p = ∅) :
    ¬ ∃ C : α → Finset α,
      (∀ q, C q ∈ F q) ∧ (∀ q r, r ∈ C q ↔ q ∈ C r) := by
  rintro ⟨C, hmem, hrecip⟩
  have hp := reciprocal_choice_mem_iterate_prune F C hmem hrecip n p
  rw [hempty] at hp
  simpa using hp

/-- On an odd finite type there is no loopless reciprocal choice with exactly
one chosen neighbor at every vertex.  Equivalently, an odd-order simple graph
cannot be one-regular. -/
theorem no_loopless_reciprocal_singleton_choice_of_odd_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (C : α → Finset α)
    (hcard : ∀ p, (C p).card = 1)
    (hloop : ∀ p, p ∉ C p)
    (hrecip : ∀ p q, q ∈ C p ↔ p ∈ C q)
    (hodd : Odd (Fintype.card α)) : False := by
  classical
  let G := SimpleGraph.fromRel fun p q : α => q ∈ C p
  have hneighbor : ∀ p, G.neighborFinset p = C p := by
    intro p
    ext q
    simp only [G, SimpleGraph.mem_neighborFinset,
      SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hpq | hqp⟩
      · exact hpq
      · exact (hrecip q p).mp hqp
    · intro hpq
      exact ⟨fun hpqEq => hloop p (hpqEq ▸ hpq), Or.inl hpq⟩
  have hdegree : ∀ p, G.degree p = 1 := by
    intro p
    rw [← G.card_neighborFinset_eq_degree, hneighbor p, hcard p]
  have hsum : (∑ p, G.degree p) = Fintype.card α := by
    simp [hdegree]
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhandshake
  obtain ⟨k, hk⟩ := hodd
  omega

/-- If pruning forces every surviving pattern to be a singleton, odd
cardinality rules out a loopless reciprocal choice even when no fiber has
become empty. -/
theorem no_reciprocal_choice_of_iterate_prune_all_singleton_odd
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → Finset (Finset α)) (n : ℕ)
    (hselfless : ∀ p S, S ∈ F p → p ∉ S)
    (hsingle : ∀ p S, S ∈ (reciprocalPatternPrune^[n]) F p → S.card = 1)
    (hodd : Odd (Fintype.card α)) :
    ¬ ∃ C : α → Finset α,
      (∀ p, C p ∈ F p) ∧ (∀ p q, q ∈ C p ↔ p ∈ C q) := by
  rintro ⟨C, hmem, hrecip⟩
  have hsurvive := reciprocal_choice_mem_iterate_prune F C hmem hrecip n
  exact no_loopless_reciprocal_singleton_choice_of_odd_card C
    (fun p => hsingle p (C p) (hsurvive p))
    (fun p => hselfless p (C p) (hmem p)) hrecip hodd

/-- A small warning example: reverse-support consistency is not complete.
Each of three vertices may choose either other vertex as its singleton
pattern.  The system is pruning-stable, but a reciprocal choice would be a
perfect matching on an odd set. -/
def threePointSingletonPatterns (p : Fin 3) : Finset (Finset (Fin 3)) :=
  (Finset.univ.erase p).image fun q => {q}

theorem threePointSingletonPatterns_prune_fixed :
    reciprocalPatternPrune threePointSingletonPatterns =
      threePointSingletonPatterns := by
  classical
  rw [reciprocalPatternPrune_eq_self_iff]
  intro p S hS q hq
  rw [threePointSingletonPatterns, Finset.mem_image] at hS
  obtain ⟨r, hr, rfl⟩ := hS
  have hqr : q = r := by simpa using hq
  subst q
  refine ⟨{p}, ?_, Finset.mem_singleton_self p⟩
  rw [threePointSingletonPatterns, Finset.mem_image]
  refine ⟨p, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ p⟩, rfl⟩
  exact (Finset.mem_erase.mp hr).1.symm

theorem threePointSingletonPatterns_no_reciprocal_choice :
    ¬ ∃ C : Fin 3 → Finset (Fin 3),
      (∀ p, C p ∈ threePointSingletonPatterns p) ∧
        (∀ p q, q ∈ C p ↔ p ∈ C q) := by
  set_option maxRecDepth 100000 in
    decide

end

end Erdos85

#print axioms Erdos85.no_reciprocal_choice_of_iterate_prune_eq_empty
#print axioms Erdos85.no_loopless_reciprocal_singleton_choice_of_odd_card
#print axioms Erdos85.no_reciprocal_choice_of_iterate_prune_all_singleton_odd
#print axioms Erdos85.threePointSingletonPatterns_prune_fixed
#print axioms Erdos85.threePointSingletonPatterns_no_reciprocal_choice
