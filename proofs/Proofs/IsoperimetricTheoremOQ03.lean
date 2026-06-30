/-
Discrete Isoperimetric Inequality on the Cycle C_n (the Discrete Circle)

Open Question from: Isoperimetric Theorem (Wiedijk #43), OQ-03
"Best constants in non-Euclidean spaces."

The classical isoperimetric inequality lives in the Euclidean plane. Its simplest
*non-Euclidean* model space is the circle S¹ — a compact 1-manifold of constant
(positive) curvature. The faithful discrete model of S¹ is the cycle graph
C_n = ℤ/nℤ with the nearest-neighbour adjacency i ~ i ± 1.

This file formalizes the discrete isoperimetric inequality on C_n and pins down its
sharp constant. For S ⊆ ℤ/nℤ we split the cut edges of the cycle into

  rises S = { i : i ∉ S ∧ i+1 ∈ S }   ("entering" edges)
  falls S = { i : i ∈ S ∧ i+1 ∉ S }   ("leaving" edges)
  cut S   = rises S ∪ falls S          (the edge boundary)

and prove:

  * (Balance)        |rises S| = |falls S|.  Closing the loop forces the number of
                     times the indicator rises to equal the number of times it falls.
  * (Structure)      |cut S| = 2 · |rises S|.
  * (Evenness)       |cut S| is even — a phenomenon special to the *closed* loop,
                     absent for the line ℤ (sibling entry OQ-02 → OQ-03).
  * (Sharp bound)    every proper nonempty S has |cut S| ≥ 2.
  * (Achievability)  a single vertex {a} (the smallest geodesic ball) attains
                     |cut S| = 2 whenever n ≥ 2.

Hence the best isoperimetric constant on the discrete circle is 2, achieved by
geodesic balls (arcs) — the discrete analogue of "circles are optimal".

Everything below is fully verified: no axioms, no sorries.

Tags: combinatorics, discrete-geometry, isoperimetric-inequality, cycle-graph,
non-euclidean
-/
import Mathlib

namespace IsoperimetricCycle

open Finset

variable {n : ℕ} [NeZero n]

/-- The "rising" edges of `S ⊆ ℤ/nℤ`: positions `i` with `i ∉ S` but `i + 1 ∈ S`. -/
def rises (S : Finset (ZMod n)) : Finset (ZMod n) :=
  univ.filter (fun i => i ∉ S ∧ i + 1 ∈ S)

/-- The "falling" edges of `S ⊆ ℤ/nℤ`: positions `i` with `i ∈ S` but `i + 1 ∉ S`. -/
def falls (S : Finset (ZMod n)) : Finset (ZMod n) :=
  univ.filter (fun i => i ∈ S ∧ i + 1 ∉ S)

/-- The edge boundary (cut) of `S`: the cut edges of the cycle, i.e. the positions
    `i` where membership in `S` changes between `i` and `i + 1`. -/
def cut (S : Finset (ZMod n)) : Finset (ZMod n) :=
  rises S ∪ falls S

/-- `rises` and `falls` are disjoint: a position cannot both have `i ∉ S` and
    `i ∈ S`. -/
lemma disjoint_rises_falls (S : Finset (ZMod n)) :
    Disjoint (rises S) (falls S) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [rises, falls, Finset.mem_filter] at ha hb
  exact ha.2.1 hb.2.1

/-- **Balance lemma.** On the cycle the number of rising edges equals the number of
    falling edges. The indicator of `S` must rise and fall the same number of times
    on its way around the loop. -/
lemma rises_card_eq_falls_card (S : Finset (ZMod n)) :
    (rises S).card = (falls S).card := by
  -- Reindexing by `i ↦ i + 1` (a bijection of ℤ/nℤ) shows the shifted indicator
  -- sums to the same total as the unshifted one.
  have key : (∑ i : ZMod n, (if i + 1 ∈ S then (1 : ℤ) else 0))
           = (∑ i : ZMod n, (if i ∈ S then (1 : ℤ) else 0)) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun _ => rfl)
  have hsum : (∑ i : ZMod n,
      ((if i + 1 ∈ S then (1 : ℤ) else 0) - (if i ∈ S then (1 : ℤ) else 0))) = 0 := by
    rw [Finset.sum_sub_distrib, key, sub_self]
  -- Each term is `(rise indicator) - (fall indicator)`.
  have term : ∀ i : ZMod n,
      ((if i + 1 ∈ S then (1 : ℤ) else 0) - (if i ∈ S then (1 : ℤ) else 0))
      = ((if (i ∉ S ∧ i + 1 ∈ S) then (1 : ℤ) else 0)
          - (if (i ∈ S ∧ i + 1 ∉ S) then (1 : ℤ) else 0)) := by
    intro i; by_cases h1 : i ∈ S <;> by_cases h2 : i + 1 ∈ S <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun i _ => term i), Finset.sum_sub_distrib,
      Finset.sum_boole, Finset.sum_boole] at hsum
  have hcast : ((rises S).card : ℤ) = ((falls S).card : ℤ) := by
    simp only [rises, falls]; linarith [hsum]
  exact_mod_cast hcast

/-- **Structure of the cut.** The edge boundary has cardinality `2 · |rises S|`. -/
theorem cut_card_eq_two_mul_rises (S : Finset (ZMod n)) :
    (cut S).card = 2 * (rises S).card := by
  rw [cut, Finset.card_union_of_disjoint (disjoint_rises_falls S),
      ← rises_card_eq_falls_card]
  ring

/-- **Evenness.** The edge boundary of any `S ⊆ ℤ/nℤ` has even cardinality. This is
    forced by the loop topology of the cycle and has no analogue on the line ℤ. -/
theorem cut_card_even (S : Finset (ZMod n)) : Even (cut S).card := by
  rw [cut_card_eq_two_mul_rises]
  exact ⟨(rises S).card, by ring⟩

/-- If `rises S` is empty then `S` is closed under taking predecessors:
    `i + 1 ∈ S → i ∈ S`. -/
lemma closed_of_rises_empty {S : Finset (ZMod n)} (h : rises S = ∅) :
    ∀ i : ZMod n, i + 1 ∈ S → i ∈ S := by
  intro i hi
  by_contra hiS
  have : i ∈ rises S := by simp [rises, hiS, hi]
  rw [h] at this
  exact absurd this (Finset.notMem_empty i)

/-- **No rises forces the whole cycle.** A nonempty `S ⊆ ℤ/nℤ` with no rising edge is
    all of `ℤ/nℤ`: closure under predecessors propagates membership around the loop,
    since `1` generates the additive group. -/
lemma rises_nonempty {S : Finset (ZMod n)} (hne : S.Nonempty) (hproper : S ≠ univ) :
    (rises S).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have closed := closed_of_rises_empty h
  obtain ⟨a, ha⟩ := hne
  -- Every `a - k` (k : ℕ) is in S, by induction on k using predecessor closure.
  have allmem : ∀ k : ℕ, a - (k : ZMod n) ∈ S := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ m ih =>
        have hstep := closed (a - ((m : ZMod n) + 1))
        have e1 : a - ((m : ZMod n) + 1) + 1 = a - (m : ZMod n) := by ring
        rw [e1] at hstep
        have hres := hstep ih
        have e2 : a - (((m + 1 : ℕ)) : ZMod n) = a - ((m : ZMod n) + 1) := by
          push_cast; ring
        rw [e2]; exact hres
  -- Hence S = univ, contradicting properness. Every `x` is `a - k` for some `k : ℕ`
  -- because `Nat.cast : ℕ → ZMod n` is surjective.
  apply hproper
  rw [Finset.eq_univ_iff_forall]
  intro x
  obtain ⟨k, hk⟩ := (ZMod.natCast_rightInverse (n := n)).surjective (a - x)
  have hxeq : a - (k : ZMod n) = x := by rw [hk]; ring
  rw [← hxeq]
  exact allmem k

/-- **Sharp isoperimetric lower bound on the cycle.** Every proper nonempty subset of
    `ℤ/nℤ` has edge boundary of cardinality at least `2`. This is the best constant. -/
theorem cut_card_ge_two {S : Finset (ZMod n)} (hne : S.Nonempty) (hproper : S ≠ univ) :
    2 ≤ (cut S).card := by
  rw [cut_card_eq_two_mul_rises]
  have h1 := (rises_nonempty hne hproper).card_pos
  omega

/-- **Achievability.** A single vertex `{a}` — the smallest discrete geodesic ball —
    achieves the sharp constant `|cut S| = 2`, provided `n ≥ 2`. -/
theorem cut_card_singleton (a : ZMod n) (hn : 2 ≤ n) :
    (cut ({a} : Finset (ZMod n))).card = 2 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hone : (1 : ZMod n) ≠ 0 := one_ne_zero
  -- The two distinctness facts on the cycle, derived without ordered-field lemmas.
  have hsub : (a - 1 : ZMod n) ≠ a := by
    intro h; apply hone
    have h2 : a - (a - 1) = a - a := by rw [h]
    rw [sub_sub_cancel, sub_self] at h2
    exact h2
  have hadd : (a + 1 : ZMod n) ≠ a := by
    intro h; apply hone
    have h2 : a + 1 - a = a - a := by rw [h]
    rw [add_sub_cancel_left, sub_self] at h2
    exact h2
  have hrises : rises ({a} : Finset (ZMod n)) = {a - 1} := by
    ext i
    simp only [rises, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, hi1⟩
      rw [← hi1]; ring
    · rintro rfl
      exact ⟨hsub, by ring⟩
  have hfalls : falls ({a} : Finset (ZMod n)) = {a} := by
    ext i
    simp only [falls, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hi, _⟩; exact hi
    · rintro rfl
      exact ⟨rfl, hadd⟩
  have hd : Disjoint ({a - 1} : Finset (ZMod n)) {a} := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_singleton]
    exact hsub
  rw [cut, hrises, hfalls, Finset.card_union_of_disjoint hd]
  simp

/-- **Packaged isoperimetric inequality on the discrete circle.** Combines the sharp
    lower bound `2 ≤ |cut S|` with its achievability by a geodesic ball: `2` is the
    best isoperimetric constant on the cycle `ℤ/nℤ` for `n ≥ 2`. -/
theorem cycle_isoperimetric (hn : 2 ≤ n) :
    (∀ S : Finset (ZMod n), S.Nonempty → S ≠ univ → 2 ≤ (cut S).card)
    ∧ (∃ S : Finset (ZMod n), S.Nonempty ∧ S ≠ univ ∧ (cut S).card = 2) := by
  refine ⟨fun S hne hproper => cut_card_ge_two hne hproper, ⟨{0}, ?_, ?_, ?_⟩⟩
  · exact Finset.singleton_nonempty 0
  · -- {0} ≠ univ since univ has n ≥ 2 elements
    intro h
    have : ({0} : Finset (ZMod n)).card = Fintype.card (ZMod n) := by
      rw [h]; exact Finset.card_univ
    rw [Finset.card_singleton, ZMod.card] at this
    omega
  · exact cut_card_singleton 0 hn

end IsoperimetricCycle
