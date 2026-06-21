/-
  Erdős Problem #131 — Non-Dividing Sets
  Follow-up (oq-01-oq-01-oq-01): sharpening the EGZ bound `|A| ≤ 2a − 1` to the
  Davenport bound `|A| ≤ a + 1`.

  Source: https://erdosproblems.com/131
  Companion to: `Proofs.Erdos131Problem` (def `Erdos131.IsNonDividing`) and the
  EGZ follow-up `Proofs.Erdos131EGZBound` (`egz_nondividing_card_bound`).

  NOTE.  This file is deliberately SELF-CONTAINED: it re-states `IsNonDividing`
  (verbatim from the parent) rather than importing the companions, because the
  parent file does not currently compile against the pinned Mathlib (v4.26.0).
  Decoupling keeps this contribution axiom-free and independently verifiable.

  ## What this file adds

  The EGZ follow-up proves, via `Int.erdos_ginzburg_ziv`, that

      `egz_nondividing_card_bound` :  a ∈ A → 2 ≤ a → IsNonDividing A → A.card ≤ 2a − 1.

  That argument only uses the *size-exactly-`a`* zero-sum subset produced by EGZ
  (the Erdős–Ginzburg–Ziv constant `s(ℤ/aℤ) = 2a − 1`).  But the non-dividing
  property forbids a zero-sum subset of *every* size `≥ 2`, so the governing
  invariant is really the **Davenport constant** `D(ℤ/aℤ) = a`, which forbids a
  zero-sum subset of *any* size.  Exploiting this sharpens the bound to

      **If `a ∈ A`, `2 ≤ a`, and `A` is non-dividing, then `A.card ≤ a + 1`.**

  This nearly halves the EGZ bound: `a + 1 ≤ 2a − 1` for all `a ≥ 2`, with strict
  inequality for `a ≥ 3` (`davenport_le_egz`, `davenport_strictly_sharper`).

  Mechanism.  Work inside `A \ {a}`.
  * At most one element of `A \ {a}` is divisible by `a`: two such would form a
    size-`2` subset whose sum is `≡ 0 (mod a)`, violating non-dividing.
  * The remaining `≥ a` elements all have *nonzero* residue mod `a`.  By the
    Davenport bound (`exists_nonempty_subset_sum_dvd`: any `a` integers contain a
    nonempty subset with sum divisible by `a`, proved here by a prefix-sum
    pigeonhole) one of their nonempty subsets has sum `≡ 0`.  As every element is
    nonzero mod `a`, that subset has size `≥ 2` — again a violation.

  Hence `|A \ {a}| ≤ a`, i.e. `|A| ≤ a + 1`.

  Mathlib has EGZ but *not* the cyclic Davenport constant / zero-sum-free
  sequences, so `exists_nonempty_subset_sum_dvd` is built from scratch.

  All results are unconditional and axiom-free.  The bound is sharp at `a = 2`
  (`{2,4,5}`, `davenport_bound_sharp_at_two`), where `a + 1 = 3 = 2a − 1`.
-/

import Mathlib

namespace Erdos131Davenport

open Finset

/-- A set `A` is *non-dividing* if no `a ∈ A` divides the sum of any subset of
`A \ {a}` of size `≥ 2`.  (Verbatim copy of `Erdos131.IsNonDividing` from the
parent file `Proofs.Erdos131Problem`.) -/
def IsNonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.card ≥ 2 →
    ¬(a ∣ S.sum id)

/-- **Davenport bound for the cyclic group `ℤ/aℤ`.**  Any `a` natural numbers
contain a *nonempty* subset whose sum is divisible by `a`.

Proof: order `s` as a list `L` and consider the `a + 1` prefix sums of `L`
reduced mod `a`.  These land in `ZMod a` (which has `a` elements), so by
pigeonhole two prefix sums coincide; the block of `L` strictly between the two
indices is a nonempty sublist whose sum is `≡ 0 (mod a)`.  Its `toFinset` is the
desired subset.  (This is `D(ℤ/aℤ) ≤ a`; Mathlib lacks the Davenport constant.) -/
theorem exists_nonempty_subset_sum_dvd (a : ℕ) (ha : 1 ≤ a) (s : Finset ℕ)
    (hs : a ≤ s.card) :
    ∃ t ⊆ s, t.Nonempty ∧ a ∣ t.sum id := by
  haveI : NeZero a := ⟨by omega⟩
  classical
  -- Order `s` as a sorted (hence nodup) list.
  set L : List ℕ := s.sort (· ≤ ·) with hLdef
  have hnod : L.Nodup := by rw [hLdef]; exact s.sort_nodup _
  have hlen : L.length = s.card := by rw [hLdef]; exact s.length_sort _
  have hmem : ∀ x ∈ L, x ∈ s := by
    intro x hx; rw [hLdef] at hx; exact (Finset.mem_sort _).1 hx
  -- A prefix-sum splitting identity (no group/cast needed yet).
  have key_eq : ∀ (m n : ℕ), m ≤ n →
      (L.take n).sum = (L.take m).sum + ((L.take n).drop m).sum := by
    intro m n hmn
    have e1 : (L.take n).take m = L.take m := by
      rw [List.take_take, Nat.min_eq_left hmn]
    calc (L.take n).sum
        = ((L.take n).take m ++ (L.take n).drop m).sum := by rw [List.take_append_drop]
      _ = ((L.take n).take m).sum + ((L.take n).drop m).sum := by rw [List.sum_append]
      _ = (L.take m).sum + ((L.take n).drop m).sum := by rw [e1]
  -- The core: given two prefix indices with equal prefix-sum mod `a`, the block
  -- between them is a nonempty subset of `s` with sum divisible by `a`.
  have key : ∀ p q : Fin (L.length + 1), (p : ℕ) < (q : ℕ) →
      ((L.take (p : ℕ)).sum : ZMod a) = ((L.take (q : ℕ)).sum : ZMod a) →
      ∃ t ⊆ s, t.Nonempty ∧ a ∣ t.sum id := by
    intro p q hpq hfpq
    -- The block sum is `0` in `ZMod a`.
    have hcast : (((L.take (q : ℕ)).drop (p : ℕ)).sum : ZMod a) = 0 := by
      have hk := key_eq (p : ℕ) (q : ℕ) hpq.le
      have h2 : ((L.take (q : ℕ)).sum : ZMod a) =
          ((L.take (p : ℕ)).sum : ZMod a) + (((L.take (q : ℕ)).drop (p : ℕ)).sum : ZMod a) := by
        rw [hk]; push_cast; ring
      rw [← hfpq] at h2
      linear_combination -h2
    have hdvdblock : a ∣ ((L.take (q : ℕ)).drop (p : ℕ)).sum :=
      (ZMod.natCast_eq_zero_iff _ _).mp hcast
    -- The block is a nodup sublist of `L`.
    have hsub_block : List.Sublist ((L.take (q : ℕ)).drop (p : ℕ)) L :=
      (List.drop_sublist _ _).trans (List.take_sublist _ _)
    have hnod_block : ((L.take (q : ℕ)).drop (p : ℕ)).Nodup := hnod.sublist hsub_block
    -- ... and it is nonempty (its length is `q - p ≥ 1`).
    have hjle : (q : ℕ) ≤ L.length := by have := q.isLt; omega
    have hblen : ((L.take (q : ℕ)).drop (p : ℕ)).length = (q : ℕ) - (p : ℕ) := by
      rw [List.length_drop, List.length_take, Nat.min_eq_left hjle]
    have hblenpos : 0 < ((L.take (q : ℕ)).drop (p : ℕ)).length := by rw [hblen]; omega
    refine ⟨((L.take (q : ℕ)).drop (p : ℕ)).toFinset, ?_, ?_, ?_⟩
    · intro x hx
      rw [List.mem_toFinset] at hx
      exact hmem x (hsub_block.subset hx)
    · obtain ⟨z, hz⟩ :=
        List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hblenpos)
      exact ⟨z, List.mem_toFinset.2 hz⟩
    · have hsumeq : ((L.take (q : ℕ)).drop (p : ℕ)).toFinset.sum id
          = ((L.take (q : ℕ)).drop (p : ℕ)).sum := by
        rw [List.sum_toFinset id hnod_block, List.map_id]
      rw [hsumeq]; exact hdvdblock
  -- Pigeonhole on the `L.length + 1` prefix sums mod `a`.
  have hcardlt : Fintype.card (ZMod a) < Fintype.card (Fin (L.length + 1)) := by
    rw [ZMod.card, Fintype.card_fin]; omega
  obtain ⟨i, j, hne, hfeq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (L.length + 1) => ((L.take (i : ℕ)).sum : ZMod a)) hcardlt
  have hvalne : (i : ℕ) ≠ (j : ℕ) := Fin.val_injective.ne hne
  rcases lt_or_gt_of_ne hvalne with h | h
  · exact key i j h hfeq
  · exact key j i h hfeq.symm

/-- **Davenport structural bound for non-dividing sets.**

If `a ∈ A` with `a ≥ 2` and `A` is non-dividing, then `A.card ≤ a + 1`.

This sharpens `egz_nondividing_card_bound` (`A.card ≤ 2a − 1`): the EGZ argument
uses only a size-`a` zero-sum subset, whereas non-dividing forbids zero-sum
subsets of *every* size `≥ 2`, so the Davenport constant `D(ℤ/aℤ) = a` governs. -/
theorem davenport_nondividing_card_bound (A : Finset ℕ) (a : ℕ)
    (ha : a ∈ A) (ha2 : 2 ≤ a) (hND : IsNonDividing A) :
    A.card ≤ a + 1 := by
  by_contra hcon
  push_neg at hcon
  set B := A.erase a with hB
  have hBcard : a + 1 ≤ B.card := by
    rw [hB, Finset.card_erase_of_mem ha]; omega
  -- At most one element of `B` is divisible by `a` (two would pair to a size-2
  -- zero-sum subset).
  have hZle : (B.filter (fun x => a ∣ x)).card ≤ 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hc
    rw [Finset.mem_filter] at hx hy
    have hsub : ({x, y} : Finset ℕ) ⊆ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx.1
      · exact hy.1
    have hcard2 : ({x, y} : Finset ℕ).card = 2 := Finset.card_pair hxy
    have hdvd : a ∣ ({x, y} : Finset ℕ).sum id := by
      apply Finset.dvd_sum
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx.2
      · exact hy.2
    exact hND a ha {x, y} hsub hcard2.ge hdvd
  -- The remaining (nonzero-residue) part has `≥ a` elements.
  have hNZcard : a ≤ (B.filter (fun x => ¬ a ∣ x)).card := by
    have hsplit :=
      Finset.filter_card_add_filter_neg_card_eq_card (s := B) (p := fun x => a ∣ x)
    omega
  -- Davenport applied to the nonzero part yields a nonempty zero-sum subset...
  obtain ⟨t, htsub, htne, htdvd⟩ :=
    exists_nonempty_subset_sum_dvd a (by omega) (B.filter (fun x => ¬ a ∣ x)) hNZcard
  -- ... of size `≥ 2`, since each element is nonzero mod `a`.
  have ht2 : 2 ≤ t.card := by
    rcases Nat.lt_or_ge t.card 2 with h | h
    · exfalso
      have h1 : t.card = 1 := by have := Finset.card_pos.2 htne; omega
      obtain ⟨x, hxsing⟩ := Finset.card_eq_one.1 h1
      have hxmem : x ∈ B.filter (fun x => ¬ a ∣ x) :=
        htsub (by rw [hxsing]; exact Finset.mem_singleton_self x)
      rw [Finset.mem_filter] at hxmem
      have hax : a ∣ x := by
        have hsx : t.sum id = x := by simp [hxsing]
        rwa [hsx] at htdvd
      exact hxmem.2 hax
    · exact h
  have htB : t ⊆ B := htsub.trans (Finset.filter_subset _ _)
  exact hND a ha t htB ht2 htdvd

/-- **Smallest-element bound.** A non-dividing set all of whose elements are `≥ 2`
has at most `min + 1` elements, where `min` is its least element. -/
theorem davenport_card_le_min_succ (A : Finset ℕ) (hA : A.Nonempty)
    (hmin : ∀ x ∈ A, 2 ≤ x) (hND : IsNonDividing A) :
    A.card ≤ A.min' hA + 1 := by
  have hmem := A.min'_mem hA
  exact davenport_nondividing_card_bound A (A.min' hA) hmem (hmin _ hmem) hND

/-- The Davenport bound is **at least as strong** as the EGZ bound: for `a ≥ 2`,
`a + 1 ≤ 2a − 1`. -/
theorem davenport_le_egz (a : ℕ) (ha : 2 ≤ a) : a + 1 ≤ 2 * a - 1 := by omega

/-- ... and **strictly stronger** for `a ≥ 3`: `a + 1 < 2a − 1`. -/
theorem davenport_strictly_sharper (a : ℕ) (ha : 3 ≤ a) : a + 1 < 2 * a - 1 := by omega

/-- **Recovers the parent parity bound** `two_in_nondividing_bound` as the
`a = 2` special case: `2 ∈ A` forces `A.card ≤ 3 = 2 + 1`.  (Here the Davenport
bound `a + 1` and the EGZ bound `2a − 1` coincide.) -/
theorem two_in_card_le_three (A : Finset ℕ) (h2 : 2 ∈ A) (hND : IsNonDividing A) :
    A.card ≤ 3 := by
  have h := davenport_nondividing_card_bound A 2 h2 (le_refl 2) hND
  omega

/-- **Contrapositive / certification form.** If a candidate set has more than
`a + 1` elements for some `a ∈ A` with `a ≥ 2`, it cannot be non-dividing. -/
theorem not_nondividing_of_card_gt (A : Finset ℕ) (a : ℕ)
    (ha : a ∈ A) (ha2 : 2 ≤ a) (hcard : a + 1 < A.card) :
    ¬ IsNonDividing A := by
  intro hND
  exact absurd (davenport_nondividing_card_bound A a ha ha2 hND) (by omega)

/- ## Sharpness at `a = 2` -/

/-- Helper: a subset of size `≥ 2` inside a set of size `≤ 2` equals it. -/
private lemma finset_eq_of_subset_of_card_two {S T : Finset ℕ}
    (hsub : S ⊆ T) (hS : S.card ≥ 2) (hT : T.card ≤ 2) : S = T :=
  Finset.eq_of_subset_of_card_le hsub (by omega)

/-- `{2, 4, 5}` is non-dividing (`2 ∤ 9`, `4 ∤ 7`, `5 ∤ 6`). -/
theorem two_four_five_nondividing : IsNonDividing ({2, 4, 5} : Finset ℕ) := by
  intro a ha S hS hCard hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · have hle : (({2, 4, 5} : Finset ℕ).erase 2).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 2 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)
  · have hle : (({2, 4, 5} : Finset ℕ).erase 4).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 4 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)
  · have hle : (({2, 4, 5} : Finset ℕ).erase 5).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 5 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)

/-- The Davenport bound is **sharp at `a = 2`**: `{2,4,5}` is non-dividing,
contains `2`, and has `card = 3 = 2 + 1`, meeting `two_in_card_le_three` (and
`davenport_nondividing_card_bound` at `a = 2`) with equality. -/
theorem davenport_bound_sharp_at_two :
    (2 : ℕ) ∈ ({2, 4, 5} : Finset ℕ) ∧
    IsNonDividing ({2, 4, 5} : Finset ℕ) ∧
    ({2, 4, 5} : Finset ℕ).card = 2 + 1 :=
  ⟨by decide, two_four_five_nondividing, by decide⟩

end Erdos131Davenport
