/-
Erdős Problem #19 — Open Question OQ-02
Extensions to k-wise intersections (an Erdős–Füredi / Kleitman-style generalization)

**Status**: VERIFIED (0 sorries, 0 axioms beyond Lean's foundational
propext / Classical.choice / Quot.sound)

## Context

The parent problem `Erdos19` is the Erdős–Faber–Lovász conjecture, which lives
in the world of set families with *small* pairwise intersections.  Its natural
companion theme is the world of set families with *large* (nonempty)
intersections — **intersecting families** — studied by Kleitman, Erdős–Ko–Rado,
Frankl and others.  Mathlib formalizes the pairwise notion as `Set.Intersecting`
together with Kleitman's bound `Set.Intersecting.card_le` (an intersecting family
in a finite Boolean algebra occupies at most half the algebra).

This file formalizes the *k-wise* generalization and proves the two structural
facts that organize the whole subject:

1. **Reduction.** A `k`-wise intersecting family (`k ≥ 2`) is in particular
   pairwise intersecting, and `k`-wise intersection is monotone in `k`
   (larger `k` is a stronger hypothesis).
2. **Cardinality bound.** Consequently a `k`-wise intersecting family
   (`k ≥ 2`) in a finite Boolean algebra has at most half the elements:
   `2 * |𝒜| ≤ |α|`.  Specialized to subsets of an `n`-element ground set this is
   the classical `2 * |𝒜| ≤ 2 ^ n`, i.e. at most `2^{n-1}` members.
3. **Sharpness.** A principal up-set `{x | a ≤ x}` with `a ≠ ⊥` is `k`-wise
   intersecting *for every* `k` simultaneously, so the reduction in (1) cannot
   be improved: the same extremal families witness intersection at all levels.

`k`-wise intersection is defined directly: every nonempty subfamily of size at
most `k` has a meet (greatest common lower bound) that is not `⊥`.  Over a
Boolean algebra of finite sets this says every ≤ k members share a common point.

Reference: https://erdosproblems.com/19
-/

import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

open Finset

namespace Erdos19OQ02

variable {α : Type*} [BooleanAlgebra α]

/-- A finite family `𝒜` of elements of a Boolean algebra is **`k`-wise
intersecting** if every nonempty subfamily of size at most `k` has a meet that is
not `⊥`.  Concretely, for set families this says any `≤ k` members of `𝒜` share a
common point. -/
def KWiseIntersecting (k : ℕ) (𝒜 : Finset α) : Prop :=
  ∀ t : Finset α, t ⊆ 𝒜 → 0 < t.card → t.card ≤ k → t.inf id ≠ ⊥

/-- A subfamily of a `k`-wise intersecting family is `k`-wise intersecting. -/
theorem KWiseIntersecting.subfamily {k : ℕ} {𝒜 ℬ : Finset α} (hsub : ℬ ⊆ 𝒜)
    (h : KWiseIntersecting k 𝒜) : KWiseIntersecting k ℬ :=
  fun t ht hpos hcard => h t (ht.trans hsub) hpos hcard

/-- `k`-wise intersection is monotone in `k`: a stronger (larger-`k`) hypothesis
implies every weaker (smaller-`j`) one.  Thus the family of properties
`KWiseIntersecting k` is *antitone* in `k`. -/
theorem KWiseIntersecting.antitone {j k : ℕ} {𝒜 : Finset α} (hjk : j ≤ k)
    (h : KWiseIntersecting k 𝒜) : KWiseIntersecting j 𝒜 :=
  fun t ht hpos hcard => h t ht hpos (hcard.trans hjk)

/-- Every member of a (`k ≥ 1`)-wise intersecting family is nonzero (`≠ ⊥`):
take the singleton subfamily. -/
theorem KWiseIntersecting.mem_ne_bot {k : ℕ} {𝒜 : Finset α} (hk : 1 ≤ k)
    (h : KWiseIntersecting k 𝒜) {a : α} (ha : a ∈ 𝒜) : a ≠ ⊥ := by
  have hsingle := h {a} (Finset.singleton_subset_iff.mpr ha)
    (by rw [Finset.card_singleton]; omega) (by rw [Finset.card_singleton]; omega)
  simpa [Finset.inf_singleton, id_eq] using hsingle

/-- **Reduction to pairwise intersection.**  A `k`-wise intersecting family with
`k ≥ 2` is intersecting in Mathlib's pairwise sense: no two members are disjoint.
(`a = b` is covered by the singleton case via `mem_ne_bot`; `a ≠ b` by the pair
`{a, b}`.) -/
theorem KWiseIntersecting.intersecting [DecidableEq α] {k : ℕ} {𝒜 : Finset α} (hk : 2 ≤ k)
    (h : KWiseIntersecting k 𝒜) : (𝒜 : Set α).Intersecting := by
  intro a ha b hb
  rw [Finset.mem_coe] at ha hb
  rw [disjoint_iff]
  -- It suffices to show `a ⊓ b ≠ ⊥`, which is exactly the meet of `{a, b}`.
  have hsub : ({a, b} : Finset α) ⊆ 𝒜 :=
    Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
  have hpos : 0 < ({a, b} : Finset α).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_insert_self a {b}⟩
  have hcard : ({a, b} : Finset α).card ≤ k :=
    calc ({a, b} : Finset α).card ≤ ({b} : Finset α).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by rw [Finset.card_singleton]
      _ ≤ k := hk
  have hmeet := h {a, b} hsub hpos hcard
  have heq : ({a, b} : Finset α).inf id = a ⊓ b := by
    simp [Finset.inf_insert, Finset.inf_singleton]
  rw [heq] at hmeet
  exact hmeet

/-- **Cardinality bound (Kleitman-style).**  A `k`-wise intersecting family
(`k ≥ 2`) in a *finite* Boolean algebra occupies at most half the algebra:
`2 * |𝒜| ≤ |α|`.  This follows by combining the reduction to pairwise
intersection with Mathlib's `Set.Intersecting.card_le`. -/
theorem KWiseIntersecting.card_le [Fintype α] [DecidableEq α] {k : ℕ} {𝒜 : Finset α}
    (hk : 2 ≤ k) (h : KWiseIntersecting k 𝒜) : 2 * 𝒜.card ≤ Fintype.card α :=
  (h.intersecting hk).card_le

/-- **Classical form.**  A `k`-wise intersecting family of subsets of an
`n`-element ground set (`k ≥ 2`) has at most `2^{n-1}` members:
`2 * |𝒜| ≤ 2 ^ n`. -/
theorem kWiseIntersecting_subsets_card_le {n k : ℕ} (hk : 2 ≤ k)
    {𝒜 : Finset (Finset (Fin n))} (h : KWiseIntersecting k 𝒜) :
    2 * 𝒜.card ≤ 2 ^ n := by
  have := h.card_le hk
  simpa [Fintype.card_finset, Fintype.card_fin] using this

/-! ### Sharpness: principal up-sets are `k`-wise intersecting for all `k` -/

variable [Fintype α] [DecidableLE α]

/-- The principal up-set of `a`: all elements `x` with `a ≤ x`.  For set families
this is the family of all sets containing a fixed point. -/
def principalUp (a : α) : Finset α := Finset.univ.filter (fun x => a ≤ x)

@[simp] theorem mem_principalUp {a x : α} : x ∈ principalUp a ↔ a ≤ x := by
  simp [principalUp]

/-- A principal up-set `{x | a ≤ x}` with `a ≠ ⊥` is `k`-wise intersecting for
**every** `k`: every subfamily has meet `≥ a`, hence `≠ ⊥`.  This shows the
reduction `KWiseIntersecting.intersecting` is sharp — a single family witnesses
intersection at all levels `k` at once. -/
theorem principalUp_kWiseIntersecting {a : α} (ha : a ≠ ⊥) (k : ℕ) :
    KWiseIntersecting k (principalUp a) := by
  intro t ht _ _
  have hle : a ≤ t.inf id := by
    apply Finset.le_inf
    intro b hb
    have hb' : a ≤ b := (mem_principalUp).mp (ht hb)
    simpa using hb'
  intro hbot
  rw [hbot, le_bot_iff] at hle
  exact ha hle

/-- The principal up-set is in particular (pairwise) intersecting. -/
theorem principalUp_intersecting [DecidableEq α] {a : α} (ha : a ≠ ⊥) :
    (principalUp a : Set α).Intersecting :=
  (principalUp_kWiseIntersecting ha 2).intersecting le_rfl

/-- **Existence.**  In any nontrivial finite Boolean algebra there is a nonempty
`k`-wise intersecting family, for every `k`. -/
theorem exists_kWiseIntersecting [Nontrivial α] (k : ℕ) :
    ∃ 𝒜 : Finset α, 𝒜.Nonempty ∧ KWiseIntersecting k 𝒜 := by
  obtain ⟨a, ha⟩ := exists_ne (⊥ : α)
  exact ⟨principalUp a, ⟨a, (mem_principalUp).mpr le_rfl⟩, principalUp_kWiseIntersecting ha k⟩

end Erdos19OQ02
