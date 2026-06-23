/-
Erdős Problem #1023 — Open Question: forbidding unions of *exactly* k members

The parent entry (Erdős #1023) settles the union-free extremal function
F(n) = C(n, ⌊n/2⌋): a family of subsets of {1,…,n} in which no member is the
union of (two or more) *other* members has at most C(n, ⌊n/2⌋) sets, and the
middle layer attains this.

One of the open questions listed there asks: **what if we forbid unions of a
fixed number k of sets?**  Define a family to be `k`-union-free when no member
equals the union of *exactly* `k` distinct other members.  This file develops
the elementary structure theory of that hierarchy, all fully verified:

* boundary k = 0 : `k`-union-free ⟺ the empty set is not a member;
* boundary k = 1 : *every* family is 1-union-free (a member can never be the
  union of a single different member);
* antichains are `k`-union-free for **every** k ≥ 1 (strengthening the parent's
  "antichains are union-free", which only forbids unions of size ≥ 2);
* (≥2)-union-free ⟹ `k`-union-free for every k ≥ 2;
* every single layer (sets of one fixed size) is an antichain, hence
  `k`-union-free; the middle layer gives the lower bound
  F_k(n) ≥ C(n, ⌊n/2⌋) for every k ≥ 1.

So the parent's lower-bound construction is *robust*: the same middle layer
witnesses the bound no matter which fixed arity k of unions is forbidden.

This file is self-contained (it does not import the parent) and axiom-free.

Reference: https://erdosproblems.com/1023
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Finset

namespace Erdos1023OQ03

variable {n : ℕ}

/-- A set family on `{0,…,n-1}` is a finite collection of subsets. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- The union of all members of a subfamily. -/
def familyUnion (F : SetFamily n) : Finset (Fin n) := F.sup id

@[simp] theorem familyUnion_empty : familyUnion (∅ : SetFamily n) = ∅ :=
  Finset.sup_empty

@[simp] theorem familyUnion_singleton (B : Finset (Fin n)) :
    familyUnion ({B} : SetFamily n) = B := by
  simp [familyUnion]

/-- Each member of a subfamily is contained in the family's union. -/
lemma mem_sub_familyUnion {F : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ F) :
    B ⊆ familyUnion F := by
  intro x hx
  simp only [familyUnion]
  exact Finset.mem_sup.mpr ⟨B, hB, hx⟩

/-
## The k-union hierarchy
-/

/-- `A` is the union of *exactly* `k` distinct members of `F` (none equal to `A`). -/
def isKUnionOf (A : Finset (Fin n)) (F : SetFamily n) (k : ℕ) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card = k ∧ A ∉ G ∧ familyUnion G = A

/-- `F` is `k`-union-free: no member is the union of exactly `k` other members. -/
def isKUnionFree (F : SetFamily n) (k : ℕ) : Prop :=
  ∀ A ∈ F, ¬ isKUnionOf A (F.erase A) k

/-- An antichain: no member is properly contained in another. -/
def isAntichain (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-
## Boundary cases k = 0 and k = 1
-/

/-- Forbidding unions of `0` sets is exactly forbidding the empty set: the only
"empty union" is `∅`. -/
theorem kUnionFree_zero (F : SetFamily n) :
    isKUnionFree F 0 ↔ (∅ : Finset (Fin n)) ∉ F := by
  constructor
  · intro h hmem
    exact h ∅ hmem ⟨∅, Finset.empty_subset _, by simp, by simp, familyUnion_empty⟩
  · rintro hnot A hA ⟨G, _, hGcard, _, hGunion⟩
    rw [Finset.card_eq_zero] at hGcard
    subst hGcard
    rw [familyUnion_empty] at hGunion
    exact hnot (hGunion ▸ hA)

/-- *Every* family is `1`-union-free: a member can never be the union of a single
*different* member (that union is the other member itself). -/
theorem kUnionFree_one (F : SetFamily n) : isKUnionFree F 1 := by
  rintro A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  obtain ⟨B, rfl⟩ := Finset.card_eq_one.mp hGcard
  rw [familyUnion_singleton] at hGunion
  rw [hGunion] at hAnotG
  exact hAnotG (Finset.mem_singleton_self A)

/-
## Antichains are k-union-free for every k ≥ 1
-/

/-- Antichains are `k`-union-free for **every** arity `k ≥ 1`.  This strengthens
the parent's `antichain_unionFree` (which forbids only unions of size ≥ 2): the
obstruction already appears with a *single* contributing member, because any set
contributing to a union equal to `A` is contained in `A`, hence equals `A` by the
antichain property — contradicting that it is a *different* member. -/
theorem antichain_kUnionFree (F : SetFamily n) (hanti : isAntichain F)
    (k : ℕ) (hk : 1 ≤ k) : isKUnionFree F k := by
  rintro A hA ⟨G, hGsub, hGcard, _, hGunion⟩
  have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B, hB⟩ := hGne
  have hBmem : B ∈ F.erase A := hGsub hB
  have hBF : B ∈ F := Finset.mem_of_mem_erase hBmem
  have hBsubA : B ⊆ A := by
    rw [← hGunion]; exact mem_sub_familyUnion hB
  have hBA : B = A := hanti B hBF A hA hBsubA
  exact (Finset.mem_erase.mp hBmem).1 hBA

/-
## Relation to the parent's (≥2)-union-free notion
-/

/-- `A` is the union of two or more other members (the parent's notion). -/
def isUnionOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ 2 ≤ G.card ∧ A ∉ G ∧ familyUnion G = A

/-- `F` is union-free: no member is the union of two or more other members. -/
def isUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬ isUnionOf A (F.erase A)

/-- A (≥2)-union-free family forbids unions of every fixed arity `k ≥ 2`: a
size-exactly-`k` union with `k ≥ 2` is in particular a union of size ≥ 2. -/
theorem unionFree_implies_kUnionFree (F : SetFamily n) (h : isUnionFree F)
    (k : ℕ) (hk : 2 ≤ k) : isKUnionFree F k := by
  rintro A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  exact h A hA ⟨G, hGsub, by omega, hAnotG, hGunion⟩

/-
## Layers, the middle layer, and the lower bound
-/

/-- The power set of `{0,…,n-1}`. -/
def powerSet (n : ℕ) : SetFamily n := univ.powerset

/-- The `k`-th layer: all subsets of size exactly `k`. -/
def layer (n k : ℕ) : SetFamily n := (powerSet n).filter (fun A => A.card = k)

/-- A layer has `C(n, k)` members. -/
theorem layer_card (n k : ℕ) : (layer n k).card = Nat.choose n k := by
  rw [layer, powerSet, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]

/-- Every single layer is an antichain: equal-size sets with `A ⊆ B` coincide. -/
theorem layer_antichain (n k : ℕ) : isAntichain (layer n k) := by
  intro A hA B hB hAB
  simp only [layer, powerSet, mem_filter] at hA hB
  have hcard : A.card = B.card := by rw [hA.2, hB.2]
  exact Finset.eq_of_subset_of_card_le hAB hcard.ge

/-- The middle layer: subsets of size `⌊n/2⌋`. -/
def middleLayer (n : ℕ) : SetFamily n := layer n (n / 2)

theorem middleLayer_card (n : ℕ) : (middleLayer n).card = Nat.choose n (n / 2) :=
  layer_card n (n / 2)

theorem middleLayer_antichain (n : ℕ) : isAntichain (middleLayer n) :=
  layer_antichain n (n / 2)

/-- The middle layer is `k`-union-free for every `k ≥ 1`. -/
theorem middleLayer_kUnionFree (n k : ℕ) (hk : 1 ≤ k) :
    isKUnionFree (middleLayer n) k :=
  antichain_kUnionFree _ (middleLayer_antichain n) k hk

/-- **Lower bound construction.** For every fixed arity `k ≥ 1` there is a
`k`-union-free family of subsets of `{1,…,n}` with `C(n, ⌊n/2⌋)` members. -/
theorem exists_kUnionFree_card (n k : ℕ) (hk : 1 ≤ k) :
    ∃ F : SetFamily n, isKUnionFree F k ∧ F.card = Nat.choose n (n / 2) :=
  ⟨middleLayer n, middleLayer_kUnionFree n k hk, middleLayer_card n⟩

/-
## The extremal function F_k(n) and its lower bound
-/

/-- Any set family on `Fin n` has at most `2 ^ n` members. -/
theorem family_card_le (F : SetFamily n) : F.card ≤ 2 ^ n := by
  calc F.card ≤ Fintype.card (Finset (Fin n)) := Finset.card_le_univ F
    _ = 2 ^ n := by rw [Fintype.card_finset, Fintype.card_fin]

/-- `F_k(n)`: the maximum size of a `k`-union-free family of subsets of
`{1,…,n}`. -/
noncomputable def kUnionFreeMax (n k : ℕ) : ℕ :=
  sSup {m | ∃ F : SetFamily n, isKUnionFree F k ∧ F.card = m}

theorem kUnionFreeMax_bddAbove (n k : ℕ) :
    BddAbove {m | ∃ F : SetFamily n, isKUnionFree F k ∧ F.card = m} := by
  refine ⟨2 ^ n, ?_⟩
  rintro m ⟨F, -, rfl⟩
  exact family_card_le F

/-- **The lower bound is uniform in `k`.**  For every `k ≥ 1`,
`F_k(n) ≥ C(n, ⌊n/2⌋)` — the same middle-layer bound as the parent's
union-free function, regardless of which fixed union-arity is forbidden. -/
theorem kUnionFreeMax_ge_middle (n k : ℕ) (hk : 1 ≤ k) :
    Nat.choose n (n / 2) ≤ kUnionFreeMax n k := by
  apply le_csSup (kUnionFreeMax_bddAbove n k)
  exact ⟨middleLayer n, middleLayer_kUnionFree n k hk, middleLayer_card n⟩

end Erdos1023OQ03
