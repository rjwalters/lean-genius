/-
Erdős Problem #83 — Sharpness of the Complete Intersection bound (LOWER BOUND)

The Ahlswede–Khachatrian Complete Intersection Theorem (1997, $500 Erdős prize)
states that a family `F` of `2n`-subsets of `[4n]` with `|A ∩ B| ≥ 2` for all
`A, B ∈ F` satisfies

    |F| ≤ ½ (C(4n, 2n) − C(2n, n)²)  =: erdos83Bound n.

The *upper* bound is the deep theorem (its "pushing–pulling" proof is correctly
axiomatized in `Proofs/Erdos83Problem.lean`).  This file proves the *lower* bound
— that the bound is **sharp** — by an elementary, fully machine-checked argument:

    There exists a valid family achieving exactly `erdos83Bound n`.

The witness is the **majority family**: fix a `2n`-element "core" `C ⊆ [4n]` and
take all `2n`-subsets meeting `C` in at least `n + 1` elements.  Two such sets
share `≥ (n+1) + (n+1) − 2n = 2` core elements (pigeonhole), so the family is
`2`-intersecting; and a complement involution `S ↦ Sᶜ` pairs the "majority"
sets with the "minority" sets, leaving the `C(2n,n)²` "balanced" sets in the
middle, whence the count is `½ (C(4n,2n) − C(2n,n)²)`.

This is a genuine, 0-axiom verification of the easy (achievability) direction of
Erdős #83; it complements the axiomatized upper bound rather than reproving it.

References:
- Ahlswede, Khachatrian (1997), European J. Combin. 18, 125-136
- https://erdosproblems.com/83
-/

import Mathlib

open Finset Nat

namespace Erdos83LowerBound

variable {α : Type*} [DecidableEq α]

/-- A family is `t`-intersecting if every pair of members meets in `≥ t` points. -/
def IsTIntersecting (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, t ≤ (A ∩ B).card

/-- A family is `k`-uniform if every member has exactly `k` elements. -/
def IsKUniform (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ A ∈ F, A.card = k

/-- The Erdős #83 admissibility predicate: a family of `2n`-subsets of `[4n]`
with pairwise intersections of size at least `2`. -/
def IsValidErdos83Family (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) : Prop :=
  IsKUniform F (2 * n) ∧ IsTIntersecting F 2

/-- The Ahlswede–Khachatrian bound `½ (C(4n,2n) − C(2n,n)²)`. -/
def erdos83Bound (n : ℕ) : ℕ :=
  ((4 * n).choose (2 * n) - ((2 * n).choose n) ^ 2) / 2

/-!
## Pigeonhole: the majority family is `2`-intersecting
-/

/-- **Core pigeonhole.** If `A` and `B` each meet `C` in at least `s` points, then
`2 s ≤ |A ∩ B| + |C|`.  (Specializing `s = n+1`, `|C| = 2n` gives `|A ∩ B| ≥ 2`.) -/
theorem two_mul_le_card_inter_add_core {A B C : Finset α} {s : ℕ}
    (hA : s ≤ (A ∩ C).card) (hB : s ≤ (B ∩ C).card) :
    2 * s ≤ (A ∩ B).card + C.card := by
  have hsub : (A ∩ C) ∪ (B ∩ C) ⊆ C := by
    intro x hx
    simp only [mem_union, mem_inter] at hx
    tauto
  have hle : ((A ∩ C) ∪ (B ∩ C)).card ≤ C.card := card_le_card hsub
  have hue : ((A ∩ C) ∪ (B ∩ C)).card + ((A ∩ C) ∩ (B ∩ C)).card
      = (A ∩ C).card + (B ∩ C).card := card_union_add_card_inter _ _
  have hinter : (A ∩ C) ∩ (B ∩ C) ⊆ A ∩ B := by
    intro x hx
    simp only [mem_inter] at hx ⊢
    tauto
  have hle2 : ((A ∩ C) ∩ (B ∩ C)).card ≤ (A ∩ B).card := card_le_card hinter
  omega

/-!
## Counting subsets by their intersection with the core
-/

/-- **Split count.** Inside a ground set `G`, the number of `k`-subsets meeting a
fixed `C ⊆ G` in exactly `j` points is `C(|C|, j) · C(|G \ C|, k − j)`.
Proved by the bijection `S ↦ (S ∩ C, S \ C)`. -/
theorem card_filter_inter_card_eq {G C : Finset α} (hC : C ⊆ G) {k j : ℕ}
    (hjk : j ≤ k) :
    ((G.powersetCard k).filter (fun S => (S ∩ C).card = j)).card
      = C.card.choose j * (G \ C).card.choose (k - j) := by
  have hrhs : C.card.choose j * (G \ C).card.choose (k - j)
      = ((C.powersetCard j) ×ˢ ((G \ C).powersetCard (k - j))).card := by
    rw [card_product, card_powersetCard, card_powersetCard]
  rw [hrhs]
  apply card_nbij' (fun S => (S ∩ C, S \ C)) (fun p => p.1 ∪ p.2)
  · -- forward maps to the product
    intro S hS
    simp only [mem_coe, mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSG, hScard⟩, hSj⟩ := hS
    have hcard : (S ∩ C).card + (S \ C).card = k := by
      rw [card_inter_add_card_sdiff, hScard]
    have hsdiff : S \ C ⊆ G \ C := by
      intro x hx
      simp only [mem_sdiff] at hx ⊢
      exact ⟨hSG hx.1, hx.2⟩
    simp only [mem_coe, mem_product, mem_powersetCard]
    refine ⟨⟨inter_subset_right, hSj⟩, hsdiff, ?_⟩
    omega
  · -- backward maps into the filtered powerset
    intro p hp
    simp only [mem_coe, mem_product, mem_powersetCard] at hp
    obtain ⟨⟨hA, hAj⟩, hB, hBkj⟩ := hp
    have hdisj : Disjoint p.1 p.2 := by
      refine disjoint_left.2 ?_
      intro x hx1 hx2
      exact (mem_sdiff.1 (hB hx2)).2 (hA hx1)
    have hinterC : (p.1 ∪ p.2) ∩ C = p.1 := by
      ext x
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨h1 | h2, hxC⟩
        · exact h1
        · exact absurd hxC (mem_sdiff.1 (hB h2)).2
      · intro hx1
        exact ⟨Or.inl hx1, hA hx1⟩
    simp only [mem_coe, mem_filter, mem_powersetCard]
    refine ⟨⟨union_subset (hA.trans hC) (hB.trans sdiff_subset), ?_⟩, ?_⟩
    · rw [card_union_of_disjoint hdisj, hAj, hBkj]
      omega
    · rw [hinterC, hAj]
  · -- left inverse: `(S ∩ C) ∪ (S \ C) = S`
    intro S _
    simp only
    rw [union_comm]
    exact sdiff_union_inter S C
  · -- right inverse: `((A ∪ B) ∩ C, (A ∪ B) \ C) = (A, B)`
    intro p hp
    simp only [mem_coe, mem_product, mem_powersetCard] at hp
    obtain ⟨⟨hA, _⟩, hB, _⟩ := hp
    have hinterC : (p.1 ∪ p.2) ∩ C = p.1 := by
      ext x
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨h1 | h2, hxC⟩
        · exact h1
        · exact absurd hxC (mem_sdiff.1 (hB h2)).2
      · intro hx1
        exact ⟨Or.inl hx1, hA hx1⟩
    have hsdiffC : (p.1 ∪ p.2) \ C = p.2 := by
      ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h1 | h2, hxC⟩
        · exact absurd (hA h1) hxC
        · exact h2
      · intro hx2
        exact ⟨Or.inr hx2, (mem_sdiff.1 (hB hx2)).2⟩
    rw [Prod.ext_iff]
    exact ⟨hinterC, hsdiffC⟩

/-!
## The main result: the bound is sharp
-/

/-- **Erdős #83, lower bound (sharpness).** The Ahlswede–Khachatrian bound is
achieved: there is a valid `2`-intersecting family of `2n`-subsets of `[4n]`
whose cardinality is exactly `erdos83Bound n`. -/
theorem erdos83_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ F : Finset (Finset (Fin (4 * n))),
      IsValidErdos83Family n F ∧ F.card = erdos83Bound n := by
  have huniv : (univ : Finset (Fin (4 * n))).card = 4 * n := by
    rw [Finset.card_univ, Fintype.card_fin]
  obtain ⟨C, hCsub, hCcard⟩ :=
    exists_subset_card_eq (s := (univ : Finset (Fin (4 * n)))) (n := 2 * n)
      (by rw [huniv]; omega)
  set P : Finset (Finset (Fin (4 * n))) := univ.powersetCard (2 * n) with hP
  set F : Finset (Finset (Fin (4 * n))) :=
    P.filter (fun S => n + 1 ≤ (S ∩ C).card) with hF
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · -- `2n`-uniform
    intro A hA
    simp only [hF, hP, mem_filter, mem_powersetCard] at hA
    exact hA.1.2
  · -- `2`-intersecting
    intro A hA B hB
    simp only [hF, hP, mem_filter, mem_powersetCard] at hA hB
    have key := two_mul_le_card_inter_add_core hA.2 hB.2
    rw [hCcard] at key
    omega
  · -- the count equals `erdos83Bound n`
    set L : Finset (Finset (Fin (4 * n))) :=
      P.filter (fun S => (S ∩ C).card < n) with hL
    set M : Finset (Finset (Fin (4 * n))) :=
      P.filter (fun S => (S ∩ C).card = n) with hM
    -- `|P| = C(4n, 2n)`
    have hcardP : P.card = (4 * n).choose (2 * n) := by
      rw [hP, card_powersetCard, huniv]
    -- `|M| = C(2n, n)²`
    have hcardM : M.card = ((2 * n).choose n) ^ 2 := by
      have hcount := card_filter_inter_card_eq (G := (univ : Finset (Fin (4 * n))))
        (C := C) hCsub (k := 2 * n) (j := n) (by omega)
      have hGC : ((univ : Finset (Fin (4 * n))) \ C).card = 2 * n := by
        rw [card_univ_diff, Fintype.card_fin, hCcard]; omega
      have hsub2 : 2 * n - n = n := by omega
      rw [hM, hP, hcount, hCcard, hGC, hsub2]
      ring
    -- complement involution gives `|F| = |L|`
    have hcompl : F.card = L.card := by
      apply card_nbij' (fun S => Sᶜ) (fun S => Sᶜ)
      · intro S hS
        simp only [mem_coe, hF, hP, mem_filter, mem_powersetCard] at hS
        obtain ⟨⟨_, hScard⟩, hSge⟩ := hS
        have hcc : (Sᶜ ∩ C).card = 2 * n - (S ∩ C).card := by
          have heq : Sᶜ ∩ C = C \ S := by
            ext x; simp only [mem_inter, mem_compl, mem_sdiff]; tauto
          rw [heq, card_sdiff, hCcard]
        simp only [mem_coe, hL, hP, mem_filter, mem_powersetCard]
        refine ⟨⟨subset_univ _, ?_⟩, ?_⟩
        · rw [card_compl, Fintype.card_fin, hScard]; omega
        · rw [hcc]; omega
      · intro S hS
        simp only [mem_coe, hL, hP, mem_filter, mem_powersetCard] at hS
        obtain ⟨⟨_, hScard⟩, hSlt⟩ := hS
        have hcc : (Sᶜ ∩ C).card = 2 * n - (S ∩ C).card := by
          have heq : Sᶜ ∩ C = C \ S := by
            ext x; simp only [mem_inter, mem_compl, mem_sdiff]; tauto
          rw [heq, card_sdiff, hCcard]
        simp only [mem_coe, hF, hP, mem_filter, mem_powersetCard]
        refine ⟨⟨subset_univ _, ?_⟩, ?_⟩
        · rw [card_compl, Fintype.card_fin, hScard]; omega
        · rw [hcc]; omega
      · intro S _; simp
      · intro S _; simp
    -- partition `P = F ⊔ M ⊔ L`
    have h1 : P.card
        = F.card + (P.filter (fun S => ¬ n + 1 ≤ (S ∩ C).card)).card := by
      rw [hF]
      exact (filter_card_add_filter_neg_card_eq_card _).symm
    have h2 : (P.filter (fun S => ¬ n + 1 ≤ (S ∩ C).card)).card = M.card + L.card := by
      have e := filter_card_add_filter_neg_card_eq_card
        (s := P.filter (fun S => ¬ n + 1 ≤ (S ∩ C).card))
        (fun S => (S ∩ C).card = n)
      have eM : (P.filter (fun S => ¬ n + 1 ≤ (S ∩ C).card)).filter
          (fun S => (S ∩ C).card = n) = M := by
        rw [hM, filter_filter]
        apply filter_congr
        intro S _
        omega
      have eL : (P.filter (fun S => ¬ n + 1 ≤ (S ∩ C).card)).filter
          (fun S => ¬ (S ∩ C).card = n) = L := by
        rw [hL, filter_filter]
        apply filter_congr
        intro S _
        omega
      rw [eM, eL] at e
      omega
    have hLF : L.card = F.card := hcompl.symm
    have hkey : (4 * n).choose (2 * n) = 2 * F.card + ((2 * n).choose n) ^ 2 := by
      rw [← hcardP]; omega
    show F.card = erdos83Bound n
    unfold erdos83Bound
    omega
