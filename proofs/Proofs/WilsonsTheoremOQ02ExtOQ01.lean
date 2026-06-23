import Mathlib.Tactic
import Proofs.WilsonsTheoremOQ02Ext

/-
# OQ-01: The Two-Involution Trick as a General Theorem (Miller's Theorem)

`WilsonsTheoremOQ02Ext.lean` proves the Gauss–Wilson product law for the
specific group `(ZMod n)ˣ`, using the **two-involution trick** on the
2-torsion subgroup `S = {x | x² = 1}`. The trick itself — three applications
of `prod_involution_const` — never uses anything about `(ZMod n)ˣ`; only the
derivation of `|S| ≥ 3` is number-theoretic.

This file extracts the trick as a theorem about **arbitrary finite abelian
groups**, answering OQ-01. The headline statement is the classical

> **Miller's theorem (1903).** In a finite abelian group `G`, the product of
> all elements is `1`, unless `G` has a unique element of order `2`, in which
> case the product is that element.

## Main results
- `prod_eq_one_of_two_torsion_card_ge_three`: `|S| ≥ 3 ⟹ ∏ G = 1`
  (the two-involution trick, fully general — the direct OQ-01 answer).
- `prod_eq_one_of_card_ne_two`: `|S| ≠ 2 ⟹ ∏ G = 1` (folds in the trivial
  `|S| ∈ {0,1}` cases).
- `prod_eq_unique_involution`: a unique involution `t ⟹ ∏ G = t`.
- `miller_prod`: the full Miller disjunction.
- `gaussWilson_general`: `∏ G = -1` is impossible unless `G` has a unique
  involution, i.e. the `(ZMod n)ˣ` case is the *only* way to get `-1`.

All proofs reuse the **group-general** lemmas already proven in
`WilsonsTheoremOQ02Ext`:
`prod_eq_prod_sq_eq_one`, `prod_involution_const`, `mul_sq_eq_one`.
-/

namespace WilsonsTheoremOQ02ExtOQ01

open Finset
open WilsonsTheoremOQ02Ext (prod_eq_prod_sq_eq_one prod_involution_const mul_sq_eq_one)

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **Two-involution helper** (general `CommGroup` version). For `c` in the
2-torsion subgroup with `c ≠ 1`, the map `x ↦ c * x` is a fixed-point-free
involution on `S = {x | x² = 1}` with constant pair product `c`.

This is the group-general copy of the (private) helper from
`WilsonsTheoremOQ02Ext`. -/
private theorem mul_involution_on_sq_eq_one
    {c : G} (hc_sq : c ^ 2 = 1) (hc_ne : c ≠ 1) :
    let S := univ.filter (fun x : G => x ^ 2 = 1)
    (∀ x ∈ S, c * x ∈ S) ∧
    (∀ x ∈ S, c * (c * x) = x) ∧
    (∀ x ∈ S, c * x ≠ x) ∧
    (∀ x ∈ S, x * (c * x) = c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact mul_sq_eq_one hc_sq hx
  · intro x _; rw [← mul_assoc, ← sq, hc_sq, one_mul]
  · intro x _ h; exact hc_ne (mul_right_cancel h)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [mul_comm x (c * x), mul_assoc, ← sq, hx, mul_one]

/-- **The two-involution trick, generalized.** If the 2-torsion subgroup
`S = {x | x² = 1}` of a finite abelian group has at least three elements,
then the product of *all* group elements is `1`.

This is a verbatim generalization of
`WilsonsTheoremOQ02Ext.prod_units_one_of_not_cyclic_ext`: the
`(ZMod n)ˣ`-specific cardinality bound is replaced by the hypothesis
`hcard`, and the coercion wrapper is dropped. -/
theorem prod_eq_one_of_two_torsion_card_ge_three
    (hcard : 3 ≤ (univ.filter (fun x : G => x ^ 2 = 1)).card) :
    ∏ x : G, x = 1 := by
  rw [prod_eq_prod_sq_eq_one]
  set S := univ.filter (fun x : G => x ^ 2 = 1) with hS_def
  have hS_mem_sq : ∀ x ∈ S, x ^ 2 = 1 := fun x hx => by
    simp only [hS_def, mem_filter, mem_univ, true_and] at hx; exact hx
  -- Pick c ∈ S \ {1}
  have hS_sub1_nonempty : (S \ {1}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hempty
    have : S ⊆ {1} := by
      intro x hx; by_contra hxne
      exact Finset.not_mem_empty x (hempty ▸ Finset.mem_sdiff.mpr ⟨hx, hxne⟩)
    have := Finset.card_le_card this; simp at this; omega
  obtain ⟨c, hc_mem⟩ := hS_sub1_nonempty
  have hc_in_S : c ∈ S := (Finset.mem_sdiff.mp hc_mem).1
  have hc_ne_1 : c ≠ 1 := by intro h; exact (Finset.mem_sdiff.mp hc_mem).2 (by simp [h])
  have hc_sq : c ^ 2 = 1 := hS_mem_sq c hc_in_S
  -- Pick d ∈ S \ {1, c}
  have hS_sub2_nonempty : (S \ {1, c}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hempty
    have : S ⊆ {1, c} := by
      intro x hx; by_contra hxne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxne; push_neg at hxne
      exact Finset.not_mem_empty x (hempty ▸ Finset.mem_sdiff.mpr ⟨hx, by
        simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact hxne⟩)
    have := Finset.card_le_card this
    have : ({1, c} : Finset G).card ≤ 2 := Finset.card_insert_le _ _
    omega
  obtain ⟨d, hd_mem⟩ := hS_sub2_nonempty
  have hd_in_S : d ∈ S := (Finset.mem_sdiff.mp hd_mem).1
  have hd_ne_1 : d ≠ 1 := by intro h; exact (Finset.mem_sdiff.mp hd_mem).2 (by simp [h])
  have hd_ne_c : d ≠ c := by intro h; exact (Finset.mem_sdiff.mp hd_mem).2 (by simp [h])
  have hd_sq : d ^ 2 = 1 := hS_mem_sq d hd_in_S
  have hcd_sq : (c * d) ^ 2 = 1 := mul_sq_eq_one hc_sq hd_sq
  have hcd_ne_1 : c * d ≠ 1 := by
    intro h
    have : d = c⁻¹ := by rwa [mul_eq_one_iff_eq_inv] at h
    have : d = c := by rw [this, inv_eq_of_mul_eq_one_right]; rw [← sq]; exact hc_sq
    exact hd_ne_c this
  -- Involution data for c, d, cd
  obtain ⟨hσc_mem, hσc_inv, hσc_ne, hσc_prod⟩ := mul_involution_on_sq_eq_one hc_sq hc_ne_1
  obtain ⟨hσd_mem, hσd_inv, hσd_ne, hσd_prod⟩ := mul_involution_on_sq_eq_one hd_sq hd_ne_1
  obtain ⟨hσcd_mem, hσcd_inv, hσcd_ne, hσcd_prod⟩ := mul_involution_on_sq_eq_one hcd_sq hcd_ne_1
  have hP_eq_c : ∏ x ∈ S, x = c ^ (S.card / 2) :=
    prod_involution_const hσc_mem hσc_inv hσc_ne hσc_prod
  have hP_eq_d : ∏ x ∈ S, x = d ^ (S.card / 2) :=
    prod_involution_const hσd_mem hσd_inv hσd_ne hσd_prod
  have hP_eq_cd : ∏ x ∈ S, x = (c * d) ^ (S.card / 2) :=
    prod_involution_const hσcd_mem hσcd_inv hσcd_ne hσcd_prod
  -- Two-involution trick: c^k = (cd)^k ⟹ d^k = 1
  have hd_pow : d ^ (S.card / 2) = 1 := by
    have h : c ^ (S.card / 2) = (c * d) ^ (S.card / 2) := by rw [← hP_eq_c, hP_eq_cd]
    rw [mul_pow] at h
    exact mul_left_cancel (a := c ^ (S.card / 2)) (by rwa [mul_one])
  have hc_pow : c ^ (S.card / 2) = 1 := by rw [hP_eq_c, hP_eq_d, hd_pow]
  rw [hP_eq_c, hc_pow]

/-- If the 2-torsion subgroup has size `≠ 2`, the product of all elements is `1`.
Folds the trivial `|S| = 0` (impossible) and `|S| = 1` cases into the trick. -/
theorem prod_eq_one_of_card_ne_two
    (hcard : (univ.filter (fun x : G => x ^ 2 = 1)).card ≠ 2) :
    ∏ x : G, x = 1 := by
  set S := univ.filter (fun x : G => x ^ 2 = 1) with hS_def
  have h1_mem : (1 : G) ∈ S := by simp [hS_def, mem_filter, sq]
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨1, h1_mem⟩
  rcases lt_or_ge S.card 2 with hlt | hge
  · -- S.card = 1 ⟹ S = {1}
    have hcard1 : S.card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    have hae : a = 1 := by
      rw [ha, Finset.mem_singleton] at h1_mem; exact h1_mem.symm
    rw [prod_eq_prod_sq_eq_one, ← hS_def, ha, hae, Finset.prod_singleton]
  · -- S.card ≥ 2 and ≠ 2 ⟹ ≥ 3
    have hge3 : 3 ≤ S.card := by omega
    exact prod_eq_one_of_two_torsion_card_ge_three hge3

/-- **Unique-involution case.** If `t` is the *unique* element of order `2`,
the product of all group elements equals `t`. -/
theorem prod_eq_unique_involution
    {t : G} (ht_ne : t ≠ 1) (ht_sq : t ^ 2 = 1)
    (huniq : ∀ s : G, s ^ 2 = 1 → s = 1 ∨ s = t) :
    ∏ x : G, x = t := by
  set S := univ.filter (fun x : G => x ^ 2 = 1) with hS_def
  have hsub : S ⊆ {1, t} := by
    intro x hx
    simp only [hS_def, mem_filter, mem_univ, true_and] at hx
    rcases huniq x hx with rfl | rfl <;> simp
  have hsup : ({1, t} : Finset G) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [hS_def, mem_filter, sq]
    · simp only [hS_def, mem_filter, mem_univ, true_and]; exact ht_sq
  have hSeq : S = {1, t} := Finset.Subset.antisymm hsub hsup
  rw [prod_eq_prod_sq_eq_one, ← hS_def, hSeq, Finset.prod_pair ht_ne.symm, one_mul]

/-- **Miller's theorem (1903).** In a finite abelian group, the product of all
elements is `1`, unless the group has a unique element of order `2`, in which
case the product is that element. -/
theorem miller_prod :
    (∏ x : G, x = 1) ∨
    (∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ (∀ s : G, s ^ 2 = 1 → s = 1 ∨ s = t)
        ∧ ∏ x : G, x = t) := by
  set S := univ.filter (fun x : G => x ^ 2 = 1) with hS_def
  by_cases hc2 : S.card = 2
  · -- exactly one involution: S = {1, t}
    right
    have h1_mem : (1 : G) ∈ S := by simp [hS_def, mem_filter, sq]
    -- the second element of the pair is the involution
    obtain ⟨t, hne, hSeq⟩ : ∃ t : G, t ≠ 1 ∧ S = {1, t} := by
      obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hc2
      rw [hS] at h1_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1_mem
      rcases h1_mem with rfl | rfl
      · exact ⟨b, fun h => hab (by rw [h]), hS⟩
      · exact ⟨a, fun h => hab (by rw [h]), by rw [hS, Finset.pair_comm]⟩
    have ht_sq : t ^ 2 = 1 := by
      have : t ∈ S := by rw [hSeq]; simp
      simp only [hS_def, mem_filter, mem_univ, true_and] at this; exact this
    have huniq : ∀ s : G, s ^ 2 = 1 → s = 1 ∨ s = t := by
      intro s hs
      have : s ∈ S := by simp only [hS_def, mem_filter, mem_univ, true_and]; exact hs
      rw [hSeq] at this; simpa using this
    exact ⟨t, hne, ht_sq, huniq, prod_eq_unique_involution hne ht_sq huniq⟩
  · left; exact prod_eq_one_of_card_ne_two (hS_def ▸ hc2)

/-- **The `(ZMod n)ˣ` law is subsumed.** A finite abelian group's element
product is `-1`-like (a non-identity value) only via a *unique* involution;
the gallery's `gaussWilson_abstract_ext` is the instance `G = (ZMod n)ˣ`,
where the unique involution is `-1` precisely when the group is cyclic. -/
theorem prod_ne_one_iff_unique_involution :
    (∏ x : G, x ≠ 1) ↔
    (∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ s : G, s ^ 2 = 1 → s = 1 ∨ s = t) := by
  constructor
  · intro hne
    rcases miller_prod (G := G) with h | ⟨t, ht_ne, ht_sq, huniq, _⟩
    · exact absurd h hne
    · exact ⟨t, ht_ne, ht_sq, huniq⟩
  · rintro ⟨t, ht_ne, ht_sq, huniq⟩
    rw [prod_eq_unique_involution ht_ne ht_sq huniq]
    exact ht_ne

#check @prod_eq_one_of_two_torsion_card_ge_three
#check @miller_prod
#check @prod_eq_unique_involution

end WilsonsTheoremOQ02ExtOQ01
