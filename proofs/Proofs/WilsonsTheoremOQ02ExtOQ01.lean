import Mathlib.Tactic
import Proofs.WilsonsTheoremOQ02Ext

/-
# Gauss-Wilson Theorem: General Finite Abelian Group (OQ-02-ext OQ-01)

**Open question (`wilsons-theorem-oq-02-ext-oq-01`):** Can the two-involution
trick be formalized as a *general* theorem about finite abelian groups, rather
than only the unit group `(ZMod n)ˣ`?

**Answer: yes.** The companion file `WilsonsTheoremOQ02Ext.lean` already proves
the two-involution trick for `(ZMod n)ˣ` (`prod_units_one_of_not_cyclic_ext`).
Inspecting that proof, every step from `prod_eq_prod_sq_eq_one` onward is stated
for an arbitrary `[CommGroup G] [Fintype G] [DecidableEq G]`. The *only*
`(ZMod n)`-specific ingredient is the derivation of `3 ≤ |{x | x² = 1}|` from
`¬ IsCyclic (ZMod n)ˣ` (via `GaussWilsonNonCyclic`, CRT and the `2^k` case
analysis). The general theorem simply takes that cardinality bound as a
*hypothesis*, and is therefore strictly more elementary than the specialization.

## Main results

* `prod_eq_one_of_three_le_card_sqrt_one` — **the general two-involution
  theorem**: if `G` has at least three square roots of `1`, then `∏ x = 1`.
* `prod_eq_one_of_no_involution` — if `G` has no element of order two,
  `∏ x = 1`.
* `prod_eq_unique_involution` — if `G` has a unique element `t` of order two,
  `∏ x = t`.
* `prod_eq_one_or_unique_involution` — **full Gauss-Wilson characterization**:
  the product of all elements of a finite abelian group is the unique element
  of order two if one exists, and `1` otherwise.

The cardinality `|{x | x² = 1}|` is always a power of two (the square-roots of
`1` form an elementary abelian 2-group), so the case `|S| = 3` never occurs;
nonetheless the `3 ≤ |S|` hypothesis is all the two-involution trick needs.
-/

namespace WilsonsTheoremOQ02ExtOQ01

open Finset

/-- **Involution helper** (general `CommGroup` form, copied from the private
    helper in `WilsonsTheoremOQ02Ext`). For `c` with `c² = 1` and `c ≠ 1`, the
    map `x ↦ c * x` is a fixed-point-free involution on `S = {x | x² = 1}` with
    constant pair product `c`. -/
theorem mul_involution_on_sq_eq_one {G : Type*} [CommGroup G] [DecidableEq G]
    {c : G} (hc_sq : c ^ 2 = 1) (hc_ne : c ≠ 1) :
    let S := Finset.univ.filter (fun x : G => x ^ 2 = 1)
    (∀ x ∈ S, c * x ∈ S) ∧
    (∀ x ∈ S, c * (c * x) = x) ∧
    (∀ x ∈ S, c * x ≠ x) ∧
    (∀ x ∈ S, x * (c * x) = c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact WilsonsTheoremOQ02Ext.mul_sq_eq_one hc_sq hx
  · intro x _; rw [← mul_assoc, ← sq, hc_sq, one_mul]
  · intro x _ h; exact hc_ne (mul_right_cancel h)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [mul_comm x (c * x), mul_assoc, ← sq, hx, mul_one]

/-- **General two-involution theorem.** In a finite abelian group with at least
    three square roots of `1`, the product of all elements is `1`.

    This is the abstract content of the two-involution trick: the proof body is
    the `(ZMod n)ˣ` proof `prod_units_one_of_not_cyclic_ext`, with the
    cardinality bound supplied as a hypothesis instead of derived from
    non-cyclicity. -/
theorem prod_eq_one_of_three_le_card_sqrt_one
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (hS_card : 3 ≤ (Finset.univ.filter (fun x : G => x ^ 2 = 1)).card) :
    ∏ x : G, x = 1 := by
  rw [WilsonsTheoremOQ02Ext.prod_eq_prod_sq_eq_one]
  set S := Finset.univ.filter (fun x : G => x ^ 2 = 1)
  have hS_mem_sq : ∀ x ∈ S, x ^ 2 = 1 := fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx
  -- Pick c ∈ S \ {1}
  have hS_sub1_nonempty : (S \ {1}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hempty
    have hsub : S ⊆ {1} := by
      intro x hx; by_contra hxne
      exact Finset.not_mem_empty x (hempty ▸ Finset.mem_sdiff.mpr ⟨hx, hxne⟩)
    have := Finset.card_le_card hsub; simp at this; omega
  obtain ⟨c, hc_mem⟩ := hS_sub1_nonempty
  have hc_in_S : c ∈ S := (Finset.mem_sdiff.mp hc_mem).1
  have hc_ne_1 : c ≠ 1 := by intro h; exact (Finset.mem_sdiff.mp hc_mem).2 (by simp [h])
  have hc_sq : c ^ 2 = 1 := hS_mem_sq c hc_in_S
  -- Pick d ∈ S \ {1, c}
  have hS_sub2_nonempty : (S \ {1, c}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hempty
    have hsub : S ⊆ {1, c} := by
      intro x hx; by_contra hxne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxne; push_neg at hxne
      exact Finset.not_mem_empty x (hempty ▸ Finset.mem_sdiff.mpr ⟨hx, by
        simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact hxne⟩)
    have h1 := Finset.card_le_card hsub
    have h2 : ({1, c} : Finset G).card ≤ 2 := Finset.card_insert_le _ _
    omega
  obtain ⟨d, hd_mem⟩ := hS_sub2_nonempty
  have hd_in_S : d ∈ S := (Finset.mem_sdiff.mp hd_mem).1
  have hd_ne_1 : d ≠ 1 := by intro h; exact (Finset.mem_sdiff.mp hd_mem).2 (by simp [h])
  have hd_ne_c : d ≠ c := by intro h; exact (Finset.mem_sdiff.mp hd_mem).2 (by simp [h])
  have hd_sq : d ^ 2 = 1 := hS_mem_sq d hd_in_S
  -- c * d ≠ 1
  have hcd_sq : (c * d) ^ 2 = 1 := WilsonsTheoremOQ02Ext.mul_sq_eq_one hc_sq hd_sq
  have hcd_ne_1 : c * d ≠ 1 := by
    intro h
    have hdc : d = c⁻¹ := by rwa [mul_eq_one_iff_eq_inv] at h
    have : d = c := by
      rw [hdc, inv_eq_of_mul_eq_one_right]; rw [← sq]; exact hc_sq
    exact hd_ne_c this
  -- Involution data for c, d, cd
  obtain ⟨hσc_mem, hσc_inv, hσc_ne, hσc_prod⟩ := mul_involution_on_sq_eq_one hc_sq hc_ne_1
  obtain ⟨hσd_mem, hσd_inv, hσd_ne, hσd_prod⟩ := mul_involution_on_sq_eq_one hd_sq hd_ne_1
  obtain ⟨hσcd_mem, hσcd_inv, hσcd_ne, hσcd_prod⟩ :=
    mul_involution_on_sq_eq_one hcd_sq hcd_ne_1
  -- ∏ S equals c^k, d^k and (cd)^k where k = |S|/2
  have hP_eq_c : ∏ x ∈ S, x = c ^ (S.card / 2) :=
    WilsonsTheoremOQ02Ext.prod_involution_const hσc_mem hσc_inv hσc_ne hσc_prod
  have hP_eq_d : ∏ x ∈ S, x = d ^ (S.card / 2) :=
    WilsonsTheoremOQ02Ext.prod_involution_const hσd_mem hσd_inv hσd_ne hσd_prod
  have hP_eq_cd : ∏ x ∈ S, x = (c * d) ^ (S.card / 2) :=
    WilsonsTheoremOQ02Ext.prod_involution_const hσcd_mem hσcd_inv hσcd_ne hσcd_prod
  -- Two-involution trick: c^k = (cd)^k ⟹ d^k = 1 ⟹ c^k = 1
  have hd_pow : d ^ (S.card / 2) = 1 := by
    have h : c ^ (S.card / 2) = (c * d) ^ (S.card / 2) := by rw [← hP_eq_c, hP_eq_cd]
    rw [mul_pow] at h
    exact mul_left_cancel (a := c ^ (S.card / 2)) (by rwa [mul_one])
  have hc_pow : c ^ (S.card / 2) = 1 := by rw [hP_eq_c, hP_eq_d, hd_pow]
  rw [hP_eq_c, hc_pow]

/-- If a finite abelian group has no element of order two, the product of all
    its elements is `1`. -/
theorem prod_eq_one_of_no_involution
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (h : ∀ s : G, s ^ 2 = 1 → s = 1) :
    ∏ x : G, x = 1 := by
  rw [WilsonsTheoremOQ02Ext.prod_eq_prod_sq_eq_one]
  have hS : Finset.univ.filter (fun x : G => x ^ 2 = 1) = {1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨by simp only [Finset.mem_filter, Finset.mem_univ, true_and, one_pow], ?_⟩
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact h x hx
  rw [hS, Finset.prod_singleton]

/-- If a finite abelian group has a unique element `t` of order two, the product
    of all its elements is `t`. -/
theorem prod_eq_unique_involution
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {t : G} (ht_ne : t ≠ 1) (ht_sq : t ^ 2 = 1)
    (huniq : ∀ s : G, s ^ 2 = 1 → s = 1 ∨ s = t) :
    ∏ x : G, x = t := by
  rw [WilsonsTheoremOQ02Ext.prod_eq_prod_sq_eq_one]
  have hS : Finset.univ.filter (fun x : G => x ^ 2 = 1) = {1, t} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine ⟨fun hx => huniq x hx, ?_⟩
    rintro (rfl | rfl)
    · simp
    · exact ht_sq
  rw [hS, Finset.prod_pair (Ne.symm ht_ne), one_mul]

/-- **Full Gauss-Wilson characterization for finite abelian groups.** The
    product of all elements of a finite abelian group is the unique element of
    order two if such an element exists, and `1` otherwise. -/
theorem prod_eq_one_or_unique_involution
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] :
    (∏ x : G, x = 1) ∨
      (∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧
        (∀ s : G, s ^ 2 = 1 → s = 1 ∨ s = t) ∧ ∏ x : G, x = t) := by
  by_cases h1 : ∀ s : G, s ^ 2 = 1 → s = 1
  · exact Or.inl (prod_eq_one_of_no_involution h1)
  · push_neg at h1
    obtain ⟨t, ht_sq, ht_ne⟩ := h1
    by_cases huniq : ∀ s : G, s ^ 2 = 1 → s = 1 ∨ s = t
    · exact Or.inr ⟨t, ht_ne, ht_sq, huniq, prod_eq_unique_involution ht_ne ht_sq huniq⟩
    · -- A second non-identity involution `u` exists ⟹ |{x | x²=1}| ≥ 3
      push_neg at huniq
      obtain ⟨u, hu_sq, hu_ne1, hu_net⟩ := huniq
      have hcard : 3 ≤ (Finset.univ.filter (fun x : G => x ^ 2 = 1)).card := by
        have h1m : (1 : G) ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, one_pow]
        have htm : t ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ht_sq
        have hum : u ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hu_sq
        have hsub : ({1, t, u} : Finset G) ⊆
            Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact h1m
          · exact htm
          · exact hum
        have hcard3 : ({1, t, u} : Finset G).card = 3 := by
          rw [Finset.card_insert_of_not_mem (by simp [Ne.symm ht_ne, Ne.symm hu_ne1])]
          rw [Finset.card_insert_of_not_mem (by simp [Ne.symm hu_net])]
          simp
        have hle := Finset.card_le_card hsub
        omega
      exact Or.inl (prod_eq_one_of_three_le_card_sqrt_one hcard)

end WilsonsTheoremOQ02ExtOQ01
