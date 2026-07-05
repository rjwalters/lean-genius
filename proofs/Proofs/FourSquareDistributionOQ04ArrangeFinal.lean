import Mathlib
import Proofs.FourSquareDistributionOQ04Surj

/-
# Four-Square Distribution — OQ-04: the arrangement-count residue, discharged

This file closes the single open combinatorial residue of the OQ-04
generalization, `arrangement_card`:

  `(arrangements s).card = Nat.multinomial s.toFinset s.count = m! / ∏_v (count_v)!`,

where `arrangements s = { g : Fin m → ℤ | multiset(g) = s }`. Prior sessions
reduced the entire open question (`fiber_card_eq_contribution` in
`…OQ04Decomp/Sign/Keystone`) to exactly this count, and flagged the orbit
–surjectivity step ("two tuples with equal value-multiset differ by a
permutation") as the genuine blocker with no direct Mathlib lemma.

That blocker is discharged by `FourSquareDistributionOQ04Surj.exists_perm_comp`
(via `Tuple.sort` + sorted-list uniqueness). This file assembles the rest by
orbit–stabilizer counting of the precomposition action of `Equiv.Perm (Fin m)`:

* `stabilizer_card_eq_prod_count` — the stabilizer of an arrangement has order
  `∏_v (count_v)!`, via `DomMulAct.stabilizer_card'`;
* `comp_perm_mem` — precomposition preserves the arrangement set;
* `fiber_card` — every fiber of `σ ↦ g₀ ∘ σ` over `arrangements s` has size
  `∏_v (count_v)!` (translate of the stabilizer by a surjectivity witness);
* `arrangements_card_mul_prod_count` — `card(arrangements) · ∏count! = m!`
  (fiberwise count of `Equiv.Perm (Fin m)`, `Fintype.card_perm`);
* `arrangement_card` — the `Nat.multinomial` headline, by `Nat.multinomial_spec`.

All Mathlib API name-checked against the project pin (`2df2f0150c`, v4.26.0).
-/

namespace FourSquareDistributionOQ04ArrangeFinal

open Finset

/-- Arrangements of a multiset `s` as functions `Fin m → ℤ` (verbatim from the
parent `…Arrange.lean`). -/
def arrangements {m : ℕ} (s : Multiset ℤ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset (fun _ : Fin m => s.toFinset)).filter
    (fun g => Multiset.map g (Finset.univ : Finset (Fin m)).val = s)

theorem mem_arrangements_iff {m : ℕ} (s : Multiset ℤ) (g : Fin m → ℤ) :
    g ∈ arrangements s ↔ Multiset.map g (Finset.univ : Finset (Fin m)).val = s := by
  classical
  simp only [arrangements, Finset.mem_filter, Fintype.mem_piFinset, Multiset.mem_toFinset]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨fun i => ?_, h⟩
    rw [← h]
    exact Multiset.mem_map_of_mem g (Finset.mem_val.mpr (Finset.mem_univ i))

/-- The image of an arrangement is exactly `s.toFinset`. -/
theorem image_eq_toFinset_of_mem {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) :
    (Finset.univ : Finset (Fin m)).image g = s.toFinset := by
  classical
  rw [mem_arrangements_iff] at hg
  rw [← hg, Multiset.toFinset_map, Finset.val_toFinset]

/-- The `i`-fiber of an arrangement has size `s.count i`. -/
theorem card_fiber_eq_count {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) (i : ℤ) :
    Fintype.card {a : Fin m // g a = i} = s.count i := by
  classical
  rw [mem_arrangements_iff] at hg
  have hfeq : (Finset.univ : Finset (Fin m)).val.filter (fun a : Fin m => g a = i)
      = (Finset.univ : Finset (Fin m)).val.filter (fun a : Fin m => i = g a) :=
    Multiset.filter_congr (fun a _ => eq_comm)
  rw [Fintype.card_subtype, ← hg, Multiset.count_map, Finset.card_def, Finset.filter_val, hfeq]

/-- **Stabilizer order = ∏ count!** for an arrangement `g`, from
`DomMulAct.stabilizer_card'`. -/
theorem stabilizer_card_eq_prod_count {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) :
    Fintype.card {σ : Equiv.Perm (Fin m) // g ∘ σ = g}
      = ∏ v ∈ s.toFinset, (s.count v)! := by
  classical
  rw [DomMulAct.stabilizer_card' (f := g), image_eq_toFinset_of_mem s hg]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [card_fiber_eq_count s hg v]

/-- Precomposition by a permutation preserves arrangement membership. -/
theorem comp_perm_mem {m : ℕ} {s : Multiset ℤ} {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) (σ : Equiv.Perm (Fin m)) :
    g ∘ σ ∈ arrangements s := by
  rw [mem_arrangements_iff] at hg ⊢
  rw [← hg, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- **Every fiber has size `∏ count!`.** For `h ∈ arrangements s`, the fiber of
`σ ↦ g₀ ∘ σ` over `h` is a translate of the stabilizer of `g₀` (by a
surjectivity witness `ρ` with `g₀ ∘ ρ = h`), hence has the stabilizer's order. -/
theorem fiber_card {m : ℕ} (s : Multiset ℤ) {g₀ : Fin m → ℤ}
    (hg₀ : g₀ ∈ arrangements s) {h : Fin m → ℤ} (hh : h ∈ arrangements s) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => g₀ ∘ σ = h)).card
      = ∏ v ∈ s.toFinset, (s.count v)! := by
  classical
  have hms : Multiset.map g₀ (Finset.univ : Finset (Fin m)).val
           = Multiset.map h (Finset.univ : Finset (Fin m)).val := by
    rw [(mem_arrangements_iff s g₀).1 hg₀, (mem_arrangements_iff s h).1 hh]
  obtain ⟨ρ, hρ⟩ := FourSquareDistributionOQ04Surj.exists_perm_comp hms
  rw [← stabilizer_card_eq_prod_count s hg₀, Fintype.card_subtype]
  refine Finset.card_nbij' (fun σ => σ * ρ⁻¹) (fun σ => σ * ρ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ, ← hρ, Function.comp_assoc,
        ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one, Function.comp_id]
  · intro σ hσ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ]
    exact hρ
  · intro σ _
    show σ * ρ⁻¹ * ρ = σ
    rw [mul_assoc, inv_mul_cancel, mul_one]
  · intro σ _
    show σ * ρ * ρ⁻¹ = σ
    rw [mul_assoc, mul_inv_cancel, mul_one]

/-- **Residue: `card (arrangements s) · ∏count! = m!`.** Fiberwise count of
`Equiv.Perm (Fin m)` under `σ ↦ g₀ ∘ σ`, with all fibers of size `∏count!`. -/
theorem arrangements_card_mul_prod_count {m : ℕ} (s : Multiset ℤ)
    (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card * ∏ v ∈ s.toFinset, (s.count v)! = m ! := by
  classical
  obtain ⟨g₀, hg₀⟩ : (arrangements (m := m) s).Nonempty := by
    have hlen : s.toList.length = m := by rw [Multiset.length_toList, hm]
    exact ⟨s.toList.get ∘ ⇑(finCongr hlen.symm), by
      rw [mem_arrangements_iff, ← Multiset.map_map, Multiset.map_univ_val_equiv,
          Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩
  have key : Fintype.card (Equiv.Perm (Fin m))
      = (arrangements (m := m) s).card * ∏ v ∈ s.toFinset, (s.count v)! := by
    rw [← Finset.card_univ,
        Finset.card_eq_sum_card_fiberwise
          (f := fun σ : Equiv.Perm (Fin m) => g₀ ∘ σ)
          (t := arrangements (m := m) s) (fun σ _ => comp_perm_mem hg₀ σ),
        Finset.sum_congr rfl (fun h hh => fiber_card s hg₀ hh),
        Finset.sum_const, smul_eq_mul]
  rw [← key, Fintype.card_perm, Fintype.card_fin]

/-- **The residue, in `Nat.multinomial` form** — discharging the parent's
`arrangement_card` sorry. -/
theorem arrangement_card {m : ℕ} (s : Multiset ℤ) (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card
      = Nat.multinomial s.toFinset (fun v => s.count v) := by
  have hmul := arrangements_card_mul_prod_count s hm
  have hspec : (∏ v ∈ s.toFinset, (s.count v)!)
        * Nat.multinomial s.toFinset (fun v => s.count v) = m ! := by
    have h := Nat.multinomial_spec s.toFinset (fun v => s.count v)
    rwa [Multiset.toFinset_sum_count_eq, hm] at h
  have hP : (0 : ℕ) < ∏ v ∈ s.toFinset, (s.count v)! :=
    Finset.prod_pos (fun v _ => Nat.factorial_pos _)
  refine mul_right_cancel₀ hP.ne' ?_
  rw [hmul, mul_comm]
  exact hspec.symm

#check @arrangement_card
#check @arrangements_card_mul_prod_count

end FourSquareDistributionOQ04ArrangeFinal
