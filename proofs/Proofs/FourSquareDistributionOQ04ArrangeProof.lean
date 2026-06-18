import Mathlib

/-
# Four-Square Distribution — OQ-04: discharging the `arrangement_card` residue

Companion to `FourSquareDistributionOQ04Arrange.lean` (merged via #24518), which
reduced the entire open question to a single combinatorial residue, the
multiset-arrangement count

  `arrangement_card`:  `#{ g : Fin m → ℤ | multiset(g) = s } = Nat.multinomial s.toFinset s.count`.

## Key discovery (researcher-5, 2026-06-16)

The parent file's docstring states there is "**no ready cardinality lemma**" for
the stabilizer order `∏_v (count_v)!` and that this product "is the genuine
residue" to be computed by hand. **That is no longer true.** Mathlib's
`DomMulAct.stabilizer_card'` (`Mathlib/GroupTheory/Perm/DomMulAct.lean`) computes
exactly this product for the precomposition action of `Equiv.Perm` on functions:

  `DomMulAct.stabilizer_card' (f : α → ι) [Fintype α] [DecidableEq α] [DecidableEq ι] :`
  `  Fintype.card {g : Perm α // f ∘ g = f}`
  `    = ∏ i ∈ Finset.univ.image f, (Fintype.card {a // f a = i})!`

(It needs only `DecidableEq ι`, NOT `Fintype ι`, so it applies with `ι = ℤ`.)

This collapses the orbit–stabilizer argument to wiring:
1. Set up the `DomMulAct (Perm (Fin m))` action on `Fin m → ℤ`.
2. `MulAction.card_orbit_mul_card_stabilizer_eq_card_group g`:
   `card (orbit) · card (stabilizer) = card (Perm (Fin m)) = m!` (`Fintype.card_perm`).
3. `stabilizer_card'` rewrites `card (stabilizer)` as `∏_{i ∈ image g} (card (fiber i))!`.
   For `g ∈ arrangements s` we have `image g = s.toFinset` and `card (fiber i) = s.count i`,
   so the product is `∏_{v ∈ s.toFinset} (s.count v)!`.
4. The orbit of `g` is (in bijection with) `arrangements s`: precomposition by a
   permutation preserves the multiset image, and conversely any function with the
   same multiset image is a precomposition of `g`.
5. Hence `card (arrangements s) · ∏count! = m!`, i.e.
   `card (arrangements s) = m! / ∏count! = Nat.multinomial s.toFinset s.count`
   (via the parent's `factorial_div_eq_multinomial` + `Nat.multinomial_spec`).

## Status

Build-gated orphan (NOT registered in `Proofs.lean`; CI-safe).

**`arrangement_card` is now fully discharged — no `sorry` anywhere in this file
(researcher-3, 2026-06-18).** The two residues that prior sessions left as `sorry`s
(orbit↔arrangements bijection + orbit–stabilizer assembly) are replaced by a single
**elementary Finset fiber-counting** argument that avoids `MulAction.orbit` entirely
— and with it the orbit `Fintype`-instance synthesis that repeatedly stalled the
orbit–stabilizer route. The new pieces, all name-checked against rev `2df2f0150c`:

- `map_univ_comp_perm_eq` / `exists_perm_of_map_univ_eq` — the value-multiset ↔
  permutation correspondence (forward + the converse "two tuples with equal
  multiset differ by a permutation", via `Tuple.sort` + `List.Perm.eq_of_sortedLE`;
  folded in from the companion `FourSquareDistributionOQ04Converse.lean`).
- `nonempty_arrangements` — a witness `g₀ ∈ arrangements s` from `s.toList`
  (`List.ofFn_congr` + `List.ofFn_get` + `Multiset.coe_toList`).
- `arrangements_card_mul_prod_count` — **the residue**, proved by
  `Finset.card_eq_sum_card_fiberwise` for the map `σ ↦ g₀ ∘ σ : Perm (Fin m) →
  arrangements s`: every fiber is a coset of the stabilizer (a `Finset.card_nbij'`
  bijection `σ ↦ σ * σ₀⁻¹`), so each has cardinality `∏count!` by
  `stabilizer_card_eq_prod_count`; summing `#(Perm (Fin m)) = m!` over the
  `(arrangements s).card` fibers gives `(arrangements s).card · ∏count! = m!`.
- `arrangement_card` (the `Nat.multinomial` headline) — unchanged, cancels
  `∏count!` against `Nat.multinomial_spec` (`mul_right_cancel₀`).

The stabilizer half (`image_eq_toFinset_of_mem`, `card_fiber_eq_count`,
`stabilizer_card_eq_prod_count`) is unchanged, resting on `DomMulAct.stabilizer_card'`.

`arrangements` is restated here verbatim from the parent so the file is
self-contained (and `prove_file`-portable). BUILD-PENDING: authored against the
offline Mathlib checkout at the build pin `2df2f0150c`; every lemma name was
re-verified there, but only a Docker build confirms the routine glue.
-/

namespace FourSquareDistributionOQ04ArrangeProof

open Finset

/-- The canonical `Finset` of multiset-arrangements (verbatim from the parent file). -/
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

/-- The image of an arrangement is exactly `s.toFinset`: the set of values of `g`
    equals the support of the multiset `s` it realizes. -/
theorem image_eq_toFinset_of_mem {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) :
    (Finset.univ : Finset (Fin m)).image g = s.toFinset := by
  classical
  rw [mem_arrangements_iff] at hg
  rw [← hg, Multiset.toFinset_map, Finset.val_toFinset]

/-- The `i`-fiber of an arrangement has size `s.count i`: the number of indices
    mapping to a value equals that value's multiplicity in the realized multiset. -/
theorem card_fiber_eq_count {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) (i : ℤ) :
    Fintype.card {a : Fin m // g a = i} = s.count i := by
  classical
  rw [mem_arrangements_iff] at hg
  have hfeq : (Finset.univ : Finset (Fin m)).val.filter (fun a : Fin m => g a = i)
      = (Finset.univ : Finset (Fin m)).val.filter (fun a : Fin m => i = g a) :=
    Multiset.filter_congr (fun a _ => eq_comm)
  rw [Fintype.card_subtype, ← hg, Multiset.count_map, Finset.card_def, Finset.filter_val, hfeq]

/-- **Stabilizer order = ∏ count!** for an arrangement `g`, packaged from
    `DomMulAct.stabilizer_card'` together with `image_eq_toFinset_of_mem` and
    `card_fiber_eq_count`. The product over `Finset.univ.image g` returned by
    `stabilizer_card'` is re-indexed to `s.toFinset` and each fiber cardinality
    is rewritten to the corresponding multiplicity `s.count v`. -/
theorem stabilizer_card_eq_prod_count {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) :
    Fintype.card {σ : Equiv.Perm (Fin m) // g ∘ σ = g}
      = ∏ v ∈ s.toFinset, (s.count v)! := by
  classical
  rw [DomMulAct.stabilizer_card' (f := g), image_eq_toFinset_of_mem s hg]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [card_fiber_eq_count s hg v]

/-- **Forward direction.** Precomposition by a permutation preserves the
value-multiset of a tuple (the `Multiset.map _ univ.val` form of
`Equiv.Perm.ofFn_comp_perm`). Folded in from `FourSquareDistributionOQ04Converse`. -/
theorem map_univ_comp_perm_eq {m : ℕ} (g : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) :
    Multiset.map (g ∘ σ) (Finset.univ : Finset (Fin m)).val
      = Multiset.map g (Finset.univ : Finset (Fin m)).val := by
  classical
  have h := Equiv.Perm.ofFn_comp_perm σ g
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map (g ∘ σ), ← Fin.univ_val_map g] at h
  exact h

/-- **The orbit-surjectivity converse.** Two integer tuples on `Fin m` with the
same value-multiset differ by a permutation of the index set. Sorting both tuples
(`Tuple.sort`) yields permutation-equivalent `SortedLE` lists, hence equal
(`List.Perm.eq_of_sortedLE`); the tuples then agree after sorting, so differ only
by the composite of their two sorting permutations. -/
theorem exists_perm_of_map_univ_eq {m : ℕ} {x y : Fin m → ℤ}
    (h : Multiset.map x (Finset.univ : Finset (Fin m)).val
       = Multiset.map y (Finset.univ : Finset (Fin m)).val) :
    ∃ σ : Equiv.Perm (Fin m), x = y ∘ σ := by
  classical
  have hxy : List.ofFn x ~ List.ofFn y := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map x, ← Fin.univ_val_map y]
    exact h
  have hsx : List.ofFn (x ∘ Tuple.sort x) ~ List.ofFn (y ∘ Tuple.sort y) :=
    ((Equiv.Perm.ofFn_comp_perm (Tuple.sort x) x).trans hxy).trans
      (Equiv.Perm.ofFn_comp_perm (Tuple.sort y) y).symm
  have hsortX : (List.ofFn (x ∘ Tuple.sort x)).SortedLE :=
    List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort x)
  have hsortY : (List.ofFn (y ∘ Tuple.sort y)).SortedLE :=
    List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort y)
  have heq : List.ofFn (x ∘ Tuple.sort x) = List.ofFn (y ∘ Tuple.sort y) :=
    hsx.eq_of_sortedLE hsortX hsortY
  have hfun : x ∘ (Tuple.sort x : Equiv.Perm (Fin m))
      = y ∘ (Tuple.sort y : Equiv.Perm (Fin m)) := List.ofFn_injective heq
  refine ⟨Tuple.sort y * (Tuple.sort x)⁻¹, ?_⟩
  ext i
  have hpt := congrFun hfun ((Tuple.sort x)⁻¹ i)
  simp only [Function.comp_apply, Equiv.Perm.apply_inv_self] at hpt
  simpa [Function.comp_apply, Equiv.Perm.mul_apply] using hpt

/-- **Nonemptiness.** A multiset `s` of cardinality `m` is realized by some
arrangement `g₀ : Fin m → ℤ` (read off `s.toList`, whose length is `m`). -/
theorem nonempty_arrangements {m : ℕ} (s : Multiset ℤ) (hm : Multiset.card s = m) :
    ∃ g : Fin m → ℤ, g ∈ arrangements (m := m) s := by
  classical
  have hlen : s.toList.length = m := by rw [Multiset.length_toList, hm]
  refine ⟨fun i => s.toList.get (Fin.cast hlen.symm i), ?_⟩
  rw [mem_arrangements_iff, Fin.univ_val_map,
    show List.ofFn (fun i : Fin m => s.toList.get (Fin.cast hlen.symm i)) = s.toList from by
      rw [← List.ofFn_congr hlen s.toList.get, List.ofFn_get]]
  exact Multiset.coe_toList s

/-- **Residue discharged: `card (arrangements s) · ∏count! = m!`.**
    Elementary fiber-counting for the precomposition map `σ ↦ g₀ ∘ σ` from
    `Perm (Fin m)` onto `arrangements s` (`g₀` a witness from `nonempty_arrangements`):
    `Finset.card_eq_sum_card_fiberwise` writes `#(Perm (Fin m)) = m!` as a sum of
    fiber cardinalities over `arrangements s`, and each fiber over `h = g₀ ∘ σ₀` is a
    coset of the stabilizer (bijection `σ ↦ σ * σ₀⁻¹`), so has cardinality `∏count!`
    by `stabilizer_card_eq_prod_count`. This is the exact-division correctness fact
    that makes the parent's `Nat.div` non-truncating, with no `MulAction.orbit` (and
    hence no orbit-`Fintype` synthesis) anywhere. -/
theorem arrangements_card_mul_prod_count {m : ℕ} (s : Multiset ℤ)
    (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card * ∏ v ∈ s.toFinset, (s.count v)! = m ! := by
  classical
  obtain ⟨g₀, hg₀⟩ := nonempty_arrangements s hm
  have hg₀map : Multiset.map g₀ (Finset.univ : Finset (Fin m)).val = s :=
    (mem_arrangements_iff s g₀).mp hg₀
  -- the precomposition map `σ ↦ g₀ ∘ σ` lands in `arrangements s`
  have hmaps : Set.MapsTo (fun σ : Equiv.Perm (Fin m) => g₀ ∘ (σ : Fin m → Fin m))
      ↑(Finset.univ : Finset (Equiv.Perm (Fin m))) ↑(arrangements (m := m) s) := by
    intro σ _
    simp only [Finset.mem_coe, mem_arrangements_iff]
    rw [map_univ_comp_perm_eq g₀ σ, hg₀map]
  -- every fiber has cardinality `∏count!`
  have hfiber : ∀ h ∈ arrangements (m := m) s,
      ({σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))) |
          g₀ ∘ (σ : Fin m → Fin m) = h}).card = ∏ v ∈ s.toFinset, (s.count v)! := by
    intro h hh
    have hhmap : Multiset.map h (Finset.univ : Finset (Fin m)).val = s :=
      (mem_arrangements_iff s h).mp hh
    obtain ⟨σ₀, hσ₀⟩ := exists_perm_of_map_univ_eq (x := h) (y := g₀)
      (by rw [hhmap, hg₀map])
    -- `hσ₀ : h = g₀ ∘ σ₀`; the fiber over `h` bijects with the stabilizer fiber
    have hbij : ({σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))) |
            g₀ ∘ (σ : Fin m → Fin m) = h}).card
        = ({σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))) |
            g₀ ∘ (σ : Fin m → Fin m) = g₀}).card := by
      apply Finset.card_nbij' (fun σ => σ * σ₀⁻¹) (fun σ => σ * σ₀)
      · intro σ hσ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ, hσ₀,
          Function.comp_assoc, ← Equiv.Perm.coe_mul, mul_inv_cancel,
          Equiv.Perm.coe_one, Function.comp_id]
      · intro σ hσ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ, ← hσ₀]
      · intro σ _; dsimp only; group
      · intro σ _; dsimp only; group
    have hconv : ({σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))) |
            g₀ ∘ (σ : Fin m → Fin m) = g₀}).card
        = Fintype.card {σ : Equiv.Perm (Fin m) // g₀ ∘ (σ : Fin m → Fin m) = g₀} := by
      rw [Fintype.card_subtype]
    rw [hbij, hconv, stabilizer_card_eq_prod_count s hg₀]
  -- assemble: `m! = Σ_{h ∈ arrangements s} ∏count! = (arrangements s).card · ∏count!`
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hsum
  exact hsum.symm

/-- **The residue, in `Nat.multinomial` form.** Identical statement to the parent
    file's `arrangement_card`; obtained by cancelling `∏count!` from
    `arrangements_card_mul_prod_count` against `Nat.multinomial_spec`
    (`∏count! · multinomial = (∑count)!` with `∑count = m`). This derivation is
    unconditional — the only residual input is `arrangements_card_mul_prod_count`. -/
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

end FourSquareDistributionOQ04ArrangeProof
