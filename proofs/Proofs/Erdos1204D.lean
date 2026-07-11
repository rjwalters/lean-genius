import Proofs.Erdos1204C

/-
# Erdős #1204 — a slope-`15/4` general lower bound `4·A(k) ≥ 15(k − 8)`

`Erdos1204Problem.lean` and `Erdos1204C.lean` record a ladder of *general* lower
bounds on the minimal admissible diameter `A(k)`, each using more small primes:

* `sub_one_le_A`         : `A(k) ≥ k − 1`      (trivial packing),
* `two_mul_sub_one_le_A` : `A(k) ≥ 2(k − 1)`   (prime `2`: single parity, slope `2`),
* `three_mul_sub_two_le_A` : `A(k) ≥ 3(k − 2)` (primes `2,3`: slope `3`).

Here we add the next rung by bringing in the prime `5`. An admissible set misses a
residue class modulo each of `2`, `3`, `5`, so by CRT its elements occupy at most
`1·2·4 = 8` residue classes modulo `30`. Pigeonholing, one of those `8` classes holds
`≥ ⌈k/8⌉` of the `k` elements; being congruent mod `30` they are `30`-separated, so the
diameter is at least `30(⌈k/8⌉ − 1)`. Cleared of the ceiling this is the slope-`15/4`
bound

* `admissible_five_le_sup` : any admissible set has `4·sup ≥ 15(card − 8)`;
* `four_mul_A_ge`          : `4·A(k) ≥ 15(k − 8)`.

The slope improves from `3 = 6/2` (primes `2,3`) to `15/4 = 30/8` (primes `2,3,5`),
the leading joint prime-`{2,3,5}` contribution toward the conjectured `A(k) ∼ k log k`.
It strictly beats the slope-`3` bound for `k ≥ 33` (`five_bound_gt_three_bound`), while
still lying far below the super-linear truth. The construction is the exact `p = 5`
analogue of `Erdos1204C.lean` and reuses its single-class spacing lemma
`same_mod_sup_ge`.

Everything is axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace Erdos1204

open Finset

/-- Missing one class mod `2`, one mod `3`, and one mod `5` leaves exactly
`1 · 2 · 4 = 8` residue triples in `ZMod 2 × ZMod 3 × ZMod 5`. A finite check. -/
theorem three_classes_prod :
    ∀ (s : ZMod 2) (u : ZMod 3) (v : ZMod 5),
      (Finset.univ.filter (fun q : ZMod 2 × ZMod 3 × ZMod 5 =>
        q.1 ≠ s ∧ q.2.1 ≠ u ∧ q.2.2 ≠ v)).card = 8 := by
  decide

/-- **Slope-`15/4` lower bound on the diameter.** Every admissible set satisfies
`4·sup ≥ 15(card − 8)`. Missing a class mod `2`, `3` and `5`, its elements occupy at most
`8` residue classes modulo `30`; the largest class holds `≥ ⌈card/8⌉` elements, `30`-spaced,
so `sup ≥ 30(⌈card/8⌉ − 1) ≥ 15(card − 8)/4`. The `p = 5` extension of
`admissible_three_sub_two_le_sup`. -/
theorem admissible_five_le_sup {a : Finset ℕ} (ha : Admissible a) :
    15 * (a.card - 8) ≤ 4 * a.sup id := by
  classical
  rcases Nat.lt_or_ge a.card 9 with hsmall | hbig
  · -- `card ≤ 8` ⇒ `15(card − 8) = 0`
    have : 15 * (a.card - 8) = 0 := by omega
    rw [this]; exact Nat.zero_le _
  · -- pull out the missed classes mod 2, mod 3 and mod 5
    obtain ⟨r2, hr2⟩ := ha 2 (by norm_num)
    obtain ⟨r3, hr3⟩ := ha 3 (by norm_num)
    obtain ⟨r5, hr5⟩ := ha 5 (by norm_num)
    -- the residue-triple map and its 8-element target
    set f : ℕ → ZMod 2 × ZMod 3 × ZMod 5 :=
      fun x => ((x : ZMod 2), (x : ZMod 3), (x : ZMod 5)) with hf_def
    set T : Finset (ZMod 2 × ZMod 3 × ZMod 5) :=
      Finset.univ.filter (fun q => q.1 ≠ r2 ∧ q.2.1 ≠ r3 ∧ q.2.2 ≠ r5) with hT
    -- admissible elements map into `T`
    have hf : ∀ x ∈ a, f x ∈ T := by
      intro x hx
      rw [hf_def, hT]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr2 x hx, hr3 x hx, hr5 x hx⟩
    -- pigeonhole: some triple `p` has a fiber larger than `(card − 1)/8`
    have hlt : T.card * ((a.card - 1) / 8) < a.card := by
      rw [hT, three_classes_prod r2 r3 r5]; omega
    obtain ⟨p, _, hp⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := f) hf hlt
    -- every element of that fiber shares the triple `p`
    have hpairmem : ∀ x ∈ a.filter (fun x => f x = p), f x = p :=
      fun x hx => (Finset.mem_filter.mp hx).2
    -- hence any two are congruent mod 2, 3 and 5, so (CRT) congruent mod 30
    have hmod30 : ∀ x ∈ a.filter (fun x => f x = p), ∀ y ∈ a.filter (fun x => f x = p),
        (x : ZMod 30) = (y : ZMod 30) := by
      intro x hx y hy
      have hxy : f x = f y := (hpairmem x hx).trans (hpairmem y hy).symm
      rw [hf_def] at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨e2, e3, e5⟩ := hxy
      rw [ZMod.natCast_eq_natCast_iff] at e2 e3 e5
      rw [ZMod.natCast_eq_natCast_iff]
      have h6 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 2 3 by decide)).mp ⟨e2, e3⟩
      have h30 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 6 5 by decide)).mp ⟨h6, e5⟩
      simpa using h30
    -- spacing within that class, transported back to `a`
    have hspace := same_mod_sup_ge (show (0 : ℕ) < 30 by norm_num) hmod30
    have hsub : a.filter (fun x => f x = p) ⊆ a := Finset.filter_subset _ _
    have hsuple : (a.filter (fun x => f x = p)).sup id ≤ a.sup id := Finset.sup_mono hsub
    omega

/-- **Slope-`15/4` lower bound on `A(k)`: `4·A(k) ≥ 15(k − 8)`.** The joint action of the
primes `2`, `3` and `5` forces every admissible `k`-set to occupy at most `8` residue
classes mod `30`, so its `k` elements are packed at density `≤ 8/30 = 4/15` and must span
at least `15(k − 8)/4`. The `p = 5` rung above `three_mul_sub_two_le_A`
(`A(k) ≥ 3(k − 2)`). -/
theorem four_mul_A_ge (k : ℕ) : 15 * (k - 8) ≤ 4 * A k := by
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem k
  have h := admissible_five_le_sup ha
  rw [hcard, hsup] at h
  exact h

/-- **The slope-`15/4` bound beats the slope-`3` bound past `k = 32`.** For every `k ≥ 33`,
`15(k − 8) > 12(k − 2) = 4·3(k − 2)`, so `four_mul_A_ge` strictly improves the (four-times)
slope-`3` bound `three_mul_sub_two_le_A`. Below `k = 33` the slope-`3` bound is still
sharper; the crossover reflects the larger constant offset (`−8` vs `−2`) that the extra
prime `5` costs. -/
theorem five_bound_gt_three_bound {k : ℕ} (hk : 33 ≤ k) :
    12 * (k - 2) < 15 * (k - 8) := by omega

end Erdos1204
