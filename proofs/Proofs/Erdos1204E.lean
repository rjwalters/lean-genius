import Proofs.Erdos1204D

/-
# Erdős #1204 — a slope-`35/8` general lower bound `8·A(k) ≥ 35(k − 48)`

`Erdos1204Problem.lean`, `Erdos1204C.lean` and `Erdos1204D.lean` record a ladder of
*general* lower bounds on the minimal admissible diameter `A(k)`, each using more small
primes via CRT + pigeonhole:

* `sub_one_le_A`         : `A(k) ≥ k − 1`      (trivial packing),
* `two_mul_sub_one_le_A` : `A(k) ≥ 2(k − 1)`   (prime `2`: single parity, slope `2`),
* `three_mul_sub_two_le_A` : `A(k) ≥ 3(k − 2)` (primes `2,3`: slope `3`),
* `four_mul_A_ge`        : `4·A(k) ≥ 15(k − 8)` (primes `2,3,5`: slope `15/4 = 3.75`).

Here we add the next rung by bringing in the prime `7`. An admissible set misses a
residue class modulo each of `2`, `3`, `5`, `7`, so by CRT its elements occupy at most
`1·2·4·6 = 48` residue classes modulo `210`. Pigeonholing, one of those `48` classes
holds `≥ ⌈k/48⌉` of the `k` elements; being congruent mod `210` they are `210`-separated,
so the diameter is at least `210(⌈k/48⌉ − 1)`. Cleared of the ceiling this is the
slope-`35/8` bound

* `admissible_seven_le_sup` : any admissible set has `8·sup ≥ 35(card − 48)`;
* `eight_mul_A_ge`          : `8·A(k) ≥ 35(k − 48)`.

The slope improves from `15/4 = 30/8` (primes `2,3,5`) to `35/8 = 210/48` (primes
`2,3,5,7`), the leading joint prime-`{2,3,5,7}` contribution toward the conjectured
`A(k) ∼ k log k`. It strictly beats the slope-`15/4` bound for `k ≥ 289`
(`seven_bound_gt_five_bound`), while still lying far below the super-linear truth. The
construction is the exact `p = 7` analogue of `Erdos1204D.lean` and reuses its
single-class spacing lemma `same_mod_sup_ge`.

Everything is axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace Erdos1204

open Finset

/-- Missing one class mod `2`, one mod `3`, one mod `5`, and one mod `7` leaves exactly
`1 · 2 · 4 · 6 = 48` residue quadruples in `ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7`. A finite
check. -/
theorem four_classes_prod :
    ∀ (s : ZMod 2) (u : ZMod 3) (v : ZMod 5) (w : ZMod 7),
      (Finset.univ.filter (fun q : ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7 =>
        q.1 ≠ s ∧ q.2.1 ≠ u ∧ q.2.2.1 ≠ v ∧ q.2.2.2 ≠ w)).card = 48 := by
  decide

/-- **Slope-`35/8` lower bound on the diameter.** Every admissible set satisfies
`8·sup ≥ 35(card − 48)`. Missing a class mod `2`, `3`, `5` and `7`, its elements occupy at
most `48` residue classes modulo `210`; the largest class holds `≥ ⌈card/48⌉` elements,
`210`-spaced, so `sup ≥ 210(⌈card/48⌉ − 1) ≥ 35(card − 48)/8`. The `p = 7` extension of
`admissible_five_le_sup`. -/
theorem admissible_seven_le_sup {a : Finset ℕ} (ha : Admissible a) :
    35 * (a.card - 48) ≤ 8 * a.sup id := by
  classical
  rcases Nat.lt_or_ge a.card 49 with hsmall | hbig
  · -- `card ≤ 48` ⇒ `35(card − 48) = 0`
    have : 35 * (a.card - 48) = 0 := by omega
    rw [this]; exact Nat.zero_le _
  · -- pull out the missed classes mod 2, mod 3, mod 5 and mod 7
    obtain ⟨r2, hr2⟩ := ha 2 (by norm_num)
    obtain ⟨r3, hr3⟩ := ha 3 (by norm_num)
    obtain ⟨r5, hr5⟩ := ha 5 (by norm_num)
    obtain ⟨r7, hr7⟩ := ha 7 (by norm_num)
    -- the residue-quadruple map and its 48-element target
    set f : ℕ → ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7 :=
      fun x => ((x : ZMod 2), (x : ZMod 3), (x : ZMod 5), (x : ZMod 7)) with hf_def
    set T : Finset (ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7) :=
      Finset.univ.filter (fun q => q.1 ≠ r2 ∧ q.2.1 ≠ r3 ∧ q.2.2.1 ≠ r5 ∧ q.2.2.2 ≠ r7)
      with hT
    -- admissible elements map into `T`
    have hf : ∀ x ∈ a, f x ∈ T := by
      intro x hx
      rw [hf_def, hT]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr2 x hx, hr3 x hx, hr5 x hx, hr7 x hx⟩
    -- pigeonhole: some quadruple `p` has a fiber larger than `(card − 1)/48`
    have hlt : T.card * ((a.card - 1) / 48) < a.card := by
      rw [hT, four_classes_prod r2 r3 r5 r7]; omega
    obtain ⟨p, _, hp⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := f) hf hlt
    -- every element of that fiber shares the quadruple `p`
    have hpairmem : ∀ x ∈ a.filter (fun x => f x = p), f x = p :=
      fun x hx => (Finset.mem_filter.mp hx).2
    -- hence any two are congruent mod 2, 3, 5 and 7, so (CRT) congruent mod 210
    have hmod210 : ∀ x ∈ a.filter (fun x => f x = p), ∀ y ∈ a.filter (fun x => f x = p),
        (x : ZMod 210) = (y : ZMod 210) := by
      intro x hx y hy
      have hxy : f x = f y := (hpairmem x hx).trans (hpairmem y hy).symm
      rw [hf_def] at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨e2, e3, e5, e7⟩ := hxy
      rw [ZMod.natCast_eq_natCast_iff] at e2 e3 e5 e7
      rw [ZMod.natCast_eq_natCast_iff]
      have h6 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 2 3 by decide)).mp ⟨e2, e3⟩
      have h30 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 6 5 by decide)).mp ⟨h6, e5⟩
      have h210 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 30 7 by decide)).mp ⟨h30, e7⟩
      simpa using h210
    -- spacing within that class, transported back to `a`
    have hspace := same_mod_sup_ge (show (0 : ℕ) < 210 by norm_num) hmod210
    have hsub : a.filter (fun x => f x = p) ⊆ a := Finset.filter_subset _ _
    have hsuple : (a.filter (fun x => f x = p)).sup id ≤ a.sup id := Finset.sup_mono hsub
    omega

/-- **Slope-`35/8` lower bound on `A(k)`: `8·A(k) ≥ 35(k − 48)`.** The joint action of the
primes `2`, `3`, `5` and `7` forces every admissible `k`-set to occupy at most `48` residue
classes mod `210`, so its `k` elements are packed at density `≤ 48/210 = 8/35` and must span
at least `35(k − 48)/8`. The `p = 7` rung above `four_mul_A_ge` (`4·A(k) ≥ 15(k − 8)`). -/
theorem eight_mul_A_ge (k : ℕ) : 35 * (k - 48) ≤ 8 * A k := by
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem k
  have h := admissible_seven_le_sup ha
  rw [hcard, hsup] at h
  exact h

/-- **The slope-`35/8` bound beats the slope-`15/4` bound past `k = 288`.** For every
`k ≥ 289`, `35(k − 48) > 30(k − 8) = 2·15(k − 8)`, so `eight_mul_A_ge` strictly improves the
(two-times) slope-`15/4` bound `four_mul_A_ge`. Below `k = 289` the slope-`15/4` bound is
still sharper; the crossover reflects the larger constant offset (`−48` vs `−8`) that the
extra prime `7` costs. -/
theorem seven_bound_gt_five_bound {k : ℕ} (hk : 289 ≤ k) :
    30 * (k - 8) < 35 * (k - 48) := by omega

end Erdos1204
