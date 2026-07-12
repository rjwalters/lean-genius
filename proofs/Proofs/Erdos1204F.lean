import Proofs.Erdos1204E

/-
# Erdős #1204 — a slope-`77/16` general lower bound `16·A(k) ≥ 77(k − 480)`

`Erdos1204Problem.lean`, `Erdos1204C.lean`, `Erdos1204D.lean` and `Erdos1204E.lean` record
a ladder of *general* lower bounds on the minimal admissible diameter `A(k)`, each bringing
in one more small prime via CRT + pigeonhole:

* `sub_one_le_A`         : `A(k) ≥ k − 1`      (trivial packing),
* `two_mul_sub_one_le_A` : `A(k) ≥ 2(k − 1)`   (prime `2`: single parity, slope `2`),
* `three_mul_sub_two_le_A` : `A(k) ≥ 3(k − 2)` (primes `2,3`: slope `3`),
* `four_mul_A_ge`        : `4·A(k) ≥ 15(k − 8)` (primes `2,3,5`: slope `15/4 = 3.75`),
* `eight_mul_A_ge`       : `8·A(k) ≥ 35(k − 48)` (primes `2,3,5,7`: slope `35/8 = 4.375`).

Here we add the next rung by bringing in the prime `11`. An admissible set misses a
residue class modulo each of `2`, `3`, `5`, `7`, `11`, so by CRT its elements occupy at
most `1·2·4·6·10 = 480` residue classes modulo `2310`. Pigeonholing, one of those `480`
classes holds `≥ ⌈k/480⌉` of the `k` elements; being congruent mod `2310` they are
`2310`-separated, so the diameter is at least `2310(⌈k/480⌉ − 1)`. Cleared of the ceiling
this is the slope-`77/16` bound

* `admissible_eleven_le_sup` : any admissible set has `16·sup ≥ 77(card − 480)`;
* `sixteen_mul_A_ge`         : `16·A(k) ≥ 77(k − 480)`.

The slope improves from `35/8 = 70/16` (primes `2,3,5,7`) to `77/16 = 2310/480` (primes
`2,3,5,7,11`), the leading joint prime-`{2,3,5,7,11}` contribution toward the conjectured
`A(k) ∼ k log k`. It strictly beats the (two-times) slope-`35/8` bound for `k ≥ 4801`
(`eleven_bound_gt_seven_bound`), while still lying far below the super-linear truth. The
construction is the exact `p = 11` analogue of `Erdos1204E.lean` and reuses its single-class
spacing lemma `same_mod_sup_ge`.

Everything is axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace Erdos1204

open Finset

/-- Removing one residue from `ZMod n` leaves `n − 1` classes. -/
theorem card_filter_ne {n : ℕ} [NeZero n] (c : ZMod n) :
    (Finset.univ.filter (· ≠ c)).card = n - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ, ZMod.card]

/-- Missing one class mod `2`, one mod `3`, one mod `5`, one mod `7`, and one mod `11`
leaves exactly `1 · 2 · 4 · 6 · 10 = 480` residue quintuples in
`ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7 × ZMod 11`. Rather than enumerate all `2310` tuples
(a kernel `decide` over that many elements is prohibitively expensive), we factor the
constraint coordinatewise: the admissible quintuples are exactly the product of the five
single-coordinate "≠"-sets, whose cardinalities multiply via `Finset.card_product`. -/
theorem five_classes_prod :
    ∀ (s : ZMod 2) (u : ZMod 3) (v : ZMod 5) (w : ZMod 7) (z : ZMod 11),
      (Finset.univ.filter (fun q : ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7 × ZMod 11 =>
        q.1 ≠ s ∧ q.2.1 ≠ u ∧ q.2.2.1 ≠ v ∧ q.2.2.2.1 ≠ w ∧ q.2.2.2.2 ≠ z)).card = 480 := by
  intro s u v w z
  have hprod :
      (Finset.univ.filter (fun q : ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7 × ZMod 11 =>
        q.1 ≠ s ∧ q.2.1 ≠ u ∧ q.2.2.1 ≠ v ∧ q.2.2.2.1 ≠ w ∧ q.2.2.2.2 ≠ z))
        = (Finset.univ.filter (· ≠ s)) ×ˢ (Finset.univ.filter (· ≠ u)) ×ˢ
            (Finset.univ.filter (· ≠ v)) ×ˢ (Finset.univ.filter (· ≠ w)) ×ˢ
            (Finset.univ.filter (· ≠ z)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [hprod, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_product, card_filter_ne, card_filter_ne, card_filter_ne,
    card_filter_ne, card_filter_ne]

/-- **Slope-`77/16` lower bound on the diameter.** Every admissible set satisfies
`16·sup ≥ 77(card − 480)`. Missing a class mod `2`, `3`, `5`, `7` and `11`, its elements
occupy at most `480` residue classes modulo `2310`; the largest class holds `≥ ⌈card/480⌉`
elements, `2310`-spaced, so `sup ≥ 2310(⌈card/480⌉ − 1) ≥ 77(card − 480)/16`. The `p = 11`
extension of `admissible_seven_le_sup`. -/
theorem admissible_eleven_le_sup {a : Finset ℕ} (ha : Admissible a) :
    77 * (a.card - 480) ≤ 16 * a.sup id := by
  classical
  rcases Nat.lt_or_ge a.card 481 with hsmall | hbig
  · -- `card ≤ 480` ⇒ `77(card − 480) = 0`
    have : 77 * (a.card - 480) = 0 := by omega
    rw [this]; exact Nat.zero_le _
  · -- pull out the missed classes mod 2, mod 3, mod 5, mod 7 and mod 11
    obtain ⟨r2, hr2⟩ := ha 2 (by norm_num)
    obtain ⟨r3, hr3⟩ := ha 3 (by norm_num)
    obtain ⟨r5, hr5⟩ := ha 5 (by norm_num)
    obtain ⟨r7, hr7⟩ := ha 7 (by norm_num)
    obtain ⟨r11, hr11⟩ := ha 11 (by norm_num)
    -- the residue-quintuple map and its 480-element target
    set f : ℕ → ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7 × ZMod 11 :=
      fun x => ((x : ZMod 2), (x : ZMod 3), (x : ZMod 5), (x : ZMod 7), (x : ZMod 11))
      with hf_def
    set T : Finset (ZMod 2 × ZMod 3 × ZMod 5 × ZMod 7 × ZMod 11) :=
      Finset.univ.filter (fun q =>
        q.1 ≠ r2 ∧ q.2.1 ≠ r3 ∧ q.2.2.1 ≠ r5 ∧ q.2.2.2.1 ≠ r7 ∧ q.2.2.2.2 ≠ r11)
      with hT
    -- admissible elements map into `T`
    have hf : ∀ x ∈ a, f x ∈ T := by
      intro x hx
      rw [hf_def, hT]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr2 x hx, hr3 x hx, hr5 x hx, hr7 x hx, hr11 x hx⟩
    -- pigeonhole: some quintuple `p` has a fiber larger than `(card − 1)/480`
    have hlt : T.card * ((a.card - 1) / 480) < a.card := by
      rw [hT, five_classes_prod r2 r3 r5 r7 r11]; omega
    obtain ⟨p, _, hp⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := f) hf hlt
    -- every element of that fiber shares the quintuple `p`
    have hpairmem : ∀ x ∈ a.filter (fun x => f x = p), f x = p :=
      fun x hx => (Finset.mem_filter.mp hx).2
    -- hence any two are congruent mod 2, 3, 5, 7 and 11, so (CRT) congruent mod 2310
    have hmod2310 : ∀ x ∈ a.filter (fun x => f x = p), ∀ y ∈ a.filter (fun x => f x = p),
        (x : ZMod 2310) = (y : ZMod 2310) := by
      intro x hx y hy
      have hxy : f x = f y := (hpairmem x hx).trans (hpairmem y hy).symm
      rw [hf_def] at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨e2, e3, e5, e7, e11⟩ := hxy
      rw [ZMod.natCast_eq_natCast_iff] at e2 e3 e5 e7 e11
      rw [ZMod.natCast_eq_natCast_iff]
      have h6 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 2 3 by decide)).mp ⟨e2, e3⟩
      have h30 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 6 5 by decide)).mp ⟨h6, e5⟩
      have h210 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 30 7 by decide)).mp ⟨h30, e7⟩
      have h2310 :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 210 11 by decide)).mp ⟨h210, e11⟩
      simpa using h2310
    -- spacing within that class, transported back to `a`
    have hspace := same_mod_sup_ge (show (0 : ℕ) < 2310 by norm_num) hmod2310
    have hsub : a.filter (fun x => f x = p) ⊆ a := Finset.filter_subset _ _
    have hsuple : (a.filter (fun x => f x = p)).sup id ≤ a.sup id := Finset.sup_mono hsub
    omega

/-- **Slope-`77/16` lower bound on `A(k)`: `16·A(k) ≥ 77(k − 480)`.** The joint action of the
primes `2`, `3`, `5`, `7` and `11` forces every admissible `k`-set to occupy at most `480`
residue classes mod `2310`, so its `k` elements are packed at density `≤ 480/2310 = 16/77`
and must span at least `77(k − 480)/16`. The `p = 11` rung above `eight_mul_A_ge`
(`8·A(k) ≥ 35(k − 48)`). -/
theorem sixteen_mul_A_ge (k : ℕ) : 77 * (k - 480) ≤ 16 * A k := by
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem k
  have h := admissible_eleven_le_sup ha
  rw [hcard, hsup] at h
  exact h

/-- **The slope-`77/16` bound beats the slope-`35/8` bound past `k = 4800`.** For every
`k ≥ 4801`, `77(k − 480) > 70(k − 48) = 2·35(k − 48)`, so `sixteen_mul_A_ge` strictly
improves the (two-times) slope-`35/8` bound `eight_mul_A_ge`. Below `k = 4801` the
slope-`35/8` bound is still sharper; the crossover reflects the larger constant offset
(`−480` vs `−48`) that the extra prime `11` costs. -/
theorem eleven_bound_gt_seven_bound {k : ℕ} (hk : 4801 ≤ k) :
    70 * (k - 48) < 77 * (k - 480) := by omega

end Erdos1204
