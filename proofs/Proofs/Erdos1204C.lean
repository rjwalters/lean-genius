import Proofs.Erdos1204Problem

/-
# Erdős #1204 — a slope-`3` general lower bound `A(k) ≥ 3(k − 2)`

`Erdos1204Problem.lean` records two *general* lower bounds on the minimal diameter
`A(k)`:

* `sub_one_le_A`      : `A(k) ≥ k − 1`   (the trivial packing bound), and
* `two_mul_sub_one_le_A` : `A(k) ≥ 2(k − 1)`  (the prime `2` forces a single parity).

Here we sharpen the *slope* from `2` to `3` by using the primes `2` **and** `3`
simultaneously. An admissible set misses a residue class modulo `2` (so it occupies
at most one class mod `2`) and misses a class modulo `3` (at most two classes mod `3`);
by CRT its elements therefore occupy at most `1 · 2 = 2` residue classes modulo `6`.
Pigeonholing, one of those two classes holds at least `⌈k/2⌉` of the `k` elements, and
those elements — all congruent mod `6` — are `6`-separated, spanning a diameter of at
least `6(⌈k/2⌉ − 1) ≥ 3(k − 2)`.

The result:

* `admissible_three_sub_two_le_sup` : any admissible set has `sup ≥ 3(card − 2)`;
* `three_mul_sub_two_le_A`          : `A(k) ≥ 3(k − 2)`.

For `k ≥ 5` this strictly improves `2(k − 1)` (since `3(k − 2) > 2(k − 1) ⇔ k > 4`),
i.e. it is the leading joint prime-`{2,3}` contribution toward the conjectured
`A(k) ∼ k log k`. It remains far below the truth (which grows super-linearly), and the
sharp small values `A(5) = 12, A(6) = 16, …` are established separately; this is a clean
*asymptotic slope* improvement provable uniformly in `k`.

Everything is axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace Erdos1204

open Finset

/- ## A spacing lemma for a single residue class

If every element of a finite set of naturals is congruent modulo `d`, the `card`
distinct elements are `d`-separated, so the maximum is at least `d(card − 1)`. This is
the exact generalization of `admissible_diam_ge` (the `d = 2` parity case) to an
arbitrary modulus. -/

/-- **Spacing in one residue class.** If all elements of `b` are congruent modulo
`d > 0`, then `b.sup id ≥ d · (card − 1)`: the map `x ↦ (x − min)/d` injects `b` into
`{0, …, (sup − min)/d}`, so `card ≤ (sup − min)/d + 1`, whence `d(card − 1) ≤ sup`. -/
theorem same_mod_sup_ge {b : Finset ℕ} {d : ℕ} (hd : 0 < d)
    (hmod : ∀ x ∈ b, ∀ y ∈ b, (x : ZMod d) = (y : ZMod d)) :
    d * (b.card - 1) ≤ b.sup id := by
  classical
  rcases b.eq_empty_or_nonempty with rfl | hne
  · simp
  · -- every element is `≥ min` and `≡ min (mod d)`, hence `d ∣ x - min`
    have hdvd : ∀ x ∈ b, d ∣ (x - b.min' hne) := by
      intro x hx
      have hmx : b.min' hne ≤ x := b.min'_le x hx
      have hpar : ((b.min' hne : ℕ) : ZMod d) = (x : ZMod d) :=
        hmod _ (b.min'_mem hne) _ hx
      rw [ZMod.natCast_eq_natCast_iff] at hpar
      exact (Nat.modEq_iff_dvd' hmx).mp hpar
    -- `x ↦ (x - min)/d` maps `b` into `range ((sup - min)/d + 1)` ...
    have hmono : ∀ x ∈ b, (x - b.min' hne) / d ∈
        Finset.range ((b.sup id - b.min' hne) / d + 1) := by
      intro x hx
      rw [Finset.mem_range]
      have hxM : x ≤ b.sup id := Finset.le_sup (f := id) hx
      have hmx : b.min' hne ≤ x := b.min'_le x hx
      have hd2 : (x - b.min' hne) / d ≤ (b.sup id - b.min' hne) / d :=
        Nat.div_le_div_right (by omega)
      exact Nat.lt_succ_of_le hd2
    -- ... and is injective (distinct multiples of `d` give distinct quotients)
    have hinj : Set.InjOn (fun x => (x - b.min' hne) / d) b := by
      intro x hx y hy hxy
      simp only at hxy
      have hmx : b.min' hne ≤ x := b.min'_le x hx
      have hmy : b.min' hne ≤ y := b.min'_le y hy
      obtain ⟨u, hu⟩ := hdvd x hx
      obtain ⟨v, hv⟩ := hdvd y hy
      rw [hu, hv, Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd] at hxy
      have hxeq : x - b.min' hne = y - b.min' hne := by rw [hu, hv, hxy]
      omega
    have hcard : b.card ≤ (b.sup id - b.min' hne) / d + 1 := by
      have h := Finset.card_le_card_of_injOn
        (f := fun x => (x - b.min' hne) / d)
        (t := Finset.range ((b.sup id - b.min' hne) / d + 1)) hmono hinj
      simpa using h
    calc d * (b.card - 1)
        ≤ d * ((b.sup id - b.min' hne) / d) :=
          Nat.mul_le_mul (le_refl d) (tsub_le_iff_right.mpr hcard)
      _ ≤ b.sup id - b.min' hne := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
      _ ≤ b.sup id := Nat.sub_le _ _

/- ## The joint prime-`{2, 3}` count

An admissible set misses one class mod `2` and one class mod `3`; via the residue pair
`x ↦ (x mod 2, x mod 3)` it lands in a fixed `2`-element subset of `ZMod 2 × ZMod 3`
(one surviving class mod `2`, two mod `3`). This is a finite check. -/

/-- Missing one class mod `2` and one class mod `3` leaves exactly `1 · 2 = 2` residue
pairs in `ZMod 2 × ZMod 3`. -/
theorem two_classes_prod :
    ∀ (s : ZMod 2) (u : ZMod 3),
      (Finset.univ.filter (fun q : ZMod 2 × ZMod 3 => q.1 ≠ s ∧ q.2 ≠ u)).card = 2 := by
  decide

/- ## The joint prime-`{2, 3}` lower bound -/

/-- **Slope-`3` lower bound on the diameter.** Every admissible set satisfies
`sup ≥ 3(card − 2)`. Missing a class mod `2` and mod `3`, its elements occupy at most
two residue classes modulo `6`; the larger class holds `≥ ⌈card/2⌉` elements, `6`-spaced,
so `sup ≥ 6(⌈card/2⌉ − 1) ≥ 3(card − 2)`. -/
theorem admissible_three_sub_two_le_sup {a : Finset ℕ} (ha : Admissible a) :
    3 * (a.card - 2) ≤ a.sup id := by
  classical
  rcases Nat.lt_or_ge a.card 3 with hsmall | hbig
  · -- `card ≤ 2` ⇒ `3(card − 2) = 0`
    have : 3 * (a.card - 2) = 0 := by omega
    rw [this]; exact Nat.zero_le _
  · -- pull out the missed classes mod 2 and mod 3
    obtain ⟨r2, hr2⟩ := ha 2 (by norm_num)
    obtain ⟨r3, hr3⟩ := ha 3 (by norm_num)
    -- the residue-pair map and its 2-element target
    set f : ℕ → ZMod 2 × ZMod 3 := fun x => ((x : ZMod 2), (x : ZMod 3)) with hf_def
    set T : Finset (ZMod 2 × ZMod 3) :=
      Finset.univ.filter (fun q => q.1 ≠ r2 ∧ q.2 ≠ r3) with hT
    -- admissible elements map into `T`
    have hf : ∀ x ∈ a, f x ∈ T := by
      intro x hx
      rw [hf_def, hT]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr2 x hx, hr3 x hx⟩
    -- pigeonhole: some pair `p` has a fiber larger than `(card − 1)/2`
    have hlt : T.card * ((a.card - 1) / 2) < a.card := by
      rw [hT, two_classes_prod r2 r3]; omega
    obtain ⟨p, _, hp⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := f) hf hlt
    -- every element of that fiber shares the pair `p`
    have hpairmem : ∀ x ∈ a.filter (fun x => f x = p), f x = p :=
      fun x hx => (Finset.mem_filter.mp hx).2
    -- hence any two are congruent mod 2 and mod 3, so (CRT) congruent mod 6
    have hmod6 : ∀ x ∈ a.filter (fun x => f x = p), ∀ y ∈ a.filter (fun x => f x = p),
        (x : ZMod 6) = (y : ZMod 6) := by
      intro x hx y hy
      have hxy : f x = f y := (hpairmem x hx).trans (hpairmem y hy).symm
      rw [hf_def] at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨e2, e3⟩ := hxy
      rw [ZMod.natCast_eq_natCast_iff] at e2 e3
      rw [ZMod.natCast_eq_natCast_iff]
      have hcomb :=
        (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 2 3 by decide)).mp ⟨e2, e3⟩
      simpa using hcomb
    -- spacing within that class, transported back to `a`
    have hspace := same_mod_sup_ge (show (0 : ℕ) < 6 by norm_num) hmod6
    have hsub : a.filter (fun x => f x = p) ⊆ a := Finset.filter_subset _ _
    have hsuple : (a.filter (fun x => f x = p)).sup id ≤ a.sup id := Finset.sup_mono hsub
    omega

/-- **Slope-`3` lower bound on `A(k)`: `A(k) ≥ 3(k − 2)`.** The joint action of the
primes `2` and `3` forces every admissible `k`-set to occupy at most two residue classes
mod `6`, so its `k` elements are packed at density `≤ 2/6 = 1/3` and must span at least
`3(k − 2)`. This sharpens `two_mul_sub_one_le_A` (`A(k) ≥ 2(k − 1)`) for all `k ≥ 5`. -/
theorem three_mul_sub_two_le_A (k : ℕ) : 3 * (k - 2) ≤ A k := by
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem k
  have h := admissible_three_sub_two_le_sup ha
  rw [hcard, hsup] at h
  exact h

/-- **The slope-`3` bound beats the parity bound past `k = 4`.** For every `k ≥ 5`,
`3(k − 2) > 2(k − 1)`, so `three_mul_sub_two_le_A` is a strict improvement on
`two_mul_sub_one_le_A`. -/
theorem three_bound_gt_two_bound {k : ℕ} (hk : 5 ≤ k) :
    2 * (k - 1) < 3 * (k - 2) := by omega

end Erdos1204
