import Mathlib
import Proofs.InverseGaloisA5

/-
# The remaining axiom has no slack: `three_dvd_gal_card ↔ |q.Gal| = 60`

`InverseGaloisA5.lean` reduces A₅-realizability of
`q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5` to a single axiom

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

Every other ingredient of `|q.Gal| = 60` is machine-checked there:

* `five_dvd_gal_card`      : `5 ∣ |q.Gal|`
* `gal_card_dvd_60_proved` : `|q.Gal| ∣ 60`   (Vandermonde / all-even argument)
* `gal_card_ne_15`         : `|q.Gal| ≠ 15`    (no `S₅`-subgroup of order 15)
* `gal_card_ne_30`         : `|q.Gal| ≠ 30`    (no `S₅`-subgroup of order 30, A₅ simple)

This file records, **without using the axiom**, that these constraints pin the
group so tightly that the lone axiom is *logically equivalent* to the full
conclusion: given everything `InverseGaloisA5` already proves,

  `3 ∣ |q.Gal|   ↔   |q.Gal| = 60`.

In other words the remaining gap has **no slack** — `three_dvd_gal_card` is
exactly as strong as the A₅-realizability target, neither more nor less. The
forward direction is the `q_gal_card` divisor argument with the axiom replaced by
a hypothesis, so it does **not** depend on `three_dvd_gal_card` (verified by
`#print axioms`). It does, however, inherit `Lean.ofReduceBool` /
`Lean.trustCompiler` from the `InverseGaloisA5` constraint lemmas
`gal_card_dvd_60_proved`, `gal_card_ne_15`, `gal_card_ne_30`, which are
discharged by `native_decide` — so these results are *not* axiom-free, they carry
the same `native_decide` trust base as the underlying A₅ entry. The point is
narrower and exact: they remove the dependence on the *open* axiom
`three_dvd_gal_card`, replacing it with an explicit hypothesis.

Combining with the concrete Galois bridge of
`InverseGaloisOQ06OQ02GalBridge.lean`, we obtain the sharpest statement of the
residual input on the mod-7 Dedekind route:

  *A single Galois automorphism acting on the five roots as a 3-cycle (the
  Frobenius element at the unramified prime 7, whose existence is the only open
  step) already forces `|q.Gal| = 60`.*

Nothing here discharges the axiom; it characterises precisely what the axiom buys.
-/

open Polynomial InverseGaloisA5

open scoped Classical

namespace InverseGaloisOQ06OQ02GapChar

/-- **Forward direction, axiom-free.** Given the machine-checked constraints of
`InverseGaloisA5` (`5 ∣ |q.Gal|`, `|q.Gal| ∣ 60`, `|q.Gal| ≠ 15`, `≠ 30`), the
hypothesis `3 ∣ |q.Gal|` forces `|q.Gal| = 60`. This is the body of
`InverseGaloisA5.q_gal_card` with the axiom `three_dvd_gal_card` replaced by an
explicit hypothesis, so it does **not** depend on that axiom. -/
theorem card_eq_60_of_three_dvd (h3 : 3 ∣ Fintype.card q.Gal) :
    Fintype.card q.Gal = 60 := by
  have h15 : 15 ∣ Fintype.card q.Gal :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5)
      h3 five_dvd_gal_card
  have h_dvd := gal_card_dvd_60_proved
  have hne15 := gal_card_ne_15
  have hne30 := gal_card_ne_30
  obtain ⟨k, hk⟩ := h15
  have hk_pos : 0 < k := by
    have hpos : 0 < Fintype.card q.Gal := Fintype.card_pos
    rw [hk] at hpos; omega
  have hk_dvd : k ∣ 4 := by
    rw [hk] at h_dvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 15) h_dvd
  have hk_le : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk_dvd
  have hk_ne1 : k ≠ 1 := fun h => by rw [h, Nat.mul_one] at hk; exact hne15 hk
  have hk_ne2 : k ≠ 2 := fun h => by subst h; norm_num at hk; exact hne30 hk
  interval_cases k <;> simp_all

/-- **The remaining axiom has no slack.** Modulo the constraints already proved
in `InverseGaloisA5`, the single open axiom `three_dvd_gal_card` is logically
equivalent to the A₅-realizability target `|q.Gal| = 60`. The reverse direction
is `3 ∣ 60`; the forward direction is `card_eq_60_of_three_dvd`, which is
independent of `three_dvd_gal_card` (it inherits only the `native_decide` trust
base — `Lean.ofReduceBool` — of the A₅ constraint lemmas). -/
theorem three_dvd_card_iff_card_eq_60 :
    3 ∣ Fintype.card q.Gal ↔ Fintype.card q.Gal = 60 :=
  ⟨card_eq_60_of_three_dvd, fun h => h ▸ (by norm_num)⟩

/-- **Sharpest form of the residual input.** A single Galois automorphism acting
on the five roots as a 3-cycle — the Frobenius element at the unramified prime 7,
matching the verified `(1,1,3)` factorization `q_mod7_factor_type`, and the sole
remaining open step — already forces the full count `|q.Gal| = 60`. This inlines
the concrete deterministic-half bridge (injectivity of `galActionHom` carries the
root-permutation cycle type to `orderOf σ = 3`, then `orderOf_dvd_card`) into
`card_eq_60_of_three_dvd`. Like the rest of the file it is independent of the
open axiom `three_dvd_gal_card`, inheriting only the `native_decide` trust base
(`Lean.ofReduceBool`) of the A₅ constraint lemmas. -/
theorem card_eq_60_of_exists_galAction_threeCycle
    (h : ∃ σ : q.Gal, (Polynomial.Gal.galActionHom q q.SplittingField σ).IsThreeCycle) :
    Fintype.card q.Gal = 60 := by
  obtain ⟨σ, hσ⟩ := h
  have horder : orderOf σ = 3 := by
    rw [← orderOf_injective _ (Polynomial.Gal.galActionHom_injective q q.SplittingField) σ]
    exact hσ.orderOf
  exact card_eq_60_of_three_dvd (horder ▸ orderOf_dvd_card)

end InverseGaloisOQ06OQ02GapChar
