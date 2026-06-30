import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-
# Large-Prime-Factor Normality for Sylow p-Subgroups

## What This Proves

Let `G` be a finite group whose order factors as `|G| = p ^ a * m` with `p` prime
and `p ∤ m` (so `p ^ a` is the full `p`-part of `|G|` and `m` is its `p'`-cofactor).

**Main theorem (`sylow_normal`).**  If the cofactor is smaller than the prime,
`m < p`, then *the* Sylow `p`-subgroup is normal in `G`.

The whole argument is the elementary divisibility/congruence pinch on the Sylow
count `n_p := #(Sylow p G)`:

* **`sylow_card_eq`** — `|P| = p ^ a` (the Sylow subgroup carries the full `p`-part);
* **`sylow_index_eq`** — `[G : P] = m`;
* **`card_sylow_eq_one`** — `n_p ∣ [G : P] = m` forces `n_p ≤ m < p`, while Sylow's
  third theorem gives `n_p ≡ 1 (mod p)`; the only value `< p` that is `≡ 1 (mod p)`
  is `1`, hence `n_p = 1`;
* **`sylow_normal`** — a unique Sylow subgroup is normal.

## Why This Is Not Already in the Gallery / Mathlib

Mathlib supplies the two pillars (`card_sylow_modEq_one`, `Sylow.card_dvd_index`)
and the uniqueness↔normality bridge (`Sylow.normal_of_subsingleton`), but not this
packaged "`m < p ⟹ normal`" criterion.  It is the clean cofactor-below-the-prime
slice of the Sylow normality landscape:

* sibling `sylow-theorem-oq-01` runs the count analysis for groups of order `p·q`;
* sibling `sylow-theorem-oq-02-oq-01` characterises global nilpotency by
  `n_p = 1` for *every* prime.

Here a *single* numerical hypothesis `m < p` on the cofactor collapses the count for
the prime `p` alone, with no restriction on the `p`-power exponent `a`.

## Sharpness

The bound is tight in spirit: the inequality used is exactly `n_p ≤ m < p`, so once
`m ≥ p` the value `n_p = p + 1` (for instance) is no longer excluded by the
congruence `n_p ≡ 1 (mod p)`, and normality can genuinely fail.
-/

namespace SylowLargePrimeFactor

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The order of a Sylow `p`-subgroup of a group of order `p ^ a * m`
(with `p ∤ m`) is exactly the full `p`-part `p ^ a`. -/
theorem sylow_card_eq {p a m : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card G = p ^ a * m) (hpm : ¬ p ∣ m) (P : Sylow p G) :
    Nat.card P = p ^ a := by
  -- `m ≠ 0` because the group is nonempty and finite.
  have hm : m ≠ 0 := by
    have hpos : 0 < p ^ a * m := hcard ▸ Nat.card_pos
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hpos
    · exact h.ne'
  rw [P.card_eq_multiplicity, hcard]
  congr 1
  -- `(p ^ a * m).factorization p = a`.
  have hppow : (p ^ a).factorization p = a := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, hp.out.factorization,
        Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  have hmfact : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpm
  rw [Nat.factorization_mul (pow_ne_zero a hp.out.ne_zero) hm, Finsupp.add_apply,
      hppow, hmfact, add_zero]

/-- The index of a Sylow `p`-subgroup of a group of order `p ^ a * m`
(with `p ∤ m`) is exactly the `p'`-cofactor `m`. -/
theorem sylow_index_eq {p a m : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card G = p ^ a * m) (hpm : ¬ p ∣ m) (P : Sylow p G) :
    (P : Subgroup G).index = m := by
  have hmul := Subgroup.card_mul_index (P : Subgroup G)
  rw [sylow_card_eq hcard hpm P, hcard] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos a) hmul

/-- **The count collapses.**  When the `p'`-cofactor `m` is smaller than `p`, the
number of Sylow `p`-subgroups is forced to `1`: it divides `m` (so is `≤ m < p`)
yet is `≡ 1 (mod p)`, and `1` is the only such value below `p`. -/
theorem card_sylow_eq_one {p a m : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card G = p ^ a * m) (hpm : ¬ p ∣ m) (hm : m < p) :
    Nat.card (Sylow p G) = 1 := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  -- `m > 0` from finiteness/nonemptiness.
  have hm0 : 0 < m := by
    have hpos : 0 < p ^ a * m := hcard ▸ Nat.card_pos
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hpos
    · exact h
  -- `n_p ∣ m`.
  have hdvd : Nat.card (Sylow p G) ∣ m := by
    have h := P.card_dvd_index
    rwa [sylow_index_eq hcard hpm P] at h
  -- hence `n_p ≤ m < p`.
  have hlt : Nat.card (Sylow p G) < p :=
    lt_of_le_of_lt (Nat.le_of_dvd hm0 hdvd) hm
  -- Sylow's congruence `n_p ≡ 1 (mod p)`, read off below `p`.
  have hmod := card_sylow_modEq_one p G
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp.out.one_lt] at hmod
  exact hmod

/-- **Main theorem — Large-Prime-Factor Normality.**  If `|G| = p ^ a * m` with
`p` prime, `p ∤ m`, and `m < p`, then every Sylow `p`-subgroup `P` is normal
(there is in fact only one). -/
theorem sylow_normal {p a m : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card G = p ^ a * m) (hpm : ¬ p ∣ m) (hm : m < p)
    (P : Sylow p G) : (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_eq_one hcard hpm hm)).1
  exact Sylow.normal_of_subsingleton P

/-- Existence form: such a group has a normal Sylow `p`-subgroup. -/
theorem exists_normal_sylow {p a m : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card G = p ^ a * m) (hpm : ¬ p ∣ m) (hm : m < p) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  exact ⟨P, sylow_normal hcard hpm hm P⟩

end SylowLargePrimeFactor
