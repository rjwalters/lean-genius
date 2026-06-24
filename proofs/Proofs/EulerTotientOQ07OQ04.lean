import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

/-!
# Setwise coprimality of a finite family of totients

**Open Question (`euler-totient-oq-07-oq-04`)**: extend the *pairwise* coprimality
criterion for Euler totients to an arbitrary finite family.

The parent entry (`euler-totient-oq-07`) packages Mathlib's
`Nat.totient_coprime_totient_iff`:

  `gcd(φ m, φ n) = 1 ↔ (m = 1 ∨ m = 2) ∨ (n = 1 ∨ n = 2)`,

together with the structural fact that for `m, n ≥ 3` the gcd is always even.
The driving phenomenon is the **parity of the totient**: `φ(k)` is even for every
`k > 2` (`Nat.totient_even`), and `φ(0) = 0` is even as well, so the *only* values
of `k` with an **odd** totient are `k ∈ {1, 2}` (where `φ(k) = 1`).

This file lifts the criterion from two arguments to a finite family
`a : ι → ℕ` indexed by a `Finset s`.  The natural object is the setwise gcd
`s.gcd (fun i ↦ φ (a i))`, i.e. the largest integer dividing *every* totient in
the family.  The headline result is the clean biconditional

  `s.gcd (fun i ↦ φ (a i)) = 1 ↔ ∃ i ∈ s, a i = 1 ∨ a i = 2`.

Read left to right: a finite family of totients is setwise coprime **iff at least
one argument lands in `{1, 2}`** (contributing the unit `φ = 1`).  Equivalently,
the moment *every* argument avoids `{1, 2}` the whole family shares the factor `2`.

This is genuinely stronger than the pairwise statement — the pairwise case is the
two-element specialization (`example` at the end) — and Mathlib has no
finite-family form.

## Contents

* `two_dvd_totient_of_ne_one_two`   — `a ∉ {1,2} ⟹ 2 ∣ φ a` (the parity engine).
* `two_dvd_gcd_totient_family`      — `(∀ i ∈ s, a i ∉ {1,2}) ⟹ 2 ∣ s.gcd (φ ∘ a)`.
* `gcd_totient_family_eq_one_iff`   — the headline biconditional.
* `gcd_totient_family_ne_one_of_forall` — its contrapositive, stated directly.

Fully machine-checked: `0` sorries, `0` axioms (the `decide` calls reduce
concrete small naturals in the kernel, not `native_decide`).
-/

namespace EulerTotientOQ07OQ04

open Nat

variable {ι : Type*}

/-- **The parity engine.**  Every natural other than `1` and `2` has an *even*
totient: `φ(0) = 0` is even, and `φ(k)` is even for all `k > 2`
(`Nat.totient_even`).  Hence `2 ∣ φ(a)` whenever `a ∉ {1, 2}`. -/
theorem two_dvd_totient_of_ne_one_two {a : ℕ} (h1 : a ≠ 1) (h2 : a ≠ 2) :
    2 ∣ φ a := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · simp [h0]
  · exact (totient_even (by omega)).two_dvd

/-- **Shared factor of a totient family.**  If *every* argument avoids `{1, 2}`,
then the totients all share the factor `2`, so `2` divides their setwise gcd.
(For the empty family this is `2 ∣ 0`, which holds.) -/
theorem two_dvd_gcd_totient_family (s : Finset ι) (a : ι → ℕ)
    (h : ∀ i ∈ s, a i ≠ 1 ∧ a i ≠ 2) :
    2 ∣ s.gcd (fun i ↦ φ (a i)) := by
  apply Finset.dvd_gcd
  intro i hi
  obtain ⟨h1, h2⟩ := h i hi
  exact two_dvd_totient_of_ne_one_two h1 h2

/-- **Headline: setwise coprimality criterion for a finite family of totients.**
The totients `{φ(a i) : i ∈ s}` are setwise coprime (their gcd is `1`) **iff at
least one argument `a i` lies in `{1, 2}`**, where the totient equals the unit `1`.

Equivalently: as soon as every argument avoids `{1, 2}`, the family shares the
factor `2` (`two_dvd_gcd_totient_family`) and is never setwise coprime.  This is
the finite-family generalization of the pairwise `Nat.totient_coprime_totient_iff`. -/
theorem gcd_totient_family_eq_one_iff (s : Finset ι) (a : ι → ℕ) :
    s.gcd (fun i ↦ φ (a i)) = 1 ↔ ∃ i ∈ s, a i = 1 ∨ a i = 2 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have h2 : (2 : ℕ) ∣ s.gcd (fun i ↦ φ (a i)) :=
      two_dvd_gcd_totient_family s a hcon
    rw [h] at h2
    exact absurd h2 (by decide)
  · rintro ⟨i, hi, hai⟩
    have hphi : φ (a i) = 1 := by rcases hai with h | h <;> simp [h]
    have hdvd : s.gcd (fun j ↦ φ (a j)) ∣ φ (a i) := Finset.gcd_dvd hi
    rw [hphi] at hdvd
    exact Nat.dvd_one.mp hdvd

/-- **Contrapositive form.**  If every argument of the family avoids `{1, 2}`, then
the totients are *not* setwise coprime: their gcd is at least `2`. -/
theorem gcd_totient_family_ne_one_of_forall (s : Finset ι) (a : ι → ℕ)
    (h : ∀ i ∈ s, a i ≠ 1 ∧ a i ≠ 2) :
    s.gcd (fun i ↦ φ (a i)) ≠ 1 := by
  intro hcontra
  obtain ⟨i, hi, hai⟩ := (gcd_totient_family_eq_one_iff s a).mp hcontra
  obtain ⟨h1, h2⟩ := h i hi
  rcases hai with h' | h' <;> [exact h1 h'; exact h2 h']

/-! ### Recovering the pairwise parent and worked examples -/

/-- The pairwise criterion `euler-totient-oq-07` is the two-element
specialization: take the family `![m, n]` indexed by `Fin 2`. -/
example (m n : ℕ) :
    (Finset.univ : Finset (Fin 2)).gcd (fun i ↦ φ (![m, n] i)) = 1 ↔
      (m = 1 ∨ m = 2) ∨ (n = 1 ∨ n = 2) := by
  rw [gcd_totient_family_eq_one_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    fin_cases i <;> simp_all
  · rintro (h | h)
    · exact ⟨0, Finset.mem_univ _, by simpa using h⟩
    · exact ⟨1, Finset.mem_univ _, by simpa using h⟩

-- A three-element family hitting `{1,2}`: `φ 2 = 1` forces setwise coprimality,
-- regardless of the other (large) arguments.
example : (Finset.univ : Finset (Fin 3)).gcd (fun k ↦ φ (![100, 2, 999] k)) = 1 := by
  rw [gcd_totient_family_eq_one_iff]
  exact ⟨1, Finset.mem_univ _, Or.inr (by decide)⟩

-- A family entirely outside `{1,2}` is never setwise coprime: `φ 3 = φ 4 = φ 9 = even`.
example : (Finset.univ : Finset (Fin 3)).gcd (fun k ↦ φ (![3, 4, 9] k)) ≠ 1 := by
  apply gcd_totient_family_ne_one_of_forall
  decide

-- The concrete shared factor of `2` for that family: `gcd(φ3, φ4, φ9) = gcd(2,2,6) = 2`.
example : (Finset.univ : Finset (Fin 3)).gcd (fun k ↦ φ (![3, 4, 9] k)) = 2 := by decide

end EulerTotientOQ07OQ04
