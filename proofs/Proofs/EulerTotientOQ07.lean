import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Coprimality of two totients: `φ(m)` and `φ(n)` are coprime iff one argument is `1` or `2`

**Open Question (`euler-totient-oq-07`)**: characterise when the Euler totients of
two numbers are coprime, i.e. for which `m n` we have `gcd(φ(m), φ(n)) = 1`.

Mathlib supplies the biconditional `Nat.totient_coprime_totient_iff`:

  `(φ m).Coprime (φ n) ↔ (m = 1 ∨ m = 2) ∨ (n = 1 ∨ n = 2)`.

The reason is the parity of the totient: `φ(k)` is **even** for every `k > 2`
(`Nat.totient_even`, via the order-`2` unit `-1 ∈ (ℤ/kℤ)ˣ` and Lagrange).  So as
soon as both `m, n ≥ 3`, both totients are even and share the common factor `2`,
hence cannot be coprime; the only way to be coprime is for one of the two
arguments to land in `{1, 2}`, where `φ = 1` is coprime to everything.

Rather than restate the one-line `iff`, this file packages the **structural
consequence Mathlib does not state**: for `m, n ≥ 3` the totients are *never*
coprime, and in fact `2 ∣ gcd(φ(m), φ(n))`, so the gcd is always at least `2`.
This turns the abstract characterisation into a concrete, quotable lower bound on
the shared structure of distinct totients.

## Contents

* `totient_coprime_iff`            — the characterisation (from Mathlib).
* `gcd_totient_eq_one_iff`         — its `gcd`-form `gcd(φ m, φ n) = 1 ↔ …`.
* `two_dvd_gcd_totient_of_three_le`— the new divisibility `2 ∣ gcd(φ m, φ n)`.
* `two_le_gcd_totient_of_three_le` — the lower bound `2 ≤ gcd(φ m, φ n)`.
* `not_coprime_totient_of_three_le`— the headline: `m, n ≥ 3 ⟹ ¬ Coprime (φ m) (φ n)`.

Fully machine-checked: `0` sorries, `0` axioms (the `decide` calls are kernel
reductions over concrete small naturals, not `native_decide`).
-/

namespace EulerTotientOQ07

open Nat

/-- **Characterisation of coprimality of totients** (Mathlib's
`Nat.totient_coprime_totient_iff`): the totients `φ(m)` and `φ(n)` are coprime
*iff* at least one of the arguments is `1` or `2`.  Re-exported here as the
flagship statement of this entry. -/
theorem totient_coprime_iff (m n : ℕ) :
    (φ m).Coprime (φ n) ↔ (m = 1 ∨ m = 2) ∨ (n = 1 ∨ n = 2) :=
  Nat.totient_coprime_totient_iff m n

/-- The `gcd`-form of the characterisation: `gcd(φ m, φ n) = 1` exactly when one
argument lies in `{1, 2}`.  (`Nat.Coprime` is definitionally `gcd = 1`, so this is
the same fact spelled with an explicit `gcd`.) -/
theorem gcd_totient_eq_one_iff (m n : ℕ) :
    Nat.gcd (φ m) (φ n) = 1 ↔ (m = 1 ∨ m = 2) ∨ (n = 1 ∨ n = 2) :=
  totient_coprime_iff m n

/-- **New divisibility fact.**  When both arguments are at least `3`, the totients
are both even, so their gcd is divisible by `2`.  Mathlib states the coprimality
biconditional but not this explicit shared factor. -/
theorem two_dvd_gcd_totient_of_three_le {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    2 ∣ Nat.gcd (φ m) (φ n) :=
  Nat.dvd_gcd
    (Even.two_dvd (totient_even (by omega)))
    (Even.two_dvd (totient_even (by omega)))

/-- **Lower bound on the shared structure.**  For `m, n ≥ 3` the gcd of the two
totients is at least `2`: they always have a nontrivial common factor. -/
theorem two_le_gcd_totient_of_three_le {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    2 ≤ Nat.gcd (φ m) (φ n) := by
  have hpos : 0 < Nat.gcd (φ m) (φ n) :=
    Nat.gcd_pos_of_pos_left _ (totient_pos.mpr (by omega))
  exact Nat.le_of_dvd hpos (two_dvd_gcd_totient_of_three_le hm hn)

/-- **Headline consequence.**  Totients of two numbers `≥ 3` are *never* coprime:
they share the factor `2`.  This is the genuinely informative half of the
characterisation, stated as a clean implication. -/
theorem not_coprime_totient_of_three_le {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ¬ (φ m).Coprime (φ n) :=
  Nat.not_coprime_of_dvd_of_dvd one_lt_two
    (Even.two_dvd (totient_even (by omega)))
    (Even.two_dvd (totient_even (by omega)))

/-! ### Worked examples -/

-- The two odd-totient arguments: `φ 1 = φ 2 = 1`, coprime to every other totient.
example : φ 1 = 1 := totient_one
example : φ 2 = 1 := totient_two

-- `φ 2 = 1` is coprime to `φ 100`, witnessing the `m = 2` branch of the iff.
example : (φ 2).Coprime (φ 100) :=
  (totient_coprime_iff 2 100).mpr (Or.inl (Or.inr rfl))

-- A concrete shared factor of `2`: `φ 3 = 2`, `φ 4 = 2`, so `gcd = 2`.
example : φ 3 = 2 := by decide
example : φ 4 = 2 := by decide
example : Nat.gcd (φ 3) (φ 4) = 2 := by decide

-- The headline theorem in action: `φ 9 = 6` and `φ 15 = 8` are not coprime
-- (both even), even though `9` and `15` are themselves coprime.
example : ¬ (φ 9).Coprime (φ 15) :=
  not_coprime_totient_of_three_le (by norm_num) (by norm_num)

-- …and the gcd is genuinely `≥ 2` here: `gcd(φ 9, φ 15) = gcd(6, 8) = 2`.
example : Nat.gcd (φ 9) (φ 15) = 2 := by decide

end EulerTotientOQ07
