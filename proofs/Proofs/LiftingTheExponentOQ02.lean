import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-
# Lifting the Exponent Lemma — the even prime `p = 2`

The odd-prime Lifting the Exponent Lemma (LTE) computes `vₚ(xⁿ - yⁿ)` as
`vₚ(x - y) + vₚ(n)`. For `p = 2` the lemma is famously different: when the
exponent `n` is **even**, an extra `v₂(x + y)` term appears and the count is
shifted by one,

  v₂(xⁿ - yⁿ) + 1 = v₂(x + y) + v₂(x - y) + v₂(n).

Mathlib proves the `emultiplicity` (`ℕ∞`-valued) version over `ℤ`
(`Int.two_pow_sub_pow`) and a `padicValNat` version over `ℕ`
(`padicValNat.pow_two_sub_pow`). It does **not** provide the `padicValInt`
(integer `vₚ`) form, which is the natural shape for the lemma's usual
applications over `ℤ`. This file fills that gap:

* `two_lte_emultiplicity` — the `ℕ∞` statement, re-exported.
* `two_pow_sub_pow_ne_zero` — `xⁿ - yⁿ ≠ 0`, extracted from finiteness of the
  valuation rather than assumed.
* `two_lte_multiplicity` — the `ℕ`-valued (`multiplicity`) form.
* `two_lte_padicValInt` — the schoolbook integer form
  `v₂(xⁿ - yⁿ) + 1 = v₂(x + y) + v₂(x - y) + v₂(n)` with `padicValInt` /
  `padicValNat`.
* `two_lte_pow_dvd` — the explicit divisibility consequence.

The mathematical core is Mathlib's; the contribution is the descent from the
extended valuation to the finite integer `vₚ` form, including manufacturing the
finiteness facts that make the natural-number identity meaningful, plus the
companion entry to the odd-prime case.
-/

namespace LiftingTheExponentOQ02

variable {x y : ℤ} {n : ℕ}

/-- **LTE for `p = 2` (`emultiplicity` form).** For `2 ∣ x - y`, `2 ∤ x` and even
`n`,
`emultiplicity 2 (xⁿ - yⁿ) + 1 = emultiplicity 2 (x + y) + emultiplicity 2 (x - y)
+ emultiplicity 2 n`. A direct re-export of `Int.two_pow_sub_pow`. -/
theorem two_lte_emultiplicity
    (hxy : (2 : ℤ) ∣ x - y) (hx : ¬(2 : ℤ) ∣ x) (hn : Even n) :
    emultiplicity 2 (x ^ n - y ^ n) + 1
      = emultiplicity 2 (x + y) + emultiplicity 2 (x - y) + emultiplicity (2 : ℤ) n :=
  Int.two_pow_sub_pow hxy hx hn

/-- Under the LTE hypotheses with `x + y ≠ 0`, `x - y ≠ 0` and `n ≠ 0`, the
difference `xⁿ - yⁿ` is nonzero: its `2`-adic valuation is finite (forced by the
LTE equation), so it cannot vanish. -/
theorem two_pow_sub_pow_ne_zero
    (hxy : (2 : ℤ) ∣ x - y) (hx : ¬(2 : ℤ) ∣ x) (hn : Even n)
    (hadd : x + y ≠ 0) (hsub : x - y ≠ 0) (hn0 : n ≠ 0) :
    x ^ n - y ^ n ≠ 0 := by
  intro h0
  have key := Int.two_pow_sub_pow hxy hx hn
  have hfin_add : FiniteMultiplicity (2 : ℤ) (x + y) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hadd⟩
  have hfin_sub : FiniteMultiplicity (2 : ℤ) (x - y) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hsub⟩
  have hfin_n : FiniteMultiplicity (2 : ℤ) (n : ℤ) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, by exact_mod_cast hn0⟩
  rw [h0, emultiplicity_zero, top_add,
      hfin_add.emultiplicity_eq_multiplicity, hfin_sub.emultiplicity_eq_multiplicity,
      hfin_n.emultiplicity_eq_multiplicity, ← Nat.cast_add, ← Nat.cast_add] at key
  exact (ENat.coe_ne_top _) key.symm

/-- **LTE for `p = 2` (`ℕ`-valued form).** With `x + y ≠ 0`, `x - y ≠ 0` and
`n ≠ 0` ensuring finiteness,
`multiplicity 2 (xⁿ - yⁿ) + 1 = multiplicity 2 (x + y) + multiplicity 2 (x - y)
+ multiplicity 2 n`. -/
theorem two_lte_multiplicity
    (hxy : (2 : ℤ) ∣ x - y) (hx : ¬(2 : ℤ) ∣ x) (hn : Even n)
    (hadd : x + y ≠ 0) (hsub : x - y ≠ 0) (hn0 : n ≠ 0) :
    multiplicity (2 : ℤ) (x ^ n - y ^ n) + 1
      = multiplicity (2 : ℤ) (x + y) + multiplicity (2 : ℤ) (x - y)
        + multiplicity (2 : ℤ) (n : ℤ) := by
  have key := Int.two_pow_sub_pow hxy hx hn
  have hne0 : x ^ n - y ^ n ≠ 0 := two_pow_sub_pow_ne_zero hxy hx hn hadd hsub hn0
  have hfin_lhs : FiniteMultiplicity (2 : ℤ) (x ^ n - y ^ n) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hne0⟩
  have hfin_add : FiniteMultiplicity (2 : ℤ) (x + y) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hadd⟩
  have hfin_sub : FiniteMultiplicity (2 : ℤ) (x - y) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hsub⟩
  have hfin_n : FiniteMultiplicity (2 : ℤ) (n : ℤ) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, by exact_mod_cast hn0⟩
  rw [hfin_lhs.emultiplicity_eq_multiplicity, hfin_add.emultiplicity_eq_multiplicity,
      hfin_sub.emultiplicity_eq_multiplicity, hfin_n.emultiplicity_eq_multiplicity] at key
  exact_mod_cast key

/-- **LTE for `p = 2` (schoolbook integer `v₂` form).** For `2 ∣ x - y`, `2 ∤ x`,
even `n`, and `x + y ≠ 0`, `x - y ≠ 0`, `n ≠ 0`,
`v₂(xⁿ - yⁿ) + 1 = v₂(x + y) + v₂(x - y) + v₂(n)`,
with `v₂` on `ℤ` given by `padicValInt 2` and on `ℕ` by `padicValNat 2`. -/
theorem two_lte_padicValInt
    (hxy : (2 : ℤ) ∣ x - y) (hx : ¬(2 : ℤ) ∣ x) (hn : Even n)
    (hadd : x + y ≠ 0) (hsub : x - y ≠ 0) (hn0 : n ≠ 0) :
    padicValInt 2 (x ^ n - y ^ n) + 1
      = padicValInt 2 (x + y) + padicValInt 2 (x - y) + padicValNat 2 n := by
  have hne0 : x ^ n - y ^ n ≠ 0 := two_pow_sub_pow_ne_zero hxy hx hn hadd hsub hn0
  have hm := two_lte_multiplicity hxy hx hn hadd hsub hn0
  -- the n-term: multiplicity (2:ℤ) ↑n = padicValNat 2 n
  have hnterm : multiplicity (2 : ℤ) (n : ℤ) = padicValNat 2 n := by
    rw [← padicValInt.of_nat (p := 2) (n := n)]
    exact (padicValInt.of_ne_one_ne_zero (by decide) (by exact_mod_cast hn0)).symm
  rw [padicValInt.of_ne_one_ne_zero (by decide) hne0,
      padicValInt.of_ne_one_ne_zero (by decide) hadd,
      padicValInt.of_ne_one_ne_zero (by decide) hsub, ← hnterm]
  exact hm

/-- **Explicit divisibility from the `p = 2` LTE.** `2` divides `xⁿ - yⁿ` to the
power `v₂(x + y) + v₂(x - y) + v₂(n) - 1`. -/
theorem two_lte_pow_dvd
    (hxy : (2 : ℤ) ∣ x - y) (hx : ¬(2 : ℤ) ∣ x) (hn : Even n)
    (hadd : x + y ≠ 0) (hsub : x - y ≠ 0) (hn0 : n ≠ 0) :
    (2 : ℤ) ^ (padicValInt 2 (x + y) + padicValInt 2 (x - y) + padicValNat 2 n - 1)
      ∣ x ^ n - y ^ n := by
  have hne0 : x ^ n - y ^ n ≠ 0 := two_pow_sub_pow_ne_zero hxy hx hn hadd hsub hn0
  have hv : padicValInt 2 (x + y) + padicValInt 2 (x - y) + padicValNat 2 n - 1
      = padicValInt 2 (x ^ n - y ^ n) := by
    rw [← two_lte_padicValInt hxy hx hn hadd hsub hn0]; omega
  rw [hv, padicValInt.of_ne_one_ne_zero (by decide) hne0]
  exact pow_multiplicity_dvd _ _

end LiftingTheExponentOQ02
