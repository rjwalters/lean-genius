import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# The power map `x ↦ xⁿ` is a bijection on a finite group iff `gcd(n, |G|) = 1`

## What This Proves

The sibling file `CauchyGroupTheoremOQ01OQ01` proves that in a finite group of
**odd** order the squaring map `x ↦ x²` is a bijection — the `n = 2` instance of
the dividing line drawn by Cauchy's theorem. This file proves the full
characterization for an arbitrary exponent `n`:

> **`pow_bijective_iff_coprime`.** For a finite group `G` and `n : ℕ`, the `n`-th
> power map `x ↦ xⁿ` is a bijection of `G` **iff** `Nat.Coprime n (|G|)`.

This holds for *every* finite group, abelian or not — even though `x ↦ xⁿ` is not
a homomorphism when `G` is non-abelian, bijectivity is governed purely by the
arithmetic of `n` against `|G|`. None of this is packaged in Mathlib.

### The two directions

* **Coprime ⟹ bijective** (`pow_surjective_of_coprime`, `pow_bijective_of_coprime`).
  When `gcd(n, |G|) = 1`, Euler's theorem (`Nat.ModEq.pow_totient`) gives
  `n ^ φ(|G|) ≡ 1 [MOD |G|]`, so the map `x ↦ x ^ (n ^ (φ(|G|) − 1))` is a
  two-sided inverse of `x ↦ xⁿ`: chaining the two exponents multiplies to
  `n ^ φ(|G|)`, which acts as the identity because every element's order divides
  `|G|`. Concretely the explicit inverse exponent makes the map a genuine
  `Equiv` (`powEquivOfCoprime`).

* **Bijective ⟹ coprime** (`not_pow_injective_of_not_coprime`). The
  contrapositive is Cauchy. If `gcd(n, |G|) > 1` it has a prime factor `p`, and
  Cauchy (`exists_prime_orderOf_dvd_card`) produces an element `g` of order `p`.
  Since `p ∣ n` we get `gⁿ = 1 = 1ⁿ` with `g ≠ 1`, so the power map collapses two
  distinct elements and cannot be injective.

### Consequences

* **Sharpened squaring boundary** (`sq_bijective_iff_odd_card`). Specializing to
  `n = 2` recovers and upgrades the sibling's odd-order result to an *iff*:
  squaring is a bijection iff `|G|` is odd.
* The general statement subsumes Fermat-style "every element is a unique `n`-th
  root" facts whenever `n` is coprime to the group order.

## Context

The `n = 2` story is the boundary between odd-order groups (squaring bijective,
no involutions) and even-order groups (Cauchy yields an involution). The present
result identifies the analogous boundary for an arbitrary exponent: the power map
`x ↦ xⁿ` is a permutation of the group exactly on the coprime side, and Cauchy's
theorem is precisely the obstruction on the non-coprime side.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01

variable {G : Type*}

/-! ### A modular reduction lemma for exponents -/

/-- If two exponents are congruent modulo `|G|`, the corresponding powers of any
element agree. This is the engine behind the coprime direction: it lets us
replace an exponent by anything congruent to it mod `|G|`, since every element's
order divides `|G|` (`orderOf_dvd_card`). -/
theorem pow_eq_of_modEq_card [Group G] [Fintype G] {a b : ℕ} (x : G)
    (h : a ≡ b [MOD Fintype.card G]) : x ^ a = x ^ b := by
  have hdvd : orderOf x ∣ Fintype.card G := orderOf_dvd_card
  exact pow_eq_pow_iff_modEq.mpr (h.of_dvd hdvd)

/-! ### Coprime exponent ⟹ the power map is a bijection -/

/-- **The inverse exponent acts as the identity.** When `gcd(n, |G|) = 1`,
`x ^ (n ^ φ(|G|)) = x` for every `x`, because `n ^ φ(|G|) ≡ 1 [MOD |G|]` by
Euler's theorem. -/
theorem pow_pow_totient_eq_self [Group G] [Fintype G] {n : ℕ}
    (hcop : Nat.Coprime n (Fintype.card G)) (x : G) :
    x ^ (n ^ Nat.totient (Fintype.card G)) = x := by
  have heul : n ^ Nat.totient (Fintype.card G) ≡ 1 [MOD Fintype.card G] :=
    Nat.ModEq.pow_totient hcop
  calc x ^ (n ^ Nat.totient (Fintype.card G))
      = x ^ 1 := pow_eq_of_modEq_card x heul
    _ = x := pow_one x

/-- **Coprime exponent ⟹ the power map is surjective.** With explicit preimage
`y ↦ y ^ (n ^ (φ(|G|) − 1))`. -/
theorem pow_surjective_of_coprime [Group G] [Fintype G] {n : ℕ}
    (hcop : Nat.Coprime n (Fintype.card G)) :
    Function.Surjective (fun x : G => x ^ n) := by
  have hφ : 0 < Nat.totient (Fintype.card G) :=
    Nat.totient_pos.mpr (Fintype.card_pos_iff.mpr ⟨1⟩)
  intro y
  refine ⟨y ^ (n ^ (Nat.totient (Fintype.card G) - 1)), ?_⟩
  simp only
  rw [← pow_mul]
  have hexp : n ^ (Nat.totient (Fintype.card G) - 1) * n
      = n ^ Nat.totient (Fintype.card G) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hexp]
  exact pow_pow_totient_eq_self hcop y

/-- **Coprime exponent ⟹ the power map is bijective.** Surjectivity plus
finiteness. -/
theorem pow_bijective_of_coprime [Group G] [Fintype G] {n : ℕ}
    (hcop : Nat.Coprime n (Fintype.card G)) :
    Function.Bijective (fun x : G => x ^ n) :=
  ⟨(Finite.injective_iff_surjective).mpr (pow_surjective_of_coprime hcop),
   pow_surjective_of_coprime hcop⟩

/-- The `n`-th power map packaged as a permutation `G ≃ G` when `n` is coprime to
`|G|`. -/
noncomputable def powEquivOfCoprime [Group G] [Fintype G] {n : ℕ}
    (hcop : Nat.Coprime n (Fintype.card G)) : G ≃ G :=
  Equiv.ofBijective (fun x : G => x ^ n) (pow_bijective_of_coprime hcop)

/-! ### Non-coprime exponent ⟹ the power map is not injective (Cauchy) -/

/-- **The Cauchy obstruction.** If `gcd(n, |G|) ≠ 1`, the power map `x ↦ xⁿ` is
not injective: a prime `p` dividing the gcd yields, by Cauchy's theorem, an
element `g` of order `p ≠ 1` with `gⁿ = 1 = 1ⁿ`. -/
theorem not_pow_injective_of_not_coprime [Group G] [Fintype G] {n : ℕ}
    (hncop : ¬ Nat.Coprime n (Fintype.card G)) :
    ¬ Function.Injective (fun x : G => x ^ n) := by
  -- Extract a common prime factor of `n` and `|G|`.
  have hgcd_ne : Nat.gcd n (Fintype.card G) ≠ 1 := hncop
  set p := (Nat.gcd n (Fintype.card G)).minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime hgcd_ne
  have hpn : p ∣ n := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hpc : p ∣ Fintype.card G := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  -- Cauchy: an element of order `p`.
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hpc
  -- `g ^ n = 1` because `orderOf g = p ∣ n`.
  have hgn : g ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp (hg ▸ hpn)
  -- `g ≠ 1` because its order is the prime `p`.
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    exact hp.ne_one hg.symm
  -- The power map sends both `g` and `1` to `1`.
  intro hinj
  exact hg1 (hinj (by simp only [hgn, one_pow]))

/-! ### The characterization -/

/-- **The `n`-th power map is a bijection iff `gcd(n, |G|) = 1`.** The headline
result: bijectivity of `x ↦ xⁿ` on a finite group is governed entirely by the
coprimality of the exponent with the group order. The forward direction is
Cauchy's theorem (contrapositive); the reverse is Euler's theorem. -/
theorem pow_bijective_iff_coprime [Group G] [Fintype G] {n : ℕ} :
    Function.Bijective (fun x : G => x ^ n) ↔ Nat.Coprime n (Fintype.card G) := by
  constructor
  · intro hbij
    by_contra hncop
    exact not_pow_injective_of_not_coprime hncop hbij.injective
  · exact pow_bijective_of_coprime

/-! ### Specialization: the squaring boundary, sharpened to an iff -/

/-- **Squaring is a bijection iff the order is odd.** The `n = 2` case of the
characterization, recovering and upgrading the sibling file's one-directional
odd-order result to an equivalence. -/
theorem sq_bijective_iff_odd_card [Group G] [Fintype G] :
    Function.Bijective (fun x : G => x ^ 2) ↔ Odd (Fintype.card G) := by
  rw [pow_bijective_iff_coprime, Nat.coprime_two_left]

/-! ### Concrete instances -/

/-- In `ZMod 5` (order coprime to `3`), tripling `y ↦ 3 • y` is a bijection,
witnessed by kernel `decide` (no `native_decide`). -/
theorem zmod5_triple_bijective :
    Function.Bijective (fun x : ZMod 5 => 3 • x) := by
  constructor
  · decide
  · decide

end CauchyGroupTheoremOQ01OQ01OQ01
