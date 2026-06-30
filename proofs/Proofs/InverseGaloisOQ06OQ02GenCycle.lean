import Mathlib

/-
# The permutation-representation bridge, in arbitrary cycle length: an `n`-cycle on the roots ⟹ `n ∣ |Gal(p)|`

`InverseGaloisOQ06OQ02GalAction.lean` proved the *deterministic half* of the mod-7
Dedekind route in the **3-cycle** form only:

  if some `σ ∈ Gal(p)` acts on the roots of `p` (in a splitting field `E`) as a
  **three-cycle**, then `3 ∣ |Gal(p)|`.

That `3` is special to `q mod 7 = (X-5)(X-6)·(cubic)`, whose factorization type
`(1,1,3)` produces a 3-cycle Frobenius. But Dedekind's theorem governs **every**
prime: at an unramified prime `p` whose squarefree reduction has an irreducible
factor of degree `d` (and the rest splitting into other-degree factors that give a
single cycle on the corresponding roots), the Frobenius acts as a `d`-cycle and so
forces `d ∣ |Gal(p)|`. This file proves that general statement against the real
`Polynomial.Gal` type, of which the 3-cycle bridge is the `d = 3` instance.

The generalization is not idle: the A5-realizability target `InverseGaloisA5.lean`
already machine-checks **two** Frobenius divisibility inputs, `3 ∣ |Gal|` (the open
axiom) **and** `5 ∣ |Gal|` (`five_dvd_gal_card`, proved). The `5` likewise arises
from a degree-5 factor — i.e. a **5-cycle** Frobenius — so the same deterministic
eliminator, taken at `d = 5`, is the faithful interface for *that* input too. A
single uniform lemma now subsumes both prime contributions to `|Gal|`.

## What is proved (0-axiom / 0-sorry)

* `orderOf_galActionHom`                       — order-preservation of the (injective)
                                                 permutation representation.
* `dvd_card_gal_of_galActionHom_cycleType`     — the **general** bridge: if the root
                                                 permutation has cycle type `{n}`
                                                 (a single `n`-cycle), then `n ∣ |Gal(p)|`.
* `dvd_card_gal_of_galActionHom_isCycle`       — support-cardinality form: if the root
                                                 permutation is *any* cycle, its support
                                                 size divides `|Gal(p)|`.
* `three_dvd_card_gal_of_galActionHom_cycleType`,
  `five_dvd_card_gal_of_galActionHom_cycleType` — the `n = 3` (cubic factor, mod 7) and
                                                 `n = 5` (quintic factor) corollaries,
                                                 the faithful interfaces for the two
                                                 Frobenius inputs of `InverseGaloisA5`.

## Honest scope

Like its sibling, this file does **NOT** discharge `three_dvd_gal_card`: it is the
deterministic group-theoretic eliminator, now in full cycle-length generality. The
sole residual input remains part (A) — producing the Frobenius permutation itself
(a genuine Mathlib 4.26 gap, Dedekind's theorem), owned by `inverse-galois-a5-oq-01`.

## Key Mathlib API

- `Polynomial.Gal.galActionHom : p.Gal →* Equiv.Perm (p.rootSet E)` (injective: faithful)
- `orderOf_injective`, `orderOf_dvd_card`
- `Equiv.Perm.lcm_cycleType : σ.cycleType.lcm = orderOf σ`
- `Equiv.Perm.IsCycle.orderOf : σ.IsCycle → orderOf σ = σ.support.card`
-/

set_option linter.unusedVariables false

open Polynomial Polynomial.Gal Equiv Equiv.Perm

open scoped Classical

namespace InverseGaloisOQ06OQ02GenCycle

variable {F : Type*} [Field F] {p : F[X]} {E : Type*} [Field E] [Algebra F E]
  [Fact ((p.map (algebraMap F E)).Splits)]

/-- **The permutation representation is order-preserving.** Restated locally (the
one-line consequence of injectivity of `galActionHom`) so this file is standalone:
the order of a Galois element equals the order of the permutation it induces on the
roots of `p` in `E`. -/
theorem orderOf_galActionHom (σ : p.Gal) :
    orderOf (galActionHom p E σ) = orderOf σ :=
  orderOf_injective (galActionHom p E) (galActionHom_injective p E) σ

/-- **General faithful Dedekind bridge (cycle-type form).** If some `σ ∈ Gal(p)` acts
on the roots of `p` in `E` as a single **`n`-cycle** (cycle type `{n}`), then
`n ∣ |Gal(p)|`.

This is the exact shape Dedekind's theorem delivers at an unramified prime: the
Frobenius cycle type equals the multiset of mod-`p` factorization degrees, and a
single irreducible factor of degree `n` (with the rest assembling into one cycle on
the remaining roots, or — as for `q mod 7` — into fixed points) is an `n`-cycle.
The order of the permutation equals the `lcm` of its cycle type, here `lcm {n} = n`;
order-preservation transports this to `orderOf σ = n`, and `orderOf_dvd_card` finishes. -/
theorem dvd_card_gal_of_galActionHom_cycleType
    {σ : p.Gal} {n : ℕ} (hσ : (galActionHom p E σ).cycleType = {n}) :
    n ∣ Fintype.card p.Gal := by
  have hord : orderOf σ = n := by
    rw [← orderOf_galActionHom (E := E) σ, ← Equiv.Perm.lcm_cycleType, hσ]
    simp [Multiset.lcm_singleton]
  rw [← hord]
  exact orderOf_dvd_card

/-- **General faithful Dedekind bridge (cycle / support-cardinality form).** If some
`σ ∈ Gal(p)` acts on the roots of `p` in `E` as *any* cycle, then the number of
roots it moves — the cardinality of its support — divides `|Gal(p)|`. For a Frobenius
arising from a single irreducible factor this support size is exactly that factor's
degree. -/
theorem dvd_card_gal_of_galActionHom_isCycle
    {σ : p.Gal} (hσ : (galActionHom p E σ).IsCycle) :
    (galActionHom p E σ).support.card ∣ Fintype.card p.Gal := by
  have h : orderOf σ = (galActionHom p E σ).support.card := by
    rw [← orderOf_galActionHom (E := E) σ]; exact hσ.orderOf
  rw [← h]
  exact orderOf_dvd_card

/-- **`n = 3` corollary — the cubic factor, mod 7.** Recovers the
`InverseGaloisOQ06OQ02GalAction` 3-cycle bridge as the degree-3 instance of the
general lemma: the faithful interface for the open axiom `three_dvd_gal_card`. -/
theorem three_dvd_card_gal_of_galActionHom_cycleType
    {σ : p.Gal} (hσ : (galActionHom p E σ).cycleType = {3}) :
    3 ∣ Fintype.card p.Gal :=
  dvd_card_gal_of_galActionHom_cycleType hσ

/-- **`n = 5` corollary — a quintic factor.** The degree-5 instance: a 5-cycle
Frobenius forces `5 ∣ |Gal(p)|`. For `q` this is the faithful root-permutation
interface for the *already-proven* constraint `five_dvd_gal_card : 5 ∣ |q.Gal|`,
showing the same deterministic eliminator covers both prime inputs of
`InverseGaloisA5`. -/
theorem five_dvd_card_gal_of_galActionHom_cycleType
    {σ : p.Gal} (hσ : (galActionHom p E σ).cycleType = {5}) :
    5 ∣ Fintype.card p.Gal :=
  dvd_card_gal_of_galActionHom_cycleType hσ

end InverseGaloisOQ06OQ02GenCycle
