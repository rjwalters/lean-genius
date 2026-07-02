import Mathlib

/-!
# Kummer–Dedekind Step 1 brick for inertia degrees (inverse-Galois A₅, OQ-04)

This file isolates the *first* of the three abstract steps in the ongoing effort to
discharge the last assumption of `Proofs.InverseGaloisA5`,

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

The companion file `Proofs.InverseGaloisA5DedekindInstantiation` reduces that axiom to the
single sharp arithmetic fact `3 ∣ Ideal.inertiaDegIn (7) (𝓞 q.SplittingField)` at an
unramified prime over `7`, and its "residual gap" note spells out a three-step route:

1. **Kummer–Dedekind** — the prime of `𝓞 ℚ(α)` matching an *irreducible cubic factor* of
   `q mod 7` has inertia degree `3`;
2. **inertia-degree multiplicativity in a tower** — lifts that to a prime of the splitting
   field;
3. **Galois uniformity** — spreads it to all primes over `7`, giving `3 ∣ inertiaDegIn (7)`.

Steps **2 and 3** were packaged, `0`-axiom, in `Proofs.DedekindInertiaTower`
(`inertiaDeg_dvd_inertiaDegIn`). This file packages step **1** as a single, fully general,
`0`-axiom existence/divisibility statement about an *arbitrary* number field `K`, algebraic
integer `θ`, and rational prime `p` not dividing the Kummer–Dedekind exponent of `θ`:

* `exists_prime_inertiaDeg_eq_natDegree`: every monic irreducible factor `Q` of
  `minpoly ℤ θ` modulo `p` is matched by a maximal prime `P` of `𝓞 K` over `(p)` with
  `inertiaDeg (p) P = Q.natDegree`;
* `exists_prime_dvd_inertiaDeg_of_dvd_natDegree`: the divisibility shape the A₅ argument
  consumes — if `d ∣ Q.natDegree`, then some prime `P` over `(p)` has `d ∣ inertiaDeg (p) P`.

Feeding such a `P` into `DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg` promotes
`d ∣ inertiaDeg (p) P` all the way to `d ∣ inertiaDegIn (p)` on the Galois splitting field.
Together with the already-verified arithmetic factorization
`Proofs.InverseGaloisA5DedekindMod7` (cubic factor of `q mod 7`, degree `3`), the two
bricks reduce the residual gap to the tower/top-prime *wiring* alone. Only the ordinary
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) are used — no `sorry`,
no new `axiom`.

The whole content is a thin, reusable repackaging of Mathlib's
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` bijection and its residual-degree
computation `inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'`, exposed in the
divisibility currency the inverse-Galois–via–Frobenius argument actually needs.
-/

open Polynomial NumberField Ideal RingOfIntegers

namespace DedekindKummerStep1

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

/-- **Kummer–Dedekind Step 1 (existence form).** Let `K` be a number field, `θ` an algebraic
integer of `K`, and `p` a rational prime that does not divide the Kummer–Dedekind exponent
of `θ` (equivalently, `p` does not divide the conductor `[𝓞 K : ℤ[θ]]`). Then every monic
irreducible factor `Q` of `minpoly ℤ θ` modulo `p` is matched by a maximal prime `P` of
`𝓞 K` lying over the rational prime `(p)`, whose inertia degree equals the degree of `Q`.

This is the concrete splitting datum consumed by the inverse-Galois argument: an
irreducible degree-`d` factor mod `p` produces a prime of inertia degree exactly `d`.

The witness is `(primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩`; primality and
lying-over are its `primesOver`-membership components, maximality is
`Ideal.isMaximal_of_mem_primesOver`, and the inertia-degree computation is Mathlib's
`inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'`. -/
theorem exists_prime_inertiaDeg_eq_natDegree
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.LiesOver (span {(p : ℤ)}) ∧
      inertiaDeg (span {(p : ℤ)}) P = Q.natDegree := by
  refine ⟨((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ :
      Ideal (𝓞 K)), ?_, ?_,
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ⟩
  · exact Ideal.isMaximal_of_mem_primesOver
      ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩).2
  · exact ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩).2.2

/-- **Kummer–Dedekind Step 1 (divisibility form).** If a natural number `d` divides the
degree of a monic irreducible factor `Q` of `minpoly ℤ θ` modulo `p` (with `p` not dividing
the exponent of `θ`), then some maximal prime `P` of `𝓞 K` over `(p)` has
`d ∣ inertiaDeg (p) P`.

This is exactly the hypothesis of `DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg`:
in the A₅ application `d = 3` and `Q` is the irreducible cubic factor of `q mod 7`, so the
two bricks compose to `3 ∣ inertiaDegIn (7) (𝓞 q.SplittingField)`. -/
theorem exists_prime_dvd_inertiaDeg_of_dvd_natDegree
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) {d : ℕ} (hd : d ∣ Q.natDegree) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.LiesOver (span {(p : ℤ)}) ∧
      d ∣ inertiaDeg (span {(p : ℤ)}) P := by
  obtain ⟨P, hPmax, hPlo, hPdeg⟩ := exists_prime_inertiaDeg_eq_natDegree hp hQ
  exact ⟨P, hPmax, hPlo, hPdeg ▸ hd⟩

end DedekindKummerStep1
