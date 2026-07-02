import Mathlib
import Proofs.DedekindKummerStep1
import Proofs.DedekindInertiaTower

/-!
# Composing Kummer–Dedekind Step 1 with the inertia-tower brick (inverse-Galois A₅, OQ-04)

This file closes the *gluing* half of the residual gap in the ongoing effort to discharge
the last assumption of `Proofs.InverseGaloisA5`,

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

`Proofs.InverseGaloisA5DedekindInstantiation` reduces that axiom to the single arithmetic
fact `3 ∣ Ideal.inertiaDegIn (7) (𝓞 q.SplittingField)` at an unramified prime over `7`, and
its "residual gap" note lays out a three-step route:

1. **Kummer–Dedekind** — the prime of `𝓞 ℚ(α)` matching an irreducible cubic factor of
   `q mod 7` has inertia degree `3` (packaged in `Proofs.DedekindKummerStep1`);
2. **inertia-degree multiplicativity in a tower** — lifts that to a prime of the splitting
   field;
3. **Galois uniformity** — spreads it to all primes over `7`
   (steps 2–3 packaged in `Proofs.DedekindInertiaTower`).

The two bricks were proved separately, `0`-axiom. This file **composes them**: given a
tower `ℤ ⊆ 𝓞 K ⊆ T` with `T / ℤ` Galois (`T` integral over `𝓞 K`), an algebraic integer
`θ` of `K` whose Kummer–Dedekind exponent is prime to `p`, and a monic irreducible factor
`Q` of `minpoly ℤ θ` modulo `p` with `d ∣ Q.natDegree`, we obtain

```
d ∣ Ideal.inertiaDegIn (span {(p : ℤ)}) T.
```

The only new ingredient beyond the two bricks is **going up**
(`Ideal.exists_maximal_ideal_liesOver_of_isIntegral`): the Step-1 prime `P` of `𝓞 K` over
`(p)` sits below *some* maximal prime `Q'` of the integral extension `T`, which is exactly
the intermediate datum the tower brick consumes. Only the ordinary foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) are used — no `sorry`, no new `axiom`.

## Effect on the A₅ residual gap

Instantiating with `K = ℚ(α)` (`α` a root of `q`), `T = 𝓞 q.SplittingField`, `G = q.Gal`,
`p = 7`, `Q =` the irreducible cubic factor of `q mod 7`
(`Proofs.InverseGaloisA5DedekindMod7`), and `d = 3` collapses the whole three-step route to
a *single* statement. What remains to feed this lemma is purely the concrete number-theoretic
wiring:

* the tower/`IsGaloisGroup` instances for `ℤ ⊆ 𝓞 ℚ(α) ⊆ 𝓞 q.SplittingField`;
* `7 ∤ RingOfIntegers.exponent α` (from `7 ∤ disc q = 32000²`);
* the identification of the cubic factor as an element of `RingOfIntegers.monicFactorsMod α 7`.

None of those require any further abstract inertia/tower reasoning: that part is now fully
machine-checked and packaged here.
-/

open Polynomial NumberField Ideal RingOfIntegers

namespace DedekindKummerToTower

/-- The rational prime `(p)` is a maximal ideal of `ℤ`: `span {(p : ℤ)}` is prime because
`p` is prime (`Ideal.span_singleton_prime`), and a nonzero prime of the one-dimensional
domain `ℤ` is maximal (`Ideal.IsPrime.isMaximal`). -/
theorem span_p_isMaximal {p : ℕ} [Fact (Nat.Prime p)] : (span {(p : ℤ)}).IsMaximal := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  refine ((Ideal.span_singleton_prime hprime.ne_zero).mpr hprime).isMaximal ?_
  simpa [Ideal.span_singleton_eq_bot] using hprime.ne_zero

/-- **Kummer–Dedekind Step 1 composed with the inertia tower.**

Let `ℤ ⊆ 𝓞 K ⊆ T` be a tower with `T` integral over `𝓞 K` and `T / ℤ` Galois with group
`G`. Let `θ` be an algebraic integer of the number field `K` whose Kummer–Dedekind exponent
is not divisible by the rational prime `p`. If a natural number `d` divides the degree of a
monic irreducible factor `Q` of `minpoly ℤ θ` modulo `p`, then

```
d ∣ Ideal.inertiaDegIn (span {(p : ℤ)}) T.
```

Proof: `DedekindKummerStep1.exists_prime_dvd_inertiaDeg_of_dvd_natDegree` produces a maximal
prime `P` of `𝓞 K` over `(p)` with `d ∣ inertiaDeg (p) P`; going up
(`Ideal.exists_maximal_ideal_liesOver_of_isIntegral`) supplies a maximal prime `Q'` of `T`
over `P`; and `DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg` promotes
`d ∣ inertiaDeg (p) P` to `d ∣ inertiaDegIn (p) T`. -/
theorem dvd_inertiaDegIn_of_dvd_natDegree_factor
    {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]
    {T : Type*} [CommRing T]
    [Algebra (𝓞 K) T] [IsScalarTower ℤ (𝓞 K) T]
    [Algebra.IsIntegral (𝓞 K) T] [FaithfulSMul (𝓞 K) T]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G ℤ T]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) {d : ℕ} (hd : d ∣ Q.natDegree) :
    d ∣ Ideal.inertiaDegIn (span {(p : ℤ)}) T := by
  -- Step 1: a maximal prime `P` of `𝓞 K` over `(p)` with `d ∣ inertiaDeg (p) P`.
  obtain ⟨P, hPmax, hPlo, hPdvd⟩ :=
    DedekindKummerStep1.exists_prime_dvd_inertiaDeg_of_dvd_natDegree hp hQ hd
  haveI := hPmax
  haveI := hPlo
  -- Going up: a maximal prime `Q'` of the integral extension `T` lying over `P`.
  obtain ⟨Q', hQ'max, hQ'lo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 K) (S := T) P
  haveI := hQ'max
  haveI := hQ'lo
  haveI : (span {(p : ℤ)}).IsMaximal := span_p_isMaximal
  -- Tower + Galois uniformity: promote to `inertiaDegIn (p) T`.
  exact DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg G (span {(p : ℤ)}) P Q' hPdvd

end DedekindKummerToTower
