import Mathlib
import Proofs.DedekindInertiaTower

/-!
# Kummer–Dedekind step for the A₅ inverse-Galois inertia argument (OQ-04)

This file supplies **Step 1** of the residual gap in the ongoing effort to discharge the
last assumption of `Proofs.InverseGaloisA5`,

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

Prior sessions reduced that axiom, via
`Proofs.InverseGaloisA5DedekindInstantiation.three_dvd_gal_card_of_bridge` and the abstract
Dedekind–Frobenius bridge, to the single sharp arithmetic fact

```
3 ∣ Ideal.inertiaDegIn (Ideal.span {(7 : ℤ)}) (𝓞 q.SplittingField)
```

and `Proofs.DedekindInertiaTower` packaged the tower-multiplicativity + Galois-uniformity
half (steps 2–3): to prove `d ∣ inertiaDegIn p (𝓞 L)` it suffices to exhibit *one*
intermediate prime `P` of a subfield `K ⊆ L` with `d ∣ inertiaDeg p P`.

The remaining half — actually **producing** that intermediate prime with the right inertia
degree from the mod-`p` factorization of a defining polynomial — is Mathlib's specialized
Kummer–Dedekind criterion
`NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`: for a number
field `K` and an algebraic integer `θ` with `p ∤ RingOfIntegers.exponent θ`, each monic
irreducible factor `Q` of `minpoly ℤ θ` modulo `p` gives a prime of `𝓞 K` over `(p)` whose
inertia degree is exactly `deg (Q mod p)`.

## Main result

`dvd_inertiaDegIn_of_monicFactorMod` composes those two Mathlib/local facts into one
reusable lemma:

> Let `K ⊆ L` be number fields with `L / ℚ` Galois (Galois group `G` acting on `𝓞 L`, so
> `[IsGaloisGroup G ℤ (𝓞 L)]`). For `θ : 𝓞 K` with `p ∤ exponent θ` and a monic factor `Q`
> of `minpoly ℤ θ` mod `p`, the degree `deg (Q mod p)` divides `inertiaDegIn (p) (𝓞 L)`.

This is the shared blocker for the two open gallery problems `inverse-galois-a5-oq-01`
(OQ-04) and `abel-ruffini-oq-07`: instantiating with `K = ℚ(α)` (a root of the defining
quintic), `L =` its splitting field, `p = 7`, and `Q =` the irreducible **cubic** factor of
`q mod 7` (verified in `Proofs.InverseGaloisA5DedekindMod7`) yields
`3 ∣ inertiaDegIn (7) (𝓞 L)` — the sole remaining hypothesis of `three_dvd_gal_card_of_bridge`.

What still remains for a full axiom elimination is the *concrete* instantiation: realizing
`K = ℚ(α)` as an intermediate field of the splitting field, identifying `minpoly ℤ α` with
the integer model of `q`, and discharging `7 ∤ exponent α` (which follows from
`7 ∤ disc q = 32000²`). This file closes the abstract number-theoretic core; it introduces
no `axiom` and no `sorry`.

## Verification status

The proof is assembled entirely from named Mathlib declarations, each confirmed present in
the repository's pinned Mathlib (`inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`,
`Int.ideal_span_isMaximal_of_prime`, `Ideal.IsMaximal.of_liesOver_isMaximal`,
`Ideal.exists_ideal_over_maximal_of_isIntegral`, `RingOfIntegers.ker_algebraMap_eq_bot`) plus
the local brick `DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg`. It was **not
machine-checked in the session that wrote it**: the host Docker disk was full
(`docker-build.sh` failed with an overlayfs I/O error, host at 100% capacity — see #33336)
and the Aristotle MCP endpoint was unreachable. Build with
`./proofs/scripts/docker-build.sh Proofs.InverseGaloisA5DedekindKummer` once the host has
free disk before relying on it or flipping any gallery status.
-/

open Polynomial NumberField Ideal RingOfIntegers

namespace InverseGaloisA5DedekindKummer

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Kummer–Dedekind ⟶ inertia-degree divisibility for the splitting field.**

Let `K ⊆ L` be number fields with `L / ℚ` Galois, realized by a finite group `G` acting on
`𝓞 L` with `[IsGaloisGroup G ℤ (𝓞 L)]`. Let `θ : 𝓞 K`, `p` a rational prime not dividing
`RingOfIntegers.exponent θ`, and `Q : ℤ[X]` a lift of a monic irreducible factor of
`minpoly ℤ θ` modulo `p`. Then the degree of that factor divides the (Galois-invariant)
inertia degree of `p` in `𝓞 L`.

Proof: Kummer–Dedekind
(`NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`) produces a
prime `P` of `𝓞 K` over `(p)` with `inertiaDeg (p) P = deg (Q mod p)`; going-up
(`exists_ideal_over_maximal_of_isIntegral`) lifts it to a maximal prime `𝔮` of `𝓞 L` over
`P`; and `DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg` promotes the divisibility
through the Galois tower `ℤ ⊆ 𝓞 K ⊆ 𝓞 L`. -/
theorem dvd_inertiaDegIn_of_monicFactorMod
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G (𝓞 L)] [IsGaloisGroup G ℤ (𝓞 L)]
    {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p) :
    (Q.map (Int.castRingHom (ZMod p))).natDegree ∣
      Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) := by
  classical
  -- The Kummer–Dedekind prime `P` of `𝓞 K` over `(p)` matching the factor `Q`.
  set Pe := (primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ with hPe
  -- Its inertia degree over `ℤ` is the degree of the factor.
  have hdeg :
      Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) (Pe : Ideal (𝓞 K))
        = (Q.map (Int.castRingHom (ZMod p))).natDegree :=
    inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hp hQ
  -- `P` is prime and lies over `(p)`; since `(p)` is maximal in `ℤ`, `P` is maximal.
  haveI hPprime : (Pe : Ideal (𝓞 K)).IsPrime := Pe.2.1
  haveI hPlo : (Pe : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}) := Pe.2.2
  haveI hpmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  haveI hPmax : (Pe : Ideal (𝓞 K)).IsMaximal :=
    IsMaximal.of_liesOver_isMaximal (Pe : Ideal (𝓞 K)) (Ideal.span {(p : ℤ)})
  -- Going-up: lift `P` to a maximal prime `𝔮` of `𝓞 L`.
  obtain ⟨𝔮, h𝔮max, h𝔮comap⟩ :=
    exists_ideal_over_maximal_of_isIntegral (R := 𝓞 K) (S := 𝓞 L)
      (Pe : Ideal (𝓞 K)) (by rw [RingOfIntegers.ker_algebraMap_eq_bot K L]; exact bot_le)
  haveI : 𝔮.IsMaximal := h𝔮max
  haveI : 𝔮.LiesOver (Pe : Ideal (𝓞 K)) := ⟨h𝔮comap.symm⟩
  -- `ℤ ⊆ 𝓞 K ⊆ 𝓞 L` is a scalar tower (all structure maps are the canonical `ℤ`-casts).
  haveI : IsScalarTower ℤ (𝓞 K) (𝓞 L) :=
    IsScalarTower.of_algebraMap_eq fun n => by
      simp only [eq_intCast, map_intCast]
  -- Promote through the Galois tower.
  have hdvd :
      (Q.map (Int.castRingHom (ZMod p))).natDegree
        ∣ Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) (Pe : Ideal (𝓞 K)) := by
    rw [hdeg]
  exact DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg G
    (Ideal.span {(p : ℤ)}) (Pe : Ideal (𝓞 K)) 𝔮 hdvd

end InverseGaloisA5DedekindKummer
