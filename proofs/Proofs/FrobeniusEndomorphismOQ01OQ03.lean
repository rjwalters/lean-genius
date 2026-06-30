/-
  Frobenius is a monomorphism on a domain and an automorphism on a finite field.

  Building on `FrobeniusEndomorphismOQ01`, which packages the Frobenius
  `x ↦ x ^ p` as a *ring homomorphism* in prime characteristic, this file
  records the two structural facts that determine its image and kernel:

    * **Injectivity over a domain.**  On any integral domain `R` of
      characteristic `p` the Frobenius is injective, i.e. a *monomorphism*.
      The reason is that an integral domain is reduced (no nonzero nilpotents),
      and `x ^ p = y ^ p ⇒ (x - y) ^ p = 0 ⇒ x = y`.  Note injectivity can fail
      badly without the reduced hypothesis: over `ZMod 4` (not a domain) we have
      `0² = 2² = 0` even though the relevant power map collapses elements.

    * **Bijectivity over a finite field.**  A finite field is a finite domain,
      so the injective Frobenius is automatically *surjective* — an
      *automorphism*.  This is the abstract source of the fact that every
      element of a finite field of characteristic `p` is a `p`-th power, and it
      packages the Frobenius as a genuine ring **equivalence** `K ≃+* K`.

  Everything is Mathlib-backed (`frobenius_inj`, `Finite.injective_iff_bijective`,
  `RingEquiv.ofBijective`) and fully verified: 0 sorries, 0 axioms, no
  `native_decide`.
-/
import Mathlib

namespace FrobeniusEndomorphismOQ01OQ03

/-! ### Frobenius is a monomorphism on an integral domain -/

section Domain

variable (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [ExpChar R p]

/-- **Frobenius is injective on an integral domain.**  In characteristic `p`,
the map `x ↦ x ^ p` is a monomorphism: an integral domain is reduced, so the
only `p`-th root of `0` is `0`, and `(x - y) ^ p = x ^ p - y ^ p`. -/
theorem frobenius_injective : Function.Injective (frobenius R p) :=
  frobenius_inj R p

/-- The injectivity, spelled out as a cancellation rule on `p`-th powers:
`x ^ p = y ^ p ↔ x = y` over an integral domain. -/
theorem pow_p_left_inj {x y : R} : x ^ p = y ^ p ↔ x = y := by
  constructor
  · intro h
    exact frobenius_injective R p (by simpa only [frobenius_def] using h)
  · rintro rfl; rfl

/-- The Frobenius has trivial kernel: `x ^ p = 0 ↔ x = 0`. -/
theorem pow_p_eq_zero_iff {x : R} : x ^ p = 0 ↔ x = 0 := by
  have h := pow_p_left_inj R p (x := x) (y := 0)
  rwa [zero_pow (expChar_pos R p).ne'] at h

end Domain

/-! ### Frobenius is an automorphism on a finite field -/

section FiniteField

variable (K : Type*) [Field K] [Finite K] (p : ℕ) [ExpChar K p]

/-- **Frobenius is bijective on a finite field.**  A finite field is a finite
integral domain, so the injective Frobenius (a monomorphism) is automatically
surjective — hence an automorphism. -/
theorem frobenius_bijective : Function.Bijective (frobenius K p) :=
  Finite.injective_iff_bijective.mp (frobenius_injective K p)

/-- The Frobenius is surjective on a finite field: **every element is a `p`-th
power**, `∀ y, ∃ x, x ^ p = y`. -/
theorem exists_pow_p (y : K) : ∃ x : K, x ^ p = y := by
  obtain ⟨x, hx⟩ := (frobenius_bijective K p).surjective y
  exact ⟨x, by simpa only [frobenius_def] using hx⟩

/-- The Frobenius packaged as a **ring automorphism** `K ≃+* K` of a finite
field. -/
noncomputable def frobeniusEquiv : K ≃+* K :=
  RingEquiv.ofBijective (frobenius K p) (frobenius_bijective K p)

@[simp]
theorem frobeniusEquiv_apply (x : K) : frobeniusEquiv K p x = x ^ p := rfl

/-- The automorphism agrees with the underlying ring hom. -/
theorem coe_frobeniusEquiv : ⇑(frobeniusEquiv K p) = frobenius K p := rfl

end FiniteField

/-! ### Concrete checks -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- On `ZMod 5` the Frobenius `x ↦ x⁵` is bijective (indeed the identity, by
Fermat). -/
theorem frobenius_bijective_zmod_five :
    Function.Bijective (frobenius (ZMod 5) 5) :=
  frobenius_bijective (ZMod 5) 5

/-- Every element of `ZMod 7` is a `7`-th power (here trivially, `a = a⁷`). -/
theorem exists_pow_seven_zmod_seven (y : ZMod 7) : ∃ x : ZMod 7, x ^ 7 = y :=
  exists_pow_p (ZMod 7) 7 y

end FrobeniusEndomorphismOQ01OQ03
