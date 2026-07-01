import Mathlib
import Proofs.InverseGaloisA5

/-
# The mod-7 factorization keystone for the A₅ quintic (Inverse-Galois OQ-04)

`InverseGaloisA5` realizes `A₅` as a Galois group over `ℚ` using the quintic

```
q = X⁵ − 5X⁴ + 10X³ − 10X² + 25X − 5,
```

but its last input is the `axiom three_dvd_gal_card : 3 ∣ |q.Gal|`. The abstract
Dedekind–Frobenius bridge `DedekindFrobeniusBridge.orderOf_arithFrobAt_eq_inertiaDegIn`
(0 axioms) reduces that axiom to the single concrete number-theoretic fact

```
3 ∣ Ideal.inertiaDegIn (7) (𝓞 q.SplittingField),
```

and `InverseGaloisA5DedekindInstantiation.three_dvd_gal_card_of_bridge` shows this fact
suffices. The residual inertia computation goes, via Kummer–Dedekind, through the
factorization of `q` modulo `7`. This file supplies that **concrete arithmetic keystone**,
fully verified with `0` axioms and `0` sorries:

```
q ≡ (X − 5)(X − 6)(X³ + 6X² + 4X + 1)   (mod 7),   the cubic irreducible over 𝔽₇.
```

That is exactly Dedekind's "Frobenius cycle type `(1, 1, 3)` at `p = 7`" datum: the
irreducible cubic factor is the one whose associated prime of `𝓞 ℚ(α)` has inertia degree
`3`, feeding `3 ∣ inertiaDegIn (7)`.

This file does **not** by itself remove `three_dvd_gal_card`: bridging "`q` has an
irreducible cubic factor mod `7`" to "`3 ∣ inertiaDegIn (7) (𝓞 q.SplittingField)`" still
needs the Kummer–Dedekind conductor step
(`inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`, using `7 ∤ disc q = 32000²`)
plus the inertia-tower and `inertiaDegIn_eq_inertiaDeg` (Galois) identities. It pins down and
verifies the arithmetic input those steps consume.
-/

open Polynomial

namespace InverseGaloisA5DedekindMod7

/-- `7` is prime, so `ZMod 7` is a field (needed for the degree-`≤ 3` irreducibility test). -/
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The integer model of `q` (same coefficients as `InverseGaloisA5.q`, over `ℤ`). -/
noncomputable def qInt : ℤ[X] :=
  X ^ 5 - 5 * X ^ 4 + 10 * X ^ 3 - 10 * X ^ 2 + 25 * X - 5

/-- `qInt` is the integer model of the rational quintic `q`: casting `ℤ → ℚ` recovers `q`. -/
theorem qInt_map_rat :
    qInt.map (Int.castRingHom ℚ) = InverseGaloisA5.q := by
  simp only [qInt, InverseGaloisA5.q, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat,
    map_ofNat]

/-- The cubic factor of `q mod 7`, `X³ + 6X² + 4X + 1` over `𝔽₇ = ZMod 7`. -/
noncomputable def cubic7 : (ZMod 7)[X] :=
  X ^ 3 + 6 * X ^ 2 + 4 * X + 1

/-- Integer identity underlying the mod-`7` reduction: `q = (X−5)(X−6)(cubic) + 7 · R`
(all coefficients of `q − (X−5)(X−6)(cubic)` are divisible by `7`). Pure `ℤ[X]`
arithmetic, closed by `ring`. -/
theorem qInt_eq_factor_add_seven :
    qInt = (X - 5) * (X - 6) * (X ^ 3 + 6 * X ^ 2 + 4 * X + 1)
             + 7 * (6 * X ^ 3 - 21 * X ^ 2 - 12 * X - 5) := by
  simp only [qInt]; ring

/-- **Mod-7 factorization of `q`.** Reducing `q` modulo `7` splits it as a product of two
distinct linear factors and the cubic `cubic7`:
`q ≡ (X − 5)(X − 6)(X³ + 6X² + 4X + 1) (mod 7)`. -/
theorem qInt_map_zmod7 :
    qInt.map (Int.castRingHom (ZMod 7)) = (X - 5) * (X - 6) * cubic7 := by
  -- In `(ZMod 7)[X]` the numeral `7` is `0` (characteristic 7), so the `7 · R` term dies.
  have h70 : (7 : (ZMod 7)[X]) = 0 := by
    have h := CharP.cast_eq_zero (ZMod 7)[X] 7
    rwa [Nat.cast_ofNat] at h
  rw [qInt_eq_factor_add_seven, Polynomial.map_add]
  simp only [cubic7, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one,
    h70, zero_mul, add_zero]

/-- `cubic7` has degree `3`. -/
theorem cubic7_natDegree : cubic7.natDegree = 3 := by
  unfold cubic7; compute_degree!

/-- `cubic7` has no root in `𝔽₇`: `x³ + 6x² + 4x + 1 ≠ 0` for every `x ∈ ZMod 7`
(checked exhaustively over the `7` residues). -/
theorem cubic7_no_root : ∀ x : ZMod 7, cubic7.eval x ≠ 0 := by
  intro x
  simp only [cubic7, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]
  revert x; decide

/-- **The cubic factor is irreducible over `𝔽₇`.** A degree-`3` polynomial over a field is
irreducible iff it has no root; `cubic7` has none. Together with `qInt_map_zmod7` this is
Dedekind's cycle-type-`(1, 1, 3)` datum for `q` at the prime `7`. -/
theorem cubic7_irreducible : Irreducible cubic7 :=
  irreducible_of_degree_le_three_of_not_isRoot
    (by rw [Finset.mem_Icc, cubic7_natDegree]; exact ⟨by norm_num, le_refl 3⟩)
    (fun x => cubic7_no_root x)

-- Axiom audit: only the three standard foundational axioms; no `sorryAx`, no
-- `Lean.ofReduceBool` (`decide` is kernel-checked, not `native_decide`).
#print axioms qInt_map_zmod7
#print axioms cubic7_irreducible

end InverseGaloisA5DedekindMod7
