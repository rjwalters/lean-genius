/-
  The Frobenius automorphism generates the Galois group of a finite field.

  Parent (`frobenius-endomorphism-oq-01`) packaged the absolute Frobenius
  `x ↦ x ^ p` as a ring homomorphism in prime characteristic, together with the
  fixed-point characterisations: it is the identity on the prime field `𝔽_p`
  (Fermat) and `x ^ q = x` on a finite field of order `q`.  Its first listed open
  question asks to exhibit the Frobenius as a GENERATOR of the cyclic Galois
  group `Gal(𝔽_{pⁿ} / 𝔽_p)` and to prove that its order is EXACTLY `n`.

  This file answers that question for the canonical model `GaloisField p n = 𝔽_{pⁿ}`.
  Working over the prime field `K = ZMod p` (so `q = |K| = p`), the Frobenius

      frob : 𝔽_{pⁿ} ≃ₐ[𝔽_p] 𝔽_{pⁿ},   x ↦ x ^ p

  is a field automorphism fixing `𝔽_p`.  We prove:

    * `frob_apply`         : `frob x = x ^ p` (the absolute Frobenius);
    * `frob_pow_apply`     : `(frobᵏ) x = x ^ (pᵏ)` (the iterated Frobenius);
    * `orderOf_frob`       : `orderOf frob = n` (order EXACTLY the degree);
    * `frob_pow_card`      : `frobⁿ = 1`;
    * `frob_pow_ne_one`    : `frobᵏ ≠ 1` for `0 < k < n` (sharpness of the order);
    * `frob_generates`     : every `σ ∈ Gal` is a power of `frob`;
    * `zpowers_frob_eq_top`: `⟨frob⟩ = Gal` (the Frobenius GENERATES);
    * `card_aut`           : `|Gal(𝔽_{pⁿ}/𝔽_p)| = n`;
    * `galois_group_cyclic`: the Galois group is cyclic.

  The heavy machinery (`frobeniusAlgEquivOfAlgebraic`, its order equals the
  finite-field degree, and the cyclicity of the absolute Galois group of a finite
  field) lives in Mathlib's `FieldTheory/Finite/Basic`.  The contribution here is
  the explicit SPECIALISATION to `GaloisField p n / ZMod p`, where the degree is
  literally `n`: this turns "order = finrank" into "order = exactly `n`", pins down
  `frob` as the named generator `x ↦ x ^ p`, and records the iterated-Frobenius
  formula `frobᵏ = (x ↦ x ^ pᵏ)` connecting to the parent's finite-field iterates.
  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

namespace FrobeniusEndomorphismOQ01OQ01

open FiniteField

variable (p : ℕ) [Fact p.Prime] (n : ℕ) [NeZero n]

/-- The **Frobenius automorphism** `x ↦ x ^ p` of the finite field `𝔽_{pⁿ}`,
viewed as an element of the Galois group `Gal(𝔽_{pⁿ} / 𝔽_p)`.  It fixes the prime
field `𝔽_p = ZMod p` pointwise (Fermat) and is the canonical generator. -/
noncomputable def frob : GaloisField p n ≃ₐ[ZMod p] GaloisField p n :=
  frobeniusAlgEquivOfAlgebraic (ZMod p) (GaloisField p n)

omit [NeZero n] in
/-- The Frobenius acts as the absolute `p`-power map: `frob x = x ^ p`. -/
theorem frob_apply (x : GaloisField p n) : frob p n x = x ^ p := by
  rw [show frob p n x = x ^ Fintype.card (ZMod p) from
        congrFun (coe_frobeniusAlgEquivOfAlgebraic (ZMod p) (GaloisField p n)) x,
      ZMod.card]

omit [NeZero n] in
/-- The `k`-th power of the Frobenius is the iterated Frobenius `x ↦ x ^ (pᵏ)`. -/
theorem frob_pow_apply (k : ℕ) (x : GaloisField p n) :
    (frob p n ^ k) x = x ^ p ^ k := by
  rw [show (frob p n ^ k) x = (⇑(frob p n))^[k] x from
        congrFun (AlgEquiv.coe_pow (frob p n) k) x,
      show (⇑(frob p n))^[k] x = x ^ Fintype.card (ZMod p) ^ k from
        congrFun (coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod p) (GaloisField p n) k) x,
      ZMod.card]

/-- **Order exactly `n`.** The Frobenius automorphism of `𝔽_{pⁿ}` has order
exactly `n` — the degree `[𝔽_{pⁿ} : 𝔽_p]`. -/
theorem orderOf_frob : orderOf (frob p n) = n := by
  rw [show frob p n = frobeniusAlgEquivOfAlgebraic (ZMod p) (GaloisField p n) from rfl,
      orderOf_frobeniusAlgEquivOfAlgebraic, GaloisField.finrank p (NeZero.ne n)]

/-- `frobⁿ = 1`: the `n`-fold Frobenius is the identity (every `x ∈ 𝔽_{pⁿ}`
satisfies `x ^ (pⁿ) = x`). -/
theorem frob_pow_card : frob p n ^ n = 1 := by
  have h := pow_orderOf_eq_one (frob p n)
  rwa [orderOf_frob p n] at h

/-- **Sharpness of the order.** No smaller positive power of the Frobenius is the
identity: `frobᵏ ≠ 1` whenever `0 < k < n`. -/
theorem frob_pow_ne_one {k : ℕ} (hk : 0 < k) (hkn : k < n) : frob p n ^ k ≠ 1 := by
  intro h
  have hdvd : orderOf (frob p n) ∣ k := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_frob p n] at hdvd
  exact absurd (Nat.le_of_dvd hk hdvd) (not_le.mpr hkn)

omit [NeZero n] in
/-- **The Frobenius generates.** Every automorphism `σ ∈ Gal(𝔽_{pⁿ} / 𝔽_p)` is a
nonnegative power of the Frobenius. -/
theorem frob_generates (σ : GaloisField p n ≃ₐ[ZMod p] GaloisField p n) :
    ∃ k : ℕ, frob p n ^ k = σ := by
  obtain ⟨m, hm⟩ :=
    (bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) (GaloisField p n)).2 σ
  exact ⟨m.1, hm⟩

omit [NeZero n] in
/-- **The Frobenius is a generator of the Galois group**: the cyclic subgroup it
generates is the whole group, `⟨frob⟩ = Gal(𝔽_{pⁿ} / 𝔽_p)`. -/
theorem zpowers_frob_eq_top : Subgroup.zpowers (frob p n) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  obtain ⟨k, hk⟩ := frob_generates p n σ
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩

/-- The Galois group `Gal(𝔽_{pⁿ} / 𝔽_p)` has order exactly `n`. -/
theorem card_aut :
    Nat.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) = n := by
  rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank p (NeZero.ne n)]

omit [NeZero n] in
/-- The Galois group of a finite field over its prime field is cyclic — generated
by the Frobenius (`zpowers_frob_eq_top`). -/
theorem galois_group_cyclic :
    IsCyclic (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) :=
  inferInstance

omit [NeZero n] in
/-- A fixed point of the Frobenius is exactly a Fermat fixed point `x ^ p = x`;
these are the elements of the prime field `𝔽_p`. -/
theorem frob_fixed_iff (x : GaloisField p n) : frob p n x = x ↔ x ^ p = x := by
  rw [frob_apply]

/-- Concrete instance `𝔽_{2³}`: the Frobenius `x ↦ x²` has order exactly `3`. -/
theorem orderOf_frob_two_three : orderOf (frob 2 3) = 3 := orderOf_frob 2 3

end FrobeniusEndomorphismOQ01OQ01
