import Mathlib
import Proofs.InverseGaloisOQ06OQ01

/-
# The mod-7 Irreducible Factorization of `q` (OQ-06 → OQ-02)

This file completes the *algebraic* half of the mod-7 Dedekind route toward the
last remaining axiom in `InverseGaloisA5.lean`:

  `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`

where `q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5`.

## What Dedekind's theorem needs as input

Dedekind's theorem says: if a prime `p` does **not** divide the discriminant of
`q` (equivalently `q mod p` is *squarefree*), and `q mod p` factors into
irreducibles of degrees `d₁, …, dₖ`, then `Gal(q)` — viewed as a subgroup of the
symmetric group on the roots — contains a permutation of cycle type
`(d₁, …, dₖ)`.

The sibling file `InverseGaloisOQ06OQ01.lean` established the *factorization
shape* mod 7:

  `q ≡ (X - 5)(X - 6) · (X³ + 6X² + 4X + 1)   (mod 7)`

and that the cubic factor `cubicMod7` has **no roots** in `𝔽₇`.

This file upgrades that to the full **irreducible-factorization** statement that
Dedekind consumes:

1. `cubicMod7_irreducible`      : the cubic factor is **irreducible** over `𝔽₇`
                                  (degree 3 + no roots ⟹ irreducible).
2. `linFactor5_irreducible`,
   `linFactor6_irreducible`     : the two monic linear factors are irreducible.
3. pairwise **non-association**  : the three factors are distinct primes,
   so the factorization type is genuinely `(1, 1, 3)`.
4. `q_mod7_squarefree`          : the product is squarefree (`p = 7`
   **unramified**), discharging Dedekind's hypothesis on the discriminant.
5. `q_mod7_factor_type`         : the packaged "(1,1,3) into distinct
   irreducibles" statement — exactly the Dedekind input.

## Honest scope

This file does **NOT** eliminate `three_dvd_gal_card`. The remaining gap is
Dedekind's theorem itself (factorization type ⟹ Frobenius cycle type ⟹
`3 ∣ |Gal|`), which is absent from Mathlib 4.26 and is the subject of the
sibling Frobenius track (`inverse-galois-a5-oq-01`). What we add here is the
verified, 0-axiom *algebraic input* to that theorem: the factorization is into
distinct irreducibles of degrees `(1,1,3)`, and 7 is unramified.

## Key Mathlib API

- `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`
    (hdeg : p.natDegree ∈ Finset.Icc 1 3) (hnot : ∀ x, ¬ IsRoot p x) : Irreducible p
- `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` : `IsUnit (a-b) → IsCoprime (X-C a) (X-C b)`
- `Irreducible.isRelPrime_iff_not_dvd`, `Polynomial.dvd_iff_isRoot`
- `squarefree_mul_iff` : `Squarefree (x*y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y`
- `Polynomial.eq_of_monic_of_associated`, `Polynomial.natDegree_le_of_dvd`
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Classical

namespace InverseGaloisOQ06OQ02

open InverseGaloisOQ06OQ01 Polynomial

/-- `7` is prime, so `ZMod 7` is a field (and `(ZMod 7)[X]` a Euclidean domain).
This instance powers the field/domain typeclass resolution used throughout. -/
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- ============================================================================
-- § 1. The three factors and their degrees
-- ============================================================================

/-- The first linear factor `X - 5` over `𝔽₇`. -/
noncomputable def linFactor5 : (ZMod 7)[X] := X - C 5

/-- The second linear factor `X - 6` over `𝔽₇`. -/
noncomputable def linFactor6 : (ZMod 7)[X] := X - C 6

theorem cubicMod7_natDegree : cubicMod7.natDegree = 3 := by
  unfold cubicMod7; compute_degree!

theorem linFactor5_natDegree : linFactor5.natDegree = 1 := by
  unfold linFactor5; compute_degree!

theorem linFactor6_natDegree : linFactor6.natDegree = 1 := by
  unfold linFactor6; compute_degree!

theorem linFactor5_ne_zero : linFactor5 ≠ 0 := (monic_X_sub_C 5).ne_zero
theorem linFactor6_ne_zero : linFactor6 ≠ 0 := (monic_X_sub_C 6).ne_zero

theorem cubicMod7_ne_zero : cubicMod7 ≠ 0 := by
  intro h0
  have hd := cubicMod7_natDegree
  rw [h0, natDegree_zero] at hd
  exact absurd hd (by decide)

-- ============================================================================
-- § 2. Irreducibility
-- ============================================================================

/-- **The cubic factor is irreducible over `𝔽₇`.**
A degree-3 polynomial over a field with no root is irreducible; the no-root fact
is `InverseGaloisOQ06OQ01.cubicMod7_no_roots`. -/
theorem cubicMod7_irreducible : Irreducible cubicMod7 := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubicMod7_natDegree]; decide
  · intro x; exact cubicMod7_no_roots x

theorem linFactor5_irreducible : Irreducible linFactor5 := irreducible_X_sub_C 5
theorem linFactor6_irreducible : Irreducible linFactor6 := irreducible_X_sub_C 6

-- ============================================================================
-- § 3. The three factors are pairwise non-associated (distinct primes)
-- ============================================================================

/-- The two linear factors are not associated: associated monic linears are
equal, forcing `5 = 6` in `𝔽₇`, which is false. -/
theorem linFactors_not_associated : ¬ Associated linFactor5 linFactor6 := by
  intro h
  have heq : linFactor5 = linFactor6 :=
    eq_of_monic_of_associated (monic_X_sub_C 5) (monic_X_sub_C 6) h
  have h0 := congrArg (eval (0 : ZMod 7)) heq
  simp only [linFactor5, linFactor6, eval_sub, eval_X, eval_C] at h0
  revert h0; decide

/-- A degree-1 factor cannot be associated to the degree-3 cubic. -/
theorem linFactor5_not_associated_cubic : ¬ Associated linFactor5 cubicMod7 := by
  intro h
  have h1 := natDegree_le_of_dvd h.dvd cubicMod7_ne_zero
  have h2 := natDegree_le_of_dvd h.symm.dvd linFactor5_ne_zero
  rw [linFactor5_natDegree, cubicMod7_natDegree] at h1 h2
  omega

/-- A degree-1 factor cannot be associated to the degree-3 cubic. -/
theorem linFactor6_not_associated_cubic : ¬ Associated linFactor6 cubicMod7 := by
  intro h
  have h1 := natDegree_le_of_dvd h.dvd cubicMod7_ne_zero
  have h2 := natDegree_le_of_dvd h.symm.dvd linFactor6_ne_zero
  rw [linFactor6_natDegree, cubicMod7_natDegree] at h1 h2
  omega

-- ============================================================================
-- § 4. Pairwise coprimality and squarefreeness (7 is unramified)
-- ============================================================================

/-- `X - 5` and `X - 6` are coprime: their difference `5 - 6 = -1` is a unit. -/
theorem linFactors_isCoprime : IsCoprime linFactor5 linFactor6 := by
  show IsCoprime (X - C (5 : ZMod 7)) (X - C 6)
  exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (by decide))

/-- `X - 5` is coprime to the cubic: `5` is not a root of the cubic. -/
theorem linFactor5_cubic_isCoprime : IsCoprime linFactor5 cubicMod7 := by
  have h : IsRelPrime linFactor5 cubicMod7 := by
    show IsRelPrime (X - C (5 : ZMod 7)) cubicMod7
    rw [(irreducible_X_sub_C (5 : ZMod 7)).isRelPrime_iff_not_dvd, dvd_iff_isRoot]
    exact cubicMod7_no_roots 5
  exact h.isCoprime

/-- `X - 6` is coprime to the cubic: `6` is not a root of the cubic. -/
theorem linFactor6_cubic_isCoprime : IsCoprime linFactor6 cubicMod7 := by
  have h : IsRelPrime linFactor6 cubicMod7 := by
    show IsRelPrime (X - C (6 : ZMod 7)) cubicMod7
    rw [(irreducible_X_sub_C (6 : ZMod 7)).isRelPrime_iff_not_dvd, dvd_iff_isRoot]
    exact cubicMod7_no_roots 6
  exact h.isCoprime

/-- **`q mod 7` is squarefree** — equivalently, 7 does not divide the
discriminant of `q`, so 7 is unramified. This discharges the hypothesis of
Dedekind's theorem. Built from the explicit factorization `(X-5)(X-6)·cubic`
into pairwise-coprime irreducibles. -/
theorem q_mod7_squarefree :
    Squarefree (linFactor5 * linFactor6 * cubicMod7) := by
  rw [squarefree_mul_iff]
  refine ⟨?_, ?_, cubicMod7_irreducible.squarefree⟩
  · exact (linFactor5_cubic_isCoprime.mul_left linFactor6_cubic_isCoprime).isRelPrime
  · rw [squarefree_mul_iff]
    exact ⟨linFactors_isCoprime.isRelPrime, linFactor5_irreducible.squarefree,
           linFactor6_irreducible.squarefree⟩

-- ============================================================================
-- § 5. Packaged Dedekind input
-- ============================================================================

/-- **`q ≡ (X-5)(X-6)·cubicMod7  (mod 7)`**, restated with the named factors
`linFactor5`, `linFactor6`. This is `InverseGaloisOQ06OQ01.q_ℤ_mod7_factorization`
re-expressed through the local factor definitions, so the packaged
`q_mod7_factor_type` below can carry the identity tying the three irreducibles
to `q` itself — exactly as the sibling `p = 11` packaging does
(`InverseGaloisOQ06OQ02P11.q_ℤ_mod11_factorization`). -/
theorem q_mod7_factorization :
    q_ℤ.map (Int.castRingHom (ZMod 7)) = linFactor5 * linFactor6 * cubicMod7 := by
  show q_ℤ.map (Int.castRingHom (ZMod 7)) = (X - C 5) * (X - C 6) * cubicMod7
  exact q_ℤ_mod7_factorization

/-- **The mod-7 factor type of `q` is `(1, 1, 3)` into distinct irreducibles.**

This bundles everything Dedekind's theorem consumes at `p = 7`:
* three irreducible factors,
* of degrees `1, 1, 3`,
* pairwise non-associated (distinct primes),
* with squarefree product (`p = 7` unramified),
* whose product is genuinely `q mod 7` (`q_mod7_factorization`).

Combined with Dedekind's theorem (still a Mathlib gap; sibling track), this
forces `Gal(q)` to contain a 3-cycle, hence `3 ∣ |Gal(q)|`. -/
theorem q_mod7_factor_type :
    Irreducible linFactor5 ∧ Irreducible linFactor6 ∧ Irreducible cubicMod7 ∧
    linFactor5.natDegree = 1 ∧ linFactor6.natDegree = 1 ∧ cubicMod7.natDegree = 3 ∧
    (¬ Associated linFactor5 linFactor6) ∧
    (¬ Associated linFactor5 cubicMod7) ∧
    (¬ Associated linFactor6 cubicMod7) ∧
    Squarefree (linFactor5 * linFactor6 * cubicMod7) ∧
    q_ℤ.map (Int.castRingHom (ZMod 7)) = linFactor5 * linFactor6 * cubicMod7 :=
  ⟨linFactor5_irreducible, linFactor6_irreducible, cubicMod7_irreducible,
   linFactor5_natDegree, linFactor6_natDegree, cubicMod7_natDegree,
   linFactors_not_associated, linFactor5_not_associated_cubic,
   linFactor6_not_associated_cubic, q_mod7_squarefree, q_mod7_factorization⟩

end InverseGaloisOQ06OQ02
