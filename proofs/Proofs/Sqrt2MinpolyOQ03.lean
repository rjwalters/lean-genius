import Mathlib
import Proofs.Sqrt2Minpoly

/-!
# Class Number 1 for Q(√2) via Minkowski's Bound (S3 ACT SCAFFOLD)

## Problem

Prove `NumberField.classNumber Q_sqrt2 = 1` where `Q_sqrt2 := AdjoinRoot (X^2 - C 2 : ℚ[X])`.

## Strategy (per S2 PREP-1..9 audit chain)

1. Construct `Q_sqrt2` via `AdjoinRoot`; obtain `Field` / `Algebra ℚ` / `NumberField` instances.
2. Compute `NumberField.discr Q_sqrt2 = 8` (S3 sub-target — PREP-3/4/5/6).
3. Compute `NumberField.minkowskiBound Q_sqrt2 < 2` (S3 sub-target).
4. Apply Minkowski's existence-of-small-norm-element lemma.
5. Conclude every ideal class contains a unit ideal; hence `h_K = 1`.

## This SCAFFOLD scope (S3 ACT)

Set up the type, irreducibility `Fact`, and the canonical instance stack, then
state the main theorem `Q_sqrt2_classNumber_eq_one` with a strategic sorry.
The 4-step discriminant/Minkowski chain (PREP-3..8's 128-LOC sketch) is the
S4+ deliverable.

## Status

Strategic sorries: 1 — narrowed to the single input `Q_sqrt2_discr_eq_eight`
(`discr Q(√2) = 8`); the capstone `classNumber = 1` is otherwise FULLY
proved via `Q_sqrt2_classNumber_eq_one_of_discr` (S9, Mathlib v4.31's
`isPrincipalIdealRing_of_abs_discr_lt`).
Axioms: 0.
Build-verified sub-targets: `X_sq_sub_two_ne_zero`, `Q_sqrt2_finrank = 2`,
`Q_sqrt2_nrComplexPlaces = 0` (via the totally-real instance),
`Q_sqrt2_classNumber_eq_one_of_discr` (conditional capstone).
-/

namespace Sqrt2MinpolyOQ03

open Polynomial

/-- The defining polynomial X² − 2 over ℚ; irreducibility imported from parent. -/
noncomputable abbrev X_sq_sub_two : ℚ[X] := X ^ 2 - C 2

/-- Q(√2) constructed as the quotient ℚ[X]/(X² − 2). -/
noncomputable abbrev Q_sqrt2 : Type := AdjoinRoot X_sq_sub_two

/-- The `Fact` instance unlocking `AdjoinRoot.field` for `Q_sqrt2`. -/
instance : Fact (Irreducible X_sq_sub_two) := ⟨Sqrt2Minpoly.irred_X_sq_sub_two⟩

/-- `Q_sqrt2` is a `NumberField`: finite-dimensional over ℚ via the power basis
of the monic irreducible defining polynomial. -/
instance : NumberField Q_sqrt2 where
  to_charZero := inferInstance
  to_finiteDimensional :=
    (PowerBasis.finite (AdjoinRoot.powerBasis
      (f := X_sq_sub_two)
      (by
        -- X² − 2 ≠ 0 (degree 2 ≠ 0)
        intro h
        have : (X_sq_sub_two : ℚ[X]).natDegree = 0 := by
          rw [h]; simp
        have hdeg : (X_sq_sub_two : ℚ[X]).natDegree = 2 := by
          simp [X_sq_sub_two]
        omega)))

/-- `X² − 2 ≠ 0` (it has degree 2). Factored helper, build-verified. -/
theorem X_sq_sub_two_ne_zero : X_sq_sub_two ≠ 0 := by
  intro h
  have hdeg : (X_sq_sub_two : ℚ[X]).natDegree = 2 := by simp [X_sq_sub_two]
  rw [h] at hdeg
  simp at hdeg

/-- **Sub-target (build-verified):** `[Q(√2) : ℚ] = 2`.

This is the field degree `n = finrank ℚ K` appearing in the Minkowski bound
`M K = (4/π)^(nrComplexPlaces K) · (n! / nⁿ · √|discr K|)`. For Q(√2), `n = 2`,
`nrComplexPlaces = 0` (totally real), and `discr = 8`, giving `M K = √2 < 2`.
The degree is computed here from the power basis of the degree-2 defining
polynomial via `AdjoinRoot.powerBasis_dim` + `PowerBasis.finrank`. -/
theorem Q_sqrt2_finrank : Module.finrank ℚ Q_sqrt2 = 2 := by
  rw [(AdjoinRoot.powerBasis X_sq_sub_two_ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  simp [X_sq_sub_two]

/-- **The square of any complex-embedding image of `root` is 2**: the
generator of `Q_sqrt2` satisfies `root² = 2`, and ring homomorphisms
preserve that relation. -/
theorem embedding_root_sq (φ : Q_sqrt2 →+* ℂ) :
    φ (AdjoinRoot.root X_sq_sub_two) ^ 2 = 2 := by
  have hroot : (AdjoinRoot.root X_sq_sub_two) ^ 2 = (2 : Q_sqrt2) := by
    have h0 := AdjoinRoot.eval₂_root X_sq_sub_two
    simp only [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at h0
    rw [h0]
    exact map_ofNat (AdjoinRoot.of X_sq_sub_two) 2
  rw [← map_pow, hroot]
  exact map_ofNat φ 2

/-- **A complex number with square 2 is real** (fixed by conjugation):
`re·im = 0` from the imaginary part of `z² = 2`, and `re = 0` is impossible
since it would force `−im² = 2`. -/
theorem conj_eq_self_of_sq_eq_two {z : ℂ} (hz : z ^ 2 = 2) :
    (starRingEnd ℂ) z = z := by
  rw [Complex.conj_eq_iff_im]
  have h1 : (z ^ 2).im = 0 := by rw [hz]; simp
  have h2 : (z ^ 2).re = 2 := by rw [hz]; simp
  rw [pow_two, Complex.mul_im] at h1
  rw [pow_two, Complex.mul_re] at h2
  have hri : z.re * z.im = 0 := by linarith
  rcases mul_eq_zero.mp hri with h | h
  · exfalso
    rw [h] at h2
    nlinarith [sq_nonneg z.im]
  · exact h

/-- **Every complex embedding of Q(√2) is real**: it sends the generator
`root` to a solution of `z² = 2` (hence a real number, `±√2`), so the
embedding agrees with its conjugate on the generator and therefore
everywhere (`AdjoinRoot.algHom_ext` over ℚ). -/
theorem complexEmbedding_isReal (φ : Q_sqrt2 →+* ℂ) :
    NumberField.ComplexEmbedding.IsReal φ := by
  rw [NumberField.ComplexEmbedding.isReal_iff]
  -- both sides agree after precomposition with the surjection ℚ[X] → Q_sqrt2
  have hcomp : (NumberField.ComplexEmbedding.conjugate φ).comp
      (AdjoinRoot.mk X_sq_sub_two) = φ.comp (AdjoinRoot.mk X_sq_sub_two) := by
    apply Polynomial.ringHom_ext
    · -- rational constants: any two ring homs ℚ →+* ℂ coincide
      intro a
      exact RingHom.congr_fun (Subsingleton.elim
        (((NumberField.ComplexEmbedding.conjugate φ).comp
          (AdjoinRoot.mk X_sq_sub_two)).comp Polynomial.C)
        ((φ.comp (AdjoinRoot.mk X_sq_sub_two)).comp Polynomial.C)) a
    · -- the generator: φ root is real, hence conjugation-fixed
      simp only [RingHom.comp_apply, AdjoinRoot.mk_X,
        NumberField.ComplexEmbedding.conjugate_coe_eq]
      exact conj_eq_self_of_sq_eq_two (embedding_root_sq φ)
  refine RingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  exact RingHom.congr_fun hcomp p

/-- **Q(√2) is totally real** (every infinite place is real). -/
instance : NumberField.IsTotallyReal Q_sqrt2 where
  isReal _ := NumberField.InfinitePlace.isReal_iff.mpr
    (complexEmbedding_isReal _)

/-- **Sub-target (build-verified): Q(√2) has no complex places.**
This is the `nrComplexPlaces K = 0` input to the Minkowski-bound
arithmetic in the capstone reduction below. -/
theorem Q_sqrt2_nrComplexPlaces :
    NumberField.InfinitePlace.nrComplexPlaces Q_sqrt2 = 0 :=
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero Q_sqrt2

/-- **Conditional capstone (fully proved):** `classNumber Q(√2) = 1`
GIVEN the discriminant computation `discr Q_sqrt2 = 8`.

Route (Mathlib v4.31 pin — `isPrincipalIdealRing_of_abs_discr_lt` EXISTS
at this pin, unlike the v4.26 pin of the S8 record):

1. `classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)`.
2. `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`: it suffices that
   `|discr K| < (2 · (π/4)^r₂ · (nⁿ/n!))²`.
3. With `discr = 8`, `r₂ = nrComplexPlaces = 0` (`Q_sqrt2_nrComplexPlaces`),
   `n = finrank = 2` (`Q_sqrt2_finrank`): the bound is
   `(2 · 1 · (4/2))² = 16` and `|8| = 8 < 16`. `norm_num` closes it.

This discharges the former sub-targets (2)–(4) of the S8 plan; the ONLY
remaining input is sub-target (1), `discr Q_sqrt2 = 8`, isolated as
`Q_sqrt2_discr_eq_eight` below. -/
theorem Q_sqrt2_classNumber_eq_one_of_discr
    (hd : NumberField.discr Q_sqrt2 = 8) :
    NumberField.classNumber Q_sqrt2 = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hd, Q_sqrt2_nrComplexPlaces, Q_sqrt2_finrank]
  norm_num [Nat.factorial]

/-! ## S10 bricks — toward `discr Q(√2) = 8` (integral-basis route)

The discriminant computation needs `𝓞 Q_sqrt2 = ℤ[root]`. This section
lands the critical-path bricks build-verified:

1. `root_sq` / `root_isIntegral` — the generator satisfies `root² = 2`
   and is an algebraic integer (easy inclusion `ℤ[root] ⊆ 𝓞`).
2. `rat_int_of_sq_int` — a rational whose square is an integer is an
   integer (monic-quadratic integrality over the integrally closed ℤ).
3. `int_pair_of_double_and_norm` — the arithmetic crux of the hard
   inclusion `𝓞 ⊆ ℤ[root]`: if `2a ∈ ℤ` (the trace of `a + b·root`)
   and `a² − 2b² ∈ ℤ` (its norm), then `a, b ∈ ℤ`. Chain:
   `(4b)² = 2(u² − 4N) ∈ ℤ` → `4b ∈ ℤ` → even (its square is even) →
   `2b ∈ ℤ` → the mod-4 obstruction `u² = 2v²` in `ZMod 4` has no
   solution with `v` odd (`x² ∈ {0, 1} ≠ 2`) → `b ∈ ℤ` →
   `a² = N + 2b² ∈ ℤ` → `a ∈ ℤ`.

S11 consumes these with the trace/norm formulas
`trace (a + b·root) = 2a`, `norm (a + b·root) = a² − 2b²` (power-basis
computation) to conclude `𝓞 = ℤ[root]`, build the `Basis (Fin 2) ℤ`,
and finish via `NumberField.discr_eq_discr` + the trace-form
determinant `[[2, 0], [0, 4]]`. -/

/-- The generator of `Q_sqrt2` squares to 2 (internal form of
`embedding_root_sq`, without an embedding). -/
theorem root_sq : (AdjoinRoot.root X_sq_sub_two) ^ 2 = 2 := by
  have h0 := AdjoinRoot.eval₂_root X_sq_sub_two
  simp only [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at h0
  rw [h0]
  exact map_ofNat (AdjoinRoot.of X_sq_sub_two) 2

/-- `root` is an algebraic integer: it is a root of the monic `X² − 2`
over ℤ. This is the easy inclusion `ℤ[root] ⊆ 𝓞 Q_sqrt2`. -/
theorem root_isIntegral : IsIntegral ℤ (AdjoinRoot.root X_sq_sub_two) := by
  refine ⟨X ^ 2 - C 2, Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, root_sq, sub_eq_zero]
  simp

/-- A rational whose square is an integer is an integer: it is a root of
the monic `X² − c` over the integrally closed ℤ. -/
theorem rat_int_of_sq_int (q : ℚ) (c : ℤ) (h : q ^ 2 = (c : ℚ)) :
    ∃ m : ℤ, (m : ℚ) = q := by
  have hint : IsIntegral ℤ q := by
    refine ⟨X ^ 2 - C c, Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, h, sub_eq_zero]
    simp
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

/-- **Arithmetic crux of `𝓞 ⊆ ℤ[√2]`** — the classical "half-integer"
exclusion. If `2a` and `a² − 2b²` are integers (the trace and norm of
`a + b√2`), then `a` and `b` are integers.

The mod-4 obstruction is run in `ZMod 4`: with `v = 2b` odd, the
integer identity `4N = u² − 2v²` reduces to `u² = 2·1 = 2` in `ZMod 4`,
but squares in `ZMod 4` are `{0, 1}` (`decide`). -/
theorem int_pair_of_double_and_norm (a b : ℚ) (u N : ℤ)
    (hu : (u : ℚ) = 2 * a) (hN : (N : ℚ) = a ^ 2 - 2 * b ^ 2) :
    (∃ a0 : ℤ, (a0 : ℚ) = a) ∧ (∃ b0 : ℤ, (b0 : ℚ) = b) := by
  -- Step 1: 4b is an integer, since (4b)² = 2(u² − 4N) ∈ ℤ.
  have hkey : (4 * b) ^ 2 = ((2 * (u ^ 2 - 4 * N) : ℤ) : ℚ) := by
    push_cast
    linear_combination (-2 * ((u : ℚ) + 2 * a)) * hu + 8 * hN
  obtain ⟨w, hw⟩ := rat_int_of_sq_int (4 * b) _ hkey
  have hw2 : w ^ 2 = 2 * (u ^ 2 - 4 * N) := by
    have h' := hkey
    rw [← hw] at h'
    exact_mod_cast h'
  -- Step 2: w = 4b is even (its square is), so 2b is an integer v.
  have hweven : Even w := by
    have h2 : Even (w ^ 2) := ⟨u ^ 2 - 4 * N, by linarith⟩
    exact (Int.even_pow.mp h2).1
  obtain ⟨v, hv⟩ := hweven
  have hv2b : (v : ℚ) = 2 * b := by
    have hcast : ((w : ℤ) : ℚ) = (v : ℚ) + (v : ℚ) := by
      rw [hv]; push_cast; ring
    rw [hw] at hcast
    linarith
  -- Step 3: the integer identity 4N = u² − 2v².
  have h4N : 4 * N = u ^ 2 - 2 * v ^ 2 := by
    have h' : ((4 * N : ℤ) : ℚ) = ((u ^ 2 - 2 * v ^ 2 : ℤ) : ℚ) := by
      push_cast
      linear_combination 4 * hN - ((u : ℚ) + 2 * a) * hu +
        2 * ((v : ℚ) + 2 * b) * hv2b
    exact_mod_cast h'
  -- Step 4: v is even — mod-4 obstruction in ZMod 4.
  have hveven : Even v := by
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    obtain ⟨j, hj⟩ := hodd
    have h40 : (4 : ZMod 4) = 0 := by decide
    have hv4 : ((v : ℤ) : ZMod 4) ^ 2 = 1 := by
      have hvc : ((v : ℤ) : ZMod 4) = 2 * ((j : ℤ) : ZMod 4) + 1 := by
        have := congrArg (fun t : ℤ => (t : ZMod 4)) hj
        push_cast at this
        exact this
      rw [hvc]
      linear_combination (((j : ℤ) : ZMod 4) ^ 2 + ((j : ℤ) : ZMod 4)) * h40
    have hu4 : ((u : ℤ) : ZMod 4) ^ 2 = 2 := by
      have hc := congrArg (fun t : ℤ => (t : ZMod 4)) h4N
      push_cast at hc
      rw [hv4] at hc
      linear_combination -hc + ((N : ℤ) : ZMod 4) * h40
    have hno : ∀ x : ZMod 4, x ^ 2 ≠ 2 := by decide
    exact hno _ hu4
  -- Step 5: b = v/2 ∈ ℤ, then a² = N + 2b² ∈ ℤ forces a ∈ ℤ.
  obtain ⟨b0, hb0⟩ := hveven
  have hb0Q : (b0 : ℚ) = b := by
    have hcast : ((v : ℤ) : ℚ) = (b0 : ℚ) + (b0 : ℚ) := by
      rw [hb0]; push_cast; ring
    rw [hv2b] at hcast
    linarith
  have hkey2 : a ^ 2 = ((N + 2 * b0 ^ 2 : ℤ) : ℚ) := by
    push_cast
    linear_combination -hN - 2 * ((b0 : ℚ) + b) * hb0Q
  obtain ⟨a0, ha0⟩ := rat_int_of_sq_int a _ hkey2
  exact ⟨⟨a0, ha0⟩, ⟨b0, hb0Q⟩⟩

/-- **Remaining sub-target (strategic sorry): `discr Q(√2) = 8`.**

The one open input to the capstone. Route (S10+ deliverable):
prove `𝓞 K = ℤ[√2]` — i.e. `a + b·root` is integral iff `a, b ∈ ℤ`
(elementary trace/norm argument: `2a ∈ ℤ` and `a² − 2b² ∈ ℤ` force
`a, b ∈ ℤ` via a mod-4 case analysis) — then exhibit `{1, root}` as a
`Basis (Fin 2) ℤ (𝓞 K)` and compute
`discr K = Algebra.discr ℤ b = det [[tr 1, tr √2], [tr √2, tr 2]]
= det [[2, 0], [0, 4]] = 8` via `NumberField.discr_eq_discr`.
No Mathlib bearer computes quadratic-field discriminants directly at the
pin (checked: no `Zsqrtd` ↔ `RingOfIntegers` bridge exists). -/
theorem Q_sqrt2_discr_eq_eight : NumberField.discr Q_sqrt2 = 8 := by
  sorry

/-- **Main theorem (capstone):** the class number of Q(√2) is 1 — i.e.
`ℤ[√2]` is a PID. Assembled from the fully-proved conditional reduction
and the (open) discriminant computation. -/
theorem Q_sqrt2_classNumber_eq_one :
    NumberField.classNumber Q_sqrt2 = 1 :=
  Q_sqrt2_classNumber_eq_one_of_discr Q_sqrt2_discr_eq_eight

/-! ## Session 11: the element-level integral basis — `IsIntegral ℤ (a + b·√2) ↔ a, b ∈ ℤ`

This section proves the complete membership characterization of the ring of
integers of `Q(√2)` at the element level: `a + b·root` is an algebraic integer
iff `a, b ∈ ℤ`. The forward direction uses the **minimal-polynomial route**
(instead of the trace/norm formulas originally sketched): for `b ≠ 0` the
element `x = a + b·root` has minimal polynomial `X² − 2aX + (a² − 2b²)` over
ℚ, and integrality forces its coefficients into ℤ
(`minpoly.isIntegrallyClosed_eq_field_fractions'`), which is exactly the
input to the S10 arithmetic crux `int_pair_of_double_and_norm`. This avoids
any `leftMulMatrix` computation. S12 packages this into the ℤ-basis `{1, root}`
of `𝓞` and the discriminant `det [[2,0],[0,4]] = 8`. -/

/-- The element `a + b·√2` of `Q_sqrt2`. -/
noncomputable def elt (a b : ℚ) : Q_sqrt2 :=
  algebraMap ℚ Q_sqrt2 a + algebraMap ℚ Q_sqrt2 b * AdjoinRoot.root X_sq_sub_two

/-- `√2` is irrational: `root` is not in the image of ℚ. (A rational root
would give an integer square root of 2 via `rat_int_of_sq_int`.) -/
theorem root_not_mem_range :
    AdjoinRoot.root X_sq_sub_two ∉ (algebraMap ℚ Q_sqrt2).range := by
  rintro ⟨r, hr⟩
  have h2 : r ^ 2 = 2 := by
    have hsq : algebraMap ℚ Q_sqrt2 (r ^ 2) = algebraMap ℚ Q_sqrt2 2 := by
      rw [map_pow, hr, root_sq, map_ofNat]
    exact_mod_cast (algebraMap ℚ Q_sqrt2).injective hsq
  obtain ⟨m, hm⟩ := rat_int_of_sq_int r 2 (by exact_mod_cast h2)
  have hm2 : m ^ 2 = 2 := by
    have h' : ((m : ℚ)) ^ 2 = 2 := by rw [hm]; exact h2
    exact_mod_cast h'
  have hub : m ≤ 1 := by nlinarith [sq_nonneg (m - 2)]
  have hlb : -1 ≤ m := by nlinarith [sq_nonneg (m + 2)]
  interval_cases m <;> norm_num at hm2

/-- Elements `a + b·root` with `b ≠ 0` are irrational. -/
theorem elt_not_mem_range (a b : ℚ) (hb : b ≠ 0) :
    elt a b ∉ (algebraMap ℚ Q_sqrt2).range := by
  rintro ⟨r, hr⟩
  apply root_not_mem_range
  refine ⟨(r - a) / b, ?_⟩
  have hbne : algebraMap ℚ Q_sqrt2 b ≠ 0 := by
    simpa using (algebraMap ℚ Q_sqrt2).injective.ne hb
  apply mul_left_cancel₀ hbne
  rw [← map_mul, mul_div_cancel₀ _ hb, map_sub, hr]
  simp only [elt]
  ring

/-- `x = a + b·root` is annihilated by the monic quadratic
`X² − 2aX + (a² − 2b²)` (written with `+` and a negated linear coefficient
for direct monicity/coefficient extraction). -/
theorem aeval_elt_quadratic (a b : ℚ) :
    Polynomial.aeval (elt a b)
      (X ^ 2 + (C (-(2 * a)) * X + C (a ^ 2 - 2 * b ^ 2)) : ℚ[X]) = 0 := by
  simp only [elt, map_add, map_mul, map_pow, map_neg, Polynomial.aeval_X,
    Polynomial.aeval_C, map_sub, map_ofNat]
  linear_combination (algebraMap ℚ Q_sqrt2 b) ^ 2 * root_sq

/-- The annihilator is monic (leading term `X²`). -/
theorem quadratic_monic (a b : ℚ) :
    (X ^ 2 + (C (-(2 * a)) * X + C (a ^ 2 - 2 * b ^ 2)) : ℚ[X]).Monic := by
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

/-- **The minimal polynomial of `a + b·root` for `b ≠ 0`** is exactly the
monic quadratic `X² − 2aX + (a² − 2b²)`: the annihilator is divided by the
minimal polynomial, whose degree is ≥ 2 by irrationality
(`minpoly.two_le_natDegree_iff`), so the quotient is the monic constant 1. -/
theorem minpoly_elt (a b : ℚ) (hb : b ≠ 0) :
    minpoly ℚ (elt a b) =
      X ^ 2 + (C (-(2 * a)) * X + C (a ^ 2 - 2 * b ^ 2)) := by
  set q : ℚ[X] := X ^ 2 + (C (-(2 * a)) * X + C (a ^ 2 - 2 * b ^ 2)) with hqdef
  have hq_monic : q.Monic := quadratic_monic a b
  have hq_deg : q.natDegree = 2 := by
    rw [hqdef]
    compute_degree!
  have hx_int : IsIntegral ℚ (elt a b) := IsIntegral.of_finite ℚ _
  have hdvd : minpoly ℚ (elt a b) ∣ q := minpoly.dvd ℚ _ (aeval_elt_quadratic a b)
  have hdeg_le : (minpoly ℚ (elt a b)).natDegree ≤ 2 :=
    hq_deg ▸ Polynomial.natDegree_le_of_dvd hdvd hq_monic.ne_zero
  have hdeg_ge : 2 ≤ (minpoly ℚ (elt a b)).natDegree :=
    (minpoly.two_le_natDegree_iff hx_int).mpr (elt_not_mem_range a b hb)
  obtain ⟨c, hc⟩ := hdvd
  have hmp_monic : (minpoly ℚ (elt a b)).Monic := minpoly.monic hx_int
  have hc_ne : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hq_monic.ne_zero hc
  have hdegs : q.natDegree = (minpoly ℚ (elt a b)).natDegree + c.natDegree := by
    rw [hc, Polynomial.natDegree_mul (minpoly.ne_zero hx_int) hc_ne]
  have hc0 : c.natDegree = 0 := by omega
  have hc_monic : c.Monic := hmp_monic.of_mul_monic_left (hc ▸ hq_monic)
  have hcC : c = C (c.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hc0
  have hlead : c.coeff 0 = 1 := by
    have hl := hc_monic
    rwa [Polynomial.Monic, Polynomial.leadingCoeff, hc0] at hl
  rw [hc, hcC, hlead, Polynomial.C_1, mul_one]

/-- **Forward direction of `𝓞 = ℤ[√2]`**: an integral `a + b·root` has
`a, b ∈ ℤ`. For `b ≠ 0` the minimal polynomial over ℚ descends to ℤ
(`minpoly.isIntegrallyClosed_eq_field_fractions'`), so its coefficients
`−2a` and `a² − 2b²` are integers, and the S10 arithmetic crux applies.
For `b = 0` integrality of the rational `a` gives `a ∈ ℤ` directly. -/
theorem coords_int_of_isIntegral {a b : ℚ} (hint : IsIntegral ℤ (elt a b)) :
    (∃ a0 : ℤ, (a0 : ℚ) = a) ∧ (∃ b0 : ℤ, (b0 : ℚ) = b) := by
  by_cases hb : b = 0
  · subst hb
    have ha : IsIntegral ℤ a := by
      have hxa : elt a 0 = algebraMap ℚ Q_sqrt2 a := by
        simp [elt]
      rw [hxa] at hint
      exact (isIntegral_algebraMap_iff (algebraMap ℚ Q_sqrt2).injective).mp hint
    exact ⟨IsIntegrallyClosed.isIntegral_iff.mp ha, ⟨0, by norm_num⟩⟩
  · have hmap : minpoly ℚ (elt a b) = (minpoly ℤ (elt a b)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    rw [minpoly_elt a b hb] at hmap
    have hcoeff1 : -(2 * a) = ((minpoly ℤ (elt a b)).coeff 1 : ℚ) := by
      have h := congrArg (fun p : ℚ[X] => p.coeff 1) hmap
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_one, Polynomial.coeff_C, Polynomial.coeff_map, eq_intCast,
        mul_one, add_zero, one_ne_zero, ite_false] at h
      simpa using h
    have hcoeff0 : a ^ 2 - 2 * b ^ 2 = ((minpoly ℤ (elt a b)).coeff 0 : ℚ) := by
      have h := congrArg (fun p : ℚ[X] => p.coeff 0) hmap
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_zero, Polynomial.coeff_C, Polynomial.coeff_map, eq_intCast,
        mul_zero, zero_add] at h
      simpa using h
    exact int_pair_of_double_and_norm a b (-(minpoly ℤ (elt a b)).coeff 1)
      ((minpoly ℤ (elt a b)).coeff 0)
      (by rw [Int.cast_neg]; linarith [hcoeff1]) (by linarith [hcoeff0])

/-- **Reverse direction**: integer coordinates give an algebraic integer
(`ℤ[√2] ⊆ 𝓞`). -/
theorem isIntegral_elt_of_coords (m n : ℤ) :
    IsIntegral ℤ (elt (m : ℚ) (n : ℚ)) := by
  have hm : algebraMap ℚ Q_sqrt2 (m : ℚ) = algebraMap ℤ Q_sqrt2 m := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Q_sqrt2 m]
    norm_num
  have hn : algebraMap ℚ Q_sqrt2 (n : ℚ) = algebraMap ℤ Q_sqrt2 n := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Q_sqrt2 n]
    norm_num
  unfold elt
  rw [hm, hn]
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul root_isIntegral)

/-- **The element-level integral basis: `a + b·√2 ∈ 𝓞 ↔ a, b ∈ ℤ`.**
This is the complete membership description of the ring of integers of
`Q(√2)`; S12 packages it as `Basis (Fin 2) ℤ (𝓞 Q_sqrt2)` and computes
`discr = 8`. -/
theorem isIntegral_elt_iff (a b : ℚ) :
    IsIntegral ℤ (elt a b) ↔
      (∃ a0 : ℤ, (a0 : ℚ) = a) ∧ (∃ b0 : ℤ, (b0 : ℚ) = b) := by
  constructor
  · exact coords_int_of_isIntegral
  · rintro ⟨⟨a0, rfl⟩, ⟨b0, rfl⟩⟩
    exact isIntegral_elt_of_coords a0 b0

end Sqrt2MinpolyOQ03
