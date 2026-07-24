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

end Sqrt2MinpolyOQ03
