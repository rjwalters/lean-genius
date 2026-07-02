/-
  Composition/commutation theory for the *second kind* Chebyshev polynomials `Uₙ`
  and the Dickson polynomials — which structural laws survive?

  The parent entry records the composition law for the first kind,
  `T_{m·n} = T_m ∘ T_n` (`Polynomial.Chebyshev.T_mul`), and derives from it that
  the `Tₙ` form a **commutative compositional monoid**: `X` is the identity, the
  `Tₙ` commute under `∘`, and composition is associative.  Open question #2 asks
  for the analogous story for the second-kind polynomials `Uₙ` and for the Dickson
  polynomials, *identifying which structural laws survive*.

  The answer splits sharply along the first-kind / second-kind divide.

  **Dickson polynomials of the first kind (parameter `a = 1`): the law SURVIVES.**
  The Dickson polynomials `Dₙ = dickson 1 1 n` are the `x ↦ 2x`-conjugate normal
  form of the first-kind Chebyshev polynomials (`dickson 1 1 n = Chebyshev.C n`,
  and `Cₙ(2x) = 2 Tₙ(x)`).  Conjugation is a monoid isomorphism of the
  compositional monoid, so the entire first-kind picture transports verbatim:

      D_{m·n} = D_m ∘ D_n     (`dickson_one_one_mul`)
      D₁ = X                  (compositional identity)
      D_m ∘ D_n = D_n ∘ D_m   (commutation)
      associativity of `∘`.

  So `n ↦ Dₙ` is again a monoid homomorphism `(ℕ, ·, 1) → (R[X], ∘, X)`.

  **Chebyshev polynomials of the second kind `Uₙ`: the law FAILS.**
  Here `U₁ = 2X ≠ X`.  Since `X` is the identity of the compositional monoid and
  `1` is the identity of `(ℕ, ·)`, any composition law `U_{m·n} = U_m ∘ U_n`
  would force `U₁ = U_{1·1} = U₁ ∘ U₁`, i.e. `2X = 4X` — false over `ℤ`.  The
  obstruction is intrinsic: `n ↦ Uₙ` cannot even be a monoid homomorphism into
  `(R[X], ∘, X)` because it does not send `1` to the identity.  A concrete
  higher-degree witness (via the evaluation homomorphism `Uₙ(1) = n+1`) is
  `U₄ ≠ U₂ ∘ U₂`: evaluating at `1` gives `5` on the left and `U₂(3) = 35` on the
  right.  The same failure holds for the second-kind Dickson polynomials
  `dickson 2 1 n = Chebyshev.S n` (with `Uₙ = Sₙ(2x)`): the compositional monoid
  structure is a phenomenon of the *first-kind* family alone.

  Contents:
    * `dickson_comp`, `dickson_one_eq_X`, `dickson_comp_one`, `dickson_one_comp`,
      `dickson_comp_comm`, `dickson_comp_assoc` — the surviving compositional
      monoid for the first-kind Dickson polynomials.
    * `dickson_eq_chebyshev_C` — the bridge explaining *why* it survives.
    * `U_one_ne_X`, `U_comp_law_fails_at_one`, `U_comp_law_fails_deg_two` — the
      three faces of the second-kind failure (identity, trivial case, quantitative
      witness).

  Verified: 0 sorries, 0 axioms (only propext / Classical.choice / Quot.sound;
  no native_decide, no Lean.ofReduceBool).
-/
import Mathlib

open Polynomial

namespace ChebyshevPolynomialsOQ01OQ02

open Polynomial.Chebyshev

variable (R : Type*) [CommRing R]

/-! ### Part 1: first-kind Dickson polynomials — the compositional monoid SURVIVES

The Dickson polynomials `Dₙ := dickson 1 1 n` inherit the full first-kind picture
because they are the `x ↦ 2x`-conjugate of the Chebyshev `Tₙ`. -/

/-- **Composition law for Dickson polynomials** (first kind, `a = 1`):
`D_{m·n} = D_m ∘ D_n`.  This is Mathlib's `dickson_one_one_mul`, the surviving
analogue of `T_{m·n} = T_m ∘ T_n`. -/
theorem dickson_comp (m n : ℕ) :
    dickson 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n) :=
  dickson_one_one_mul R m n

/-- `D₁ = X`: the first Dickson polynomial is the identity for composition. -/
theorem dickson_one_eq_X : dickson 1 (1 : R) 1 = X :=
  dickson_one 1 (1 : R)

/-- Right identity: `D_m ∘ D₁ = D_m` (since `D₁ = X`). -/
theorem dickson_comp_one (m : ℕ) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 1) = dickson 1 1 m := by
  rw [dickson_one, comp_X]

/-- Left identity: `D₁ ∘ p = p` for any polynomial `p` (since `D₁ = X`). -/
theorem dickson_one_comp (p : R[X]) :
    (dickson 1 (1 : R) 1).comp p = p := by
  rw [dickson_one, X_comp]

/-- **Commutation under composition**: `D_m ∘ D_n = D_n ∘ D_m`.  The Dickson
polynomials form a commuting family, exactly as the `Tₙ` do. -/
theorem dickson_comp_comm (m n : ℕ) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 n)
      = (dickson 1 1 n).comp (dickson 1 1 m) :=
  dickson_one_one_comp_comm R m n

/-- **Associativity** of Dickson composition: `D_{l·m·n}` is the triple composite
`(D_l ∘ D_m) ∘ D_n`. -/
theorem dickson_comp_assoc (l m n : ℕ) :
    dickson 1 (1 : R) (l * m * n)
      = ((dickson 1 1 l).comp (dickson 1 1 m)).comp (dickson 1 1 n) := by
  rw [dickson_comp, dickson_comp]

/-- **The bridge that explains survival.**  `Dₙ = Cₙ`, the first-kind Chebyshev
polynomial in its `2cos`-normalised form.  Together with `Cₙ(2x) = 2 Tₙ(x)`
(`Chebyshev.C_comp_two_mul_X`) this exhibits `Dₙ` as the `x ↦ 2x`-conjugate of
`Tₙ`; conjugation preserves the compositional monoid, which is why every
first-kind composition law transports to the Dickson polynomials. -/
theorem dickson_eq_chebyshev_C (n : ℕ) :
    dickson 1 (1 : R) n = Chebyshev.C R (n : ℤ) :=
  dickson_one_one_eq_chebyshev_C R n

/-! ### Part 2: second-kind Chebyshev polynomials `Uₙ` — the law FAILS

`U₁ = 2X ≠ X`, so `n ↦ Uₙ` does not send the multiplicative identity to the
compositional identity — the composition law cannot hold. -/

/-- `U₁ = 2X`, which is **not** the compositional identity `X`.  This is the root
obstruction: over `ℤ` the constant `2` is not `1`. -/
theorem U_one_ne_X : U ℤ 1 ≠ X := by
  rw [U_one]
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  simp at h1

/-- **The composition law fails already at the multiplicative identity.**
If `U_{m·n} = U_m ∘ U_n` held, then at `m = n = 1` it would say `U₁ = U₁ ∘ U₁`,
i.e. `2X = (2X) ∘ (2X) = 4X`.  Evaluating at `1` gives `2 = 4`, a contradiction.
Thus `n ↦ Uₙ` is not a homomorphism into the compositional monoid at all. -/
theorem U_comp_law_fails_at_one :
    U ℤ (1 * 1) ≠ (U ℤ 1).comp (U ℤ 1) := by
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  rw [eval_comp] at h1
  simp at h1

/-- **A quantitative higher-degree witness**: `U₄ ≠ U₂ ∘ U₂`.  Applying the
evaluation-at-`1` homomorphism and `Uₙ(1) = n + 1` (`U_eval_one`): the left side
gives `U₄(1) = 5`, while the right side gives `U₂(U₂(1)) = U₂(3) = 4·9 − 1 = 35`.
Since `5 ≠ 35` the two polynomials differ — the composition law fails on genuine
positive-degree inputs, not merely at the identity. -/
theorem U_comp_law_fails_deg_two :
    U ℤ 4 ≠ (U ℤ 2).comp (U ℤ 2) := by
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  rw [eval_comp, U_eval_one, U_eval_one, U_two] at h1
  simp at h1

end ChebyshevPolynomialsOQ01OQ02
