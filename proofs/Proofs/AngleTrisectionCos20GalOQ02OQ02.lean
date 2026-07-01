import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import Proofs.AngleTrisectionCos20GalOQ02

/-
# angle-trisection-cos-20-gal OQ-02-OQ-02: the minimal polynomial of `cos 2π/n` is an irreducible factor of `Tₙ − 1`

The parent entry (`angle-trisection-cos-20-gal-oq-02`) proves the Chebyshev witness
`Tₙ(cos 2π/n) = cos(2π) = 1`, so `cos 2π/n` is a root of `Tₙ − 1`, and lists as an open
question:

> *Identify the irreducible factor of `Tₙ − 1` of degree `φ(n)/2` (the minimal polynomial of
> `cos 2π/n`) and relate it to the cyclotomic polynomial `Φₙ`.*

The **exact degree** `φ(n)/2` is blocked on the absence of the maximal-real-subfield degree
in Mathlib. What is *not* blocked is the structural half of the statement — that the minimal
polynomial of `cos 2π/n` really is an irreducible factor of `Tₙ − 1`. This file proves that
in full generality (all `n ≥ 1`), with `0` axioms:

1. `aeval_cos_cheb` : `aeval (cos 2π/n) (Tₙ) = 1` over `ℚ` (lifting the parent's real-valued
   `Tₙ(cos 2π/n) = 1` through `Polynomial.Chebyshev.map_T`).
2. `chebT_sub_one_ne_zero` : `Tₙ − 1 ≠ 0` in `ℚ[X]` (via evaluation at `cos(π/n)`, where
   `Tₙ = cos π = −1 ≠ 1`).
3. `cos_isIntegral` : `cos 2π/n` is integral over `ℚ` — a root of the nonzero `Tₙ − 1`.
4. `minpoly_cos_dvd_chebT` : **`minpoly ℚ (cos 2π/n) ∣ (Tₙ − 1)`** — the minimal polynomial is
   a *factor* of `Tₙ − 1` (the divisibility half of the open question).
5. `minpoly_cos_irreducible` : the minimal polynomial is irreducible; with (4), it is an
   *irreducible factor* of `Tₙ − 1`.
6. `minpoly_cos_natDegree_le` : `deg (minpoly) ≤ deg (Tₙ − 1)` — the unconditional upper bound
   that divisibility gives (the sharp `φ(n)/2` remains the open refinement).

The whole file is `0` sorries / `0` axioms (`#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`; no `native_decide`).

Parent: AngleTrisectionCos20GalOQ02.lean (`cos_two_pi_div_chebyshev_root`).
-/

namespace AngleTrisectionCos20GalOQ02OQ02

open Complex Polynomial

/-- **`aeval (cos 2π/n) Tₙ = 1` over `ℚ`.** The parent proves the real-valued identity
    `(Tₙ : ℝ[X]).eval (cos 2π/n) = 1`; pushing `Tₙ ∈ ℚ[X]` through `algebraMap ℚ ℝ` via
    `Polynomial.Chebyshev.map_T` transports it to the `ℚ`-algebra evaluation `aeval`. -/
theorem aeval_cos_cheb (n : ℕ) (hn : n ≠ 0) :
    aeval (Real.cos (2 * Real.pi / n)) (Polynomial.Chebyshev.T ℚ (n : ℤ)) = 1 := by
  rw [aeval_def, eval₂_eq_eval_map, Polynomial.Chebyshev.map_T]
  exact AngleTrisectionCos20GalOQ02.cos_two_pi_div_chebyshev_root n hn

/-- **`Tₙ − 1 ∈ ℚ[X]` is nonzero for `n ≥ 1`.** If it vanished, mapping to `ℝ[X]` would make
    `Tₙ = 1` as a polynomial, but `(Tₙ : ℝ[X]).eval (cos(π/n)) = cos(n·π/n) = cos π = −1 ≠ 1`. -/
theorem chebT_sub_one_ne_zero (n : ℕ) (hn : n ≠ 0) :
    Polynomial.Chebyshev.T ℚ (n : ℤ) - 1 ≠ 0 := by
  have hcast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  intro h
  have hmap : (Polynomial.Chebyshev.T ℝ (n : ℤ)) - 1 = 0 := by
    have h2 := congrArg (Polynomial.map (algebraMap ℚ ℝ)) h
    rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_zero,
        Polynomial.Chebyshev.map_T] at h2
    exact h2
  have heval := congrArg (Polynomial.eval (Real.cos (Real.pi / (n : ℝ)))) hmap
  rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_zero,
      Polynomial.Chebyshev.T_real_cos] at heval
  rw [show ((n : ℤ) : ℝ) * (Real.pi / (n : ℝ)) = Real.pi by push_cast; field_simp] at heval
  rw [Real.cos_pi] at heval
  norm_num at heval

/-- **`cos 2π/n` is integral over `ℚ`** — a root of the nonzero polynomial `Tₙ − 1`. -/
theorem cos_isIntegral (n : ℕ) (hn : n ≠ 0) :
    IsIntegral ℚ (Real.cos (2 * Real.pi / n)) := by
  have halg : IsAlgebraic ℚ (Real.cos (2 * Real.pi / n)) :=
    ⟨Polynomial.Chebyshev.T ℚ (n : ℤ) - 1, chebT_sub_one_ne_zero n hn, by
      rw [map_sub, aeval_cos_cheb n hn, map_one, sub_self]⟩
  exact halg.isIntegral

/-- **The minimal polynomial of `cos 2π/n` divides `Tₙ − 1` in `ℚ[X]`.** This is the
    divisibility half of the open question: the minimal polynomial is a *factor* of `Tₙ − 1`.
    Since `cos 2π/n` is a root of `Tₙ − 1`, `minpoly.dvd` applies directly. -/
theorem minpoly_cos_dvd_chebT (n : ℕ) (hn : n ≠ 0) :
    minpoly ℚ (Real.cos (2 * Real.pi / n)) ∣ (Polynomial.Chebyshev.T ℚ (n : ℤ) - 1) := by
  refine minpoly.dvd ℚ _ ?_
  rw [map_sub, aeval_cos_cheb n hn, map_one, sub_self]

/-- **The minimal polynomial is irreducible.** Combined with `minpoly_cos_dvd_chebT`, this
    says `minpoly ℚ (cos 2π/n)` is an *irreducible factor* of `Tₙ − 1` — the precise structural
    content of the open question, save for the exact degree `φ(n)/2`. -/
theorem minpoly_cos_irreducible (n : ℕ) (hn : n ≠ 0) :
    Irreducible (minpoly ℚ (Real.cos (2 * Real.pi / n))) :=
  minpoly.irreducible (cos_isIntegral n hn)

/-- **Degree bound.** The minimal polynomial's degree is bounded by that of `Tₙ − 1`. The
    open question conjectures the sharp value `φ(n)/2`; this is the (non-sharp) upper bound
    that divisibility gives unconditionally. -/
theorem minpoly_cos_natDegree_le (n : ℕ) (hn : n ≠ 0) :
    (minpoly ℚ (Real.cos (2 * Real.pi / n))).natDegree
      ≤ (Polynomial.Chebyshev.T ℚ (n : ℤ) - 1).natDegree :=
  Polynomial.natDegree_le_of_dvd (minpoly_cos_dvd_chebT n hn) (chebT_sub_one_ne_zero n hn)

end AngleTrisectionCos20GalOQ02OQ02
