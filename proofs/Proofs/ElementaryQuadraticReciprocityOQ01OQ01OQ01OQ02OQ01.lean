/-
  # Lifting the Gauss-Sum QR Identity from ZMod q to ℤ
  # (elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02-oq-01)

  ## The Open Question

  **OQ-...-OQ-02-OQ-01**: The Gauss-sum pipeline natively produces a *congruence
  in ZMod q*:

      gauss_sum_zmod_qr :
        (-1 : ZMod q) ^ (p/2 · q/2) · (q/p) = (p/q)   in ZMod q

  (`GaussSumFullAssembly.gauss_sum_zmod_qr`, proved without axioms). The classical
  statement of quadratic reciprocity, however, is an *equation of integers*:

      legendreSym p q · legendreSym q p = (-1) ^ (p/2 · q/2)   in ℤ.

  How do you get from the ZMod q congruence to the integer identity?

  ## Answer: the four-sign lift

  Both Legendre symbols are units (`p ≠ q` are primes), hence each lies in
  `{+1, -1}`, and so does the sign `(-1)^(p/2·q/2)`. The Int.cast map `ℤ → ZMod q`
  is *injective on `{+1, -1}`* because `q` is an odd prime: `(1 : ZMod q) ≠ -1`
  (otherwise `q ∣ 2`). Therefore a congruence between two elements of `{+1, -1}`
  forces an honest integer equality. Concretely:

    * From `gauss_sum_zmod_qr`, `(p/q) ≡ (-1)^(p/2·q/2) · (q/p)  (mod q)`.
    * Both sides lie in `{+1, -1}`, so equality lifts to ℤ:
        `(p/q) = (-1)^(p/2·q/2) · (q/p)`.
    * Multiplying by `(q/p)` and using `(q/p)² = 1` gives
        `(p/q) · (q/p) = (-1)^(p/2·q/2)`.

  This is the "case analysis on the four sign possibilities of the two Legendre
  symbols" requested by the open question, made into a single clean lift.

  ## Significance

  This is the *last mile* of the Gauss-sum proof of quadratic reciprocity. The
  Gauss-sum machinery (`OQ01OQ01OQ01`, `OQ01OQ01OQ02`, and the assembly
  `OQ01OQ01OQ01OQ02`) lands in `ZMod q`; this file shows the elementary, purely
  arithmetic step that converts that congruence into the integer reciprocity law,
  *without* invoking Mathlib's black-box `legendreSym.quadratic_reciprocity`.

  ## Axiom count: 0
-/

import Proofs.ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

namespace GaussSumQRIntLift

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- **The {+1, -1} lift.** For an odd prime `q`, the cast `ℤ → ZMod q` is injective
    on `{+1, -1}`: two integers each equal to `±1` that are congruent mod `q` are
    equal. (The only obstruction would be `1 ≡ -1`, i.e. `q ∣ 2`, impossible for
    `q` odd.) -/
theorem int_pm_one_cast_inj [Fact (2 < q)] {x y : ℤ}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hxy : (x : ZMod q) = (y : ZMod q)) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · simp only [Int.cast_one, Int.cast_neg] at hxy
    exact absurd hxy.symm ZMod.neg_one_ne_one
  · simp only [Int.cast_one, Int.cast_neg] at hxy
    exact absurd hxy ZMod.neg_one_ne_one
  · rfl

/-- **Integer quadratic reciprocity via the Gauss-sum lift.**

    The product of Legendre symbols equals the reciprocity sign, obtained by
    lifting the ZMod q identity `gauss_sum_zmod_qr` to ℤ through the four-sign
    case analysis. This re-derives the reciprocity law from the Gauss-sum
    pipeline, independently of `legendreSym.quadratic_reciprocity`. -/
theorem qr_int_of_gauss_sum (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = (-1) ^ (p / 2 * (q / 2)) := by
  -- The native ZMod q identity from the (verified) Gauss-sum assembly.
  have hz := GaussSumFullAssembly.gauss_sum_zmod_qr (p := p) (q := q) hp2 hq2 hpq
  haveI : Fact (2 < q) := ⟨lt_of_le_of_ne hq.out.two_le (fun h => hq2 h.symm)⟩
  -- `q` is a unit mod `p` and vice versa, since `p ≠ q` are primes.
  have hqp : ((q : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hdvd)
  have hpq2 : ((p : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hdvd).symm
  -- Both Legendre symbols are ±1, and so is the reciprocity sign.
  have hA := legendreSym.eq_one_or_neg_one (p := p) hqp
  have hB := legendreSym.eq_one_or_neg_one (p := q) hpq2
  have hBsq := legendreSym.sq_one (p := q) hpq2
  set k := p / 2 * (q / 2) with hk
  have hE : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
    rcases Nat.even_or_odd k with he | ho
    · exact Or.inl he.neg_one_pow
    · exact Or.inr ho.neg_one_pow
  -- The right-hand side `(-1)^k · (q/p)` is itself ±1.
  have hmemEB : (-1 : ℤ) ^ k * legendreSym q (p : ℤ) = 1 ∨
      (-1 : ℤ) ^ k * legendreSym q (p : ℤ) = -1 := by
    rcases hE with h | h <;> rcases hB with h' | h' <;> rw [h, h'] <;> decide
  -- Lift the ZMod q congruence `(p/q) ≡ (-1)^k · (q/p)` to an integer equality,
  -- then clear `(q/p)` using `(q/p)² = 1`.
  have hAEB : legendreSym p (q : ℤ) = (-1 : ℤ) ^ k * legendreSym q (p : ℤ) := by
    apply int_pm_one_cast_inj (q := q) hA hmemEB
    push_cast
    exact hz.symm
  rw [hAEB, mul_assoc, ← pow_two, hBsq, mul_one]

-- ============================================================================
-- Concrete verifications (independent of the lift, by direct computation)
-- ============================================================================

/-- p = 3, q = 5: (3/5)·(5/3) = 1 = (-1)^(2·1). -/
example : legendreSym 3 (5 : ℤ) * legendreSym 5 (3 : ℤ) = (-1) ^ (3 / 2 * (5 / 2)) := by
  decide

/-- p = 3, q = 7: (3/7)·(7/3) = -1 = (-1)^(3·1). -/
example : legendreSym 3 (7 : ℤ) * legendreSym 7 (3 : ℤ) = (-1) ^ (3 / 2 * (7 / 2)) := by
  decide

end GaussSumQRIntLift

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `int_pm_one_cast_inj` | `ℤ → ZMod q` is injective on `{+1,-1}` for odd prime `q` |
  | `qr_int_of_gauss_sum` | `(p/q)·(q/p) = (-1)^(p/2·q/2)` in ℤ, lifted from `gauss_sum_zmod_qr` |

  The lift uses only:
    * `gauss_sum_zmod_qr` (the verified Gauss-sum identity in ZMod q),
    * `legendreSym.eq_one_or_neg_one` / `legendreSym.sq_one` (Legendre symbols are ±1),
    * `ZMod.neg_one_ne_one` (the {+1,-1} injectivity of the cast).

  It does **not** invoke `legendreSym.quadratic_reciprocity`, so it is a genuine
  re-derivation of the reciprocity sign from the Gauss-sum pipeline.

  **Sorries**: 0
  **Axioms**: 0
-/
