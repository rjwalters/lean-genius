/-
  Fermat Defect-One — OQ-06: the sign-flip structural map

  Parent problem (`Proofs.FermatDefectOne`): does the Fermat defect
  $|a^n + b^n - c^n|$ ever equal exactly $1$ for a primitive nontrivial triple
  $2 \le a \le b < c$, $\gcd(a,b,c) = 1$?  At $n = 3$ both signs are witnessed,
  each along an explicit Mahler family (`FermatDefectOneFamilies.lean`,
  `FermatDefectOneNegInfinitude.lean`):

      negative defect  $a^3 + b^3 + 1 = c^3$   (i.e. $a^3+b^3-c^3 = -1$)
      positive defect  $a^3 + b^3 = c^3 + 1$   (i.e. $a^3+b^3-c^3 = +1$)

  OQ-06 asks the **symmetry-between-signs** question: is there a *structural map*
  (sign-flip / involution) carrying negative-defect witnesses to positive-defect
  witnesses and back?

  ## Answer: yes — an explicit involution that negates the cubic defect

  Working over `ℤ` (so the `±1` is a single signed quantity rather than a
  `Nat`-disjunction), define

      Ψ(a, b, c) = (c, -b, a).

  Then `Ψ` is an **involution** (`Ψ ∘ Ψ = id`, `signFlip_involutive`) and it
  **negates the cubic defect**:

      (Ψ(a,b,c) as (a',b',c')):   a'^3 + b'^3 - c'^3 = -(a^3 + b^3 - c^3)
      (`signFlip_negates_defect`).

  Consequently `Ψ` carries every integer negative-defect solution to a
  positive-defect solution and vice versa (`signFlip_neg_to_pos`,
  `signFlip_pos_to_neg`).  This is the structural sign-flip map OQ-06 asks for.

  ## Compatibility with the Mahler families

  The two gallery families are
      negTriple t = (9t⁴ − 3t, 9t³ − 1, 9t⁴)      (negative defect, `defect_neg_family`)
      posTriple t = (9t⁴,      9t³ + 1, 9t⁴ + 3t)  (positive defect, `defect_pos_family`)
  and on these families `Ψ` is exactly the **parameter-negation** `t ↦ −t`:

      Ψ(negTriple t) = posTriple (−t)        (`signFlip_negTriple`)
      Ψ(posTriple t) = negTriple (−t)        (`signFlip_posTriple`).

  So the sign symmetry of the defect at $n = 3$ is the involution `t ↦ −t` of
  Mahler's parametrization of $x^3 + y^3 + z^3 = 1$, realised pointwise by `Ψ`.
  The canonical taxicab witness `(9,10,12)` is `Ψ` applied to the negative-defect
  point `negTriple (−1) = (12,−10,9)` (`taxicab_is_signflip_of_neg`).

  Everything here is a polynomial identity over `ℤ`, closed by `ring` /
  `linear_combination` / `norm_num`.  No `axiom`, no `sorry`, no `native_decide`:
  this is a fully verified, 0-axiom result.
-/

import Mathlib
import Proofs.FermatDefectOne
import Proofs.FermatDefectOneFamilies

namespace FermatDefectOneOQ06

open scoped Polynomial

/-! ## The structural sign-flip map -/

/-- The **sign-flip map** on integer triples: `Ψ(a, b, c) = (c, -b, a)`.
This is the structural map OQ-06 asks for: it is an involution and it negates
the cubic defect `a³ + b³ - c³`. -/
def signFlip (T : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (T.2.2, -T.2.1, T.1)

/-- `Ψ` is an **involution**: applying it twice is the identity.
`(a,b,c) ↦ (c,-b,a) ↦ (a, -(-b), c) = (a,b,c)`. -/
@[simp] theorem signFlip_involutive (T : ℤ × ℤ × ℤ) : signFlip (signFlip T) = T := by
  simp [signFlip]

/-- **Headline.** `Ψ` negates the cubic defect: if `Ψ(a,b,c) = (a',b',c')` then
`a'³ + b'³ - c'³ = -(a³ + b³ - c³)`.  Hence `Ψ` exchanges the two defect signs. -/
theorem signFlip_negates_defect (a b c : ℤ) :
    (signFlip (a, b, c)).1 ^ 3 + (signFlip (a, b, c)).2.1 ^ 3
        - (signFlip (a, b, c)).2.2 ^ 3
      = -(a ^ 3 + b ^ 3 - c ^ 3) := by
  simp only [signFlip]
  ring

/-- `Ψ` carries every integer **negative-defect** solution `a³ + b³ + 1 = c³`
to a **positive-defect** solution `a'³ + b'³ = c'³ + 1`. -/
theorem signFlip_neg_to_pos {a b c : ℤ} (h : a ^ 3 + b ^ 3 + 1 = c ^ 3) :
    (signFlip (a, b, c)).1 ^ 3 + (signFlip (a, b, c)).2.1 ^ 3
      = (signFlip (a, b, c)).2.2 ^ 3 + 1 := by
  simp only [signFlip]
  linear_combination -h

/-- `Ψ` carries every integer **positive-defect** solution `a³ + b³ = c³ + 1`
to a **negative-defect** solution `a'³ + b'³ + 1 = c'³`. -/
theorem signFlip_pos_to_neg {a b c : ℤ} (h : a ^ 3 + b ^ 3 = c ^ 3 + 1) :
    (signFlip (a, b, c)).1 ^ 3 + (signFlip (a, b, c)).2.1 ^ 3 + 1
      = (signFlip (a, b, c)).2.2 ^ 3 := by
  simp only [signFlip]
  linear_combination -h

/-! ## The Mahler families and parameter negation

`Ψ` restricted to the gallery families is the parameter involution `t ↦ −t`. -/

/-- Negative-defect base triple from the Mahler parameter `t`:
`(9t⁴ − 3t, 9t³ − 1, 9t⁴)`, satisfying `a³ + b³ + 1 = c³`
(`FermatDefectOne.defect_neg_family`).  `t = 1 ↦ (6, 8, 9)`. -/
def negTriple (t : ℤ) : ℤ × ℤ × ℤ := (9 * t ^ 4 - 3 * t, 9 * t ^ 3 - 1, 9 * t ^ 4)

/-- Positive-defect base triple from the Mahler parameter `t`:
`(9t⁴, 9t³ + 1, 9t⁴ + 3t)`, satisfying `a³ + b³ = c³ + 1`
(`FermatDefectOne.defect_pos_family`).  `t = 1 ↦ (9, 10, 12)`. -/
def posTriple (t : ℤ) : ℤ × ℤ × ℤ := (9 * t ^ 4, 9 * t ^ 3 + 1, 9 * t ^ 4 + 3 * t)

/-- The negative-defect triple really satisfies the negative-defect equation. -/
theorem negTriple_defect (t : ℤ) :
    (negTriple t).1 ^ 3 + (negTriple t).2.1 ^ 3 + 1 = (negTriple t).2.2 ^ 3 := by
  simp only [negTriple]
  ring

/-- The positive-defect triple really satisfies the positive-defect equation. -/
theorem posTriple_defect (t : ℤ) :
    (posTriple t).1 ^ 3 + (posTriple t).2.1 ^ 3 = (posTriple t).2.2 ^ 3 + 1 := by
  simp only [posTriple]
  ring

/-- **Compatibility.** On the Mahler families `Ψ` is the parameter involution:
`Ψ(negTriple t) = posTriple (−t)`. -/
theorem signFlip_negTriple (t : ℤ) : signFlip (negTriple t) = posTriple (-t) := by
  simp only [signFlip, negTriple, posTriple, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **Compatibility (other branch).** `Ψ(posTriple t) = negTriple (−t)`. -/
theorem signFlip_posTriple (t : ℤ) : signFlip (posTriple t) = negTriple (-t) := by
  simp only [signFlip, posTriple, negTriple, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- The two compatibilities are consistent with `Ψ` being an involution: applying
`Ψ` twice to a negative-defect Mahler point returns the same point (parameter
`t ↦ −t ↦ t`). -/
theorem signFlip_negTriple_involutive (t : ℤ) :
    signFlip (signFlip (negTriple t)) = negTriple t := by
  simp

/-! ## Concrete benchmarks

The two gallery benchmarks `(6,8,9)` (negative) and `(9,10,12)` (positive)
are related by the sign-flip map. -/

/-- `negTriple 1 = (6, 8, 9)`, the negative-defect benchmark. -/
theorem negTriple_one : negTriple 1 = (6, 8, 9) := by
  simp only [negTriple]; norm_num

/-- `posTriple 1 = (9, 10, 12)`, the positive-defect (taxicab) benchmark. -/
theorem posTriple_one : posTriple 1 = (9, 10, 12) := by
  simp only [posTriple]; norm_num

/-- `Ψ` sends the negative benchmark `(6,8,9)` to the integer positive-defect
solution `(9, -8, 6)`: indeed `9³ + (-8)³ = 6³ + 1` (`729 - 512 = 217`). -/
theorem signFlip_benchmark : signFlip (6, 8, 9) = (9, -8, 6) := by
  simp only [signFlip]

/-- The image `(9, -8, 6)` is genuinely a positive-defect solution over `ℤ`. -/
theorem signFlip_benchmark_pos_defect : (9 : ℤ) ^ 3 + (-8) ^ 3 = 6 ^ 3 + 1 := by
  norm_num

/-- The **canonical taxicab positive witness** `(9,10,12) = posTriple 1` is the
sign-flip image of the negative-defect Mahler point `negTriple (-1) = (12,-10,9)`.
So `(6,8,9) → (9,10,12)` is realised structurally through the parameter
involution: `posTriple 1 = Ψ(negTriple (-1))`. -/
theorem taxicab_is_signflip_of_neg :
    posTriple 1 = signFlip (negTriple (-1)) := by
  rw [signFlip_negTriple]; norm_num

/-- `negTriple (-1) = (12, -10, 9)`, an integer negative-defect solution
(`12³ + (-10)³ + 1 = 9³`). -/
theorem negTriple_neg_one : negTriple (-1) = (12, -10, 9) := by
  simp only [negTriple]; norm_num

/-! ## Summary statement

Both signs at `n = 3` are the two branches of one identity under `t ↦ -t`. -/

/-- **Sign symmetry (OQ-06), packaged.** For every parameter `t`:
* the negative-defect Mahler triple satisfies `a³ + b³ + 1 = c³`;
* the positive-defect Mahler triple satisfies `a³ + b³ = c³ + 1`;
* the explicit involution `Ψ(a,b,c) = (c,-b,a)` carries one to the other,
  matching the parameter negation `t ↦ -t`. -/
theorem sign_symmetry (t : ℤ) :
    ((negTriple t).1 ^ 3 + (negTriple t).2.1 ^ 3 + 1 = (negTriple t).2.2 ^ 3) ∧
    ((posTriple t).1 ^ 3 + (posTriple t).2.1 ^ 3 = (posTriple t).2.2 ^ 3 + 1) ∧
    (signFlip (negTriple t) = posTriple (-t)) ∧
    (signFlip (posTriple t) = negTriple (-t)) :=
  ⟨negTriple_defect t, posTriple_defect t, signFlip_negTriple t, signFlip_posTriple t⟩

end FermatDefectOneOQ06
