/-
  Aristotle targets for Sqrt2PlusSqrt3IrrationalOQ03
  Single sorry: irreducibility of X⁴ − 10X² + 1 over ℚ.
  See Sqrt2PlusSqrt3IrrationalOQ03.lean for the main formalization.

  ## Proof Strategy for irred_f

  To show X⁴ − 10X² + 1 is irreducible over ℚ, it suffices to show:

  (1) No rational roots: by the rational root theorem, candidates are ±1;
      direct evaluation gives f(1) = f(-1) = -8 ≠ 0.

  (2) No quadratic factors: any factorization into quadratics over ℚ must have
      the form (X² + aX + b)(X² − aX + d). Expanding and comparing coefficients:
        • bd = 1
        • a(d − b) = 0   →   a = 0 or d = b
        • b + d − a² = −10

      Case a = 0: b + d = −10, bd = 1. Discriminant of t² + 10t + 1 = 0 is 96;
        √96 ∉ ℚ, so no rational b, d.

      Case d = b: b² = 1, so b = ±1.
        • b = 1:  a² = 12, but √12 ∉ ℚ.
        • b = −1: a² = 8, but √8 ∉ ℚ.

  Degree-4 + no linear factors + no quadratic factors → irreducible over ℚ.

  ## Criteria for inclusion

  - NOT the main open conjecture (irrationality is already proved)
  - All sorries are theorem sorries (not definition sorries)
  - No axiom declarations
  - All are HARD supporting lemmas with known proofs
-/
import Mathlib

open Polynomial

namespace Sqrt2PlusSqrt3IrrationalOQ03

-- ============================================================
-- SECTION I: Evaluation Helpers (TRIVIAL)
-- ============================================================

/-- f(1) = 1 - 10 + 1 = -8 ≠ 0, so 1 is not a rational root. -/
private lemma f_eval_one :
    (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).eval 1 = -8 := by
  sorry

/-- f(-1) = 1 - 10 + 1 = -8 ≠ 0, so -1 is not a rational root. -/
private lemma f_eval_neg_one :
    (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).eval (-1) = -8 := by
  sorry

-- ============================================================
-- SECTION II: Main Target (HARD)
-- ============================================================

/-- X⁴ − 10X² + 1 is irreducible over ℚ.

    Proof by cases on any factorization p = a * b in ℚ[X]:
    - If deg(a) = 1: p has a rational root, contradicting f(±1) = -8 ≠ 0
      (only rational root candidates by the rational root theorem are ±1).
    - If deg(a) = 2: quadratic factorization (X² + aX + b)(X² − aX + d)
      forces the coefficient system bd=1, a(d-b)=0, b+d-a²=-10 to have
      rational solutions. Analysis shows all cases lead to irrational squares:
      discriminant 96 (case a=0) or a²∈{8,12} (case d=b). -/
private theorem irred_f : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]) := by
  sorry

end Sqrt2PlusSqrt3IrrationalOQ03
