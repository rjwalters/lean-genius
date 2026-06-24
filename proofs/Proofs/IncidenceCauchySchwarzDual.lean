/-
  The Symmetric Elementary Incidence Bound (Cauchy–Schwarz, both projections)

  `IncidenceCauchySchwarz.lean` proves the elementary incidence bound from the
  hypothesis that **two distinct lines meet in at most one point**:

        I² ≤ |P|·|L|² + |P|·I,   equivalently   I ≤ |P| + |L|·√|P|.

  That bound is asymmetric in the roles of points and lines. The incidence count
  `I`, however, is perfectly symmetric: it does not matter whether we sum line
  degrees over points or point degrees over lines. This file makes that symmetry
  do real work.

  Applying the *same* combinatorial argument to the **flipped** incidence
  relation `flip Inc : L → P → Prop` — under the dual hypothesis that **two
  distinct points lie on at most one common line** — yields the dual bound

        I² ≤ |L|·|P|² + |L|·I,   equivalently   I ≤ |L| + |P|·√|L|.

  Together the two bounds give the symmetric minimum

        I ≤ min( |P| + |L|·√|P| , |L| + |P|·√|L| ),

  which strictly improves on either projection when one side is much smaller
  than the other (e.g. few lines, many points). Neither projection dominates,
  so the `min` is the honest elementary statement.

  All of this is obtained with **no new combinatorics**: the forward file's
  theorems are reused verbatim on the flipped relation, after the single
  observation `incidences (flip Inc) = incidences Inc` (Fubini for the
  incidence indicator). It is the symmetric completion of the infrastructure-free
  half of prob-method-applications OQ-02. The genuine Szemerédi–Trotter exponent
  `(|P||L|)^{2/3}` still requires crossing-number / planar-drawing infrastructure
  that Mathlib does not provide; these elementary √-bounds are its ceiling.

  Status: 0 sorries, 0 axioms. No `native_decide`.
-/
import Mathlib
import Proofs.IncidenceCauchySchwarz

namespace ProbMethod.Incidence

open Finset BigOperators

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
variable (Inc : P → L → Prop) [∀ p ℓ, Decidable (Inc p ℓ)]

/-- Decidability transports across `flip`: `flip Inc ℓ p` is definitionally
    `Inc p ℓ`, so it inherits the point-line decidability instance. -/
instance flipDecidable : ∀ ℓ p, Decidable (flip Inc ℓ p) :=
  fun ℓ p => (inferInstance : Decidable (Inc p ℓ))

-- ═══════════════════════════════════════════════════
-- Part I: the incidence count is flip-invariant
-- ═══════════════════════════════════════════════════

/-- **Incidences are symmetric.** Summing line-degrees over points equals
    summing point-degrees over lines — this is Fubini for the `0/1` incidence
    indicator. Hence the flipped structure has exactly the same incidence count. -/
theorem incidences_flip : incidences (flip Inc) = incidences Inc := by
  -- `flip Inc ℓ p` is definitionally `Inc p ℓ`, so after expanding both incidence
  -- counts to double sums of `0/1` indicators, `Finset.sum_comm` matches them and
  -- the residual goal closes by reflexivity (the `flip` decidability instance is
  -- definitionally the ambient one).
  unfold incidences deg
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

-- ═══════════════════════════════════════════════════
-- Part II: the dual hypothesis
-- ═══════════════════════════════════════════════════

/-- The dual of `TwoLinesMeetOnce`: **two distinct points lie on at most one
    common line.** This is exactly `TwoLinesMeetOnce` applied to `flip Inc`. -/
def TwoPointsJoinOnce : Prop :=
  ∀ p₁ p₂ : P, p₁ ≠ p₂ →
    (univ.filter (fun ℓ => Inc p₁ ℓ ∧ Inc p₂ ℓ)).card ≤ 1

/-- The dual hypothesis on `Inc` is *definitionally* the once-meeting hypothesis
    on the flipped relation: `flip Inc p ℓ` reduces to `Inc ℓ p`, and the flip
    decidability instance is the ambient one, so the two `Prop`s coincide. -/
theorem twoPointsJoinOnce_iff_flip :
    TwoPointsJoinOnce Inc ↔ TwoLinesMeetOnce (flip Inc) := Iff.rfl

-- ═══════════════════════════════════════════════════
-- Part III: the dual incidence bound
-- ═══════════════════════════════════════════════════

/-- **Dual incidence bound (polynomial form).** Under the dual hypothesis that
    two distinct points share at most one line,
    `I² ≤ |L|·|P|² + |L|·I`. Obtained by running `incidence_bound` on the
    flipped structure (points and lines exchanged) and rewriting the
    flip-invariant incidence count. -/
theorem incidence_bound_dual (h : TwoPointsJoinOnce Inc) :
    incidences Inc ^ 2
      ≤ Fintype.card L * Fintype.card P ^ 2 + Fintype.card L * incidences Inc := by
  have hflip : TwoLinesMeetOnce (flip Inc) := (twoPointsJoinOnce_iff_flip Inc).mp h
  have hb := incidence_bound (flip Inc) hflip
  rwa [incidences_flip] at hb

/-- **Dual incidence bound (square-root form).**
    `I ≤ |L| + |P|·√|L|`. -/
theorem incidence_bound_dual_sqrt (h : TwoPointsJoinOnce Inc) :
    (incidences Inc : ℝ)
      ≤ Fintype.card L + Fintype.card P * Real.sqrt (Fintype.card L) := by
  have hflip : TwoLinesMeetOnce (flip Inc) := (twoPointsJoinOnce_iff_flip Inc).mp h
  have hb := incidence_bound_sqrt (flip Inc) hflip
  rwa [incidences_flip] at hb

-- ═══════════════════════════════════════════════════
-- Part IV: the symmetric minimum
-- ═══════════════════════════════════════════════════

/-- **Symmetric elementary incidence bound.** When *both* the once-meeting and
    the once-joining hypotheses hold (the standard point–line incidence axioms),
    the incidence count is bounded by the smaller of the two projections:

      `I ≤ min( |P| + |L|·√|P| , |L| + |P|·√|L| )`.

    Neither term dominates the other, so this `min` is a genuine strengthening
    of each individual Cauchy–Schwarz bound: when there are far fewer lines than
    points (or vice versa), the dual projection is sharper. This is the sharpest
    bound the elementary Cauchy–Schwarz argument can give — the
    `(|P||L|)^{2/3}` Szemerédi–Trotter exponent lies beyond it. -/
theorem incidence_bound_min
    (h₁ : TwoLinesMeetOnce Inc) (h₂ : TwoPointsJoinOnce Inc) :
    (incidences Inc : ℝ)
      ≤ min (Fintype.card P + Fintype.card L * Real.sqrt (Fintype.card P))
            (Fintype.card L + Fintype.card P * Real.sqrt (Fintype.card L)) :=
  le_min (incidence_bound_sqrt Inc h₁) (incidence_bound_dual_sqrt Inc h₂)

end ProbMethod.Incidence
