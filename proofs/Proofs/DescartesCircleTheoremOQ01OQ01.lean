/-
# The complex (extended) Descartes Circle Theorem over ℂ

Research: descartes-circle-theorem-oq-01-oq-01
Parent:   descartes-circle-theorem-oq-01 (real curvature relation and Soddy circles)

The parent file established the **real** Descartes Circle Theorem: four signed
curvatures `k₁,k₂,k₃,k₄` of mutually tangent circles satisfy
`(k₁+k₂+k₃+k₄)² = 2(k₁²+k₂²+k₃²+k₄²)`, and the two Soddy solutions
`k₄ = (k₁+k₂+k₃) ± 2√(k₁k₂+k₂k₃+k₃k₁)` exist precisely when the symmetric
product is *nonnegative* (so the real square root is defined).

The Lagarias–Mallows–Wilks "complex Descartes theorem" (2002) observes that the
*same* quadratic relation holds over `ℂ` — for the curvatures themselves and,
more strikingly, for the **curvature·centre products** `wᵢ = kᵢ·zᵢ` (with `zᵢ ∈ ℂ`
the circle centres):
`(w₁+w₂+w₃+w₄)² = 2(w₁²+w₂²+w₃²+w₄²)`.

This file formalises the algebraic core of that complex theory.  Its genuinely new
content, absent in the real parent, is that **over `ℂ` the fourth solution always
exists unconditionally** — the nonnegativity hypothesis on the discriminant
disappears because `ℂ` is algebraically closed, so the symmetric product always has
a (complex) square root.

Contributions:

* `descartesRelC` — the Descartes relation over `ℂ`.
* `descartesRelC_iff_sq` — the quadratic-in-`d` rewriting (a ring identity).
* `descartes_soddy_iff` — for *any* complex square root `s` of the symmetric
  product, the relation holds iff `d = (a+b+c) ± 2s`.
* `descartes_soddy_exists` — **unconditional existence** of a fourth solution over
  `ℂ`; the algebraically-closed phenomenon with no real analogue.
* `descartes_soddy_both`, `soddy_sumC`, `soddy_prodC` — both Soddy solutions and
  their Vieta sum/product.
* `descartesRelC_ofReal` — the bridge: restricted to real arguments the complex
  relation is exactly the parent's real Descartes relation.

Everything here is `sorry`-free and `axiom`-free (only the foundational
`propext`/`Classical.choice`/`Quot.sound`; no `Lean.ofReduceBool`).
-/
import Mathlib

namespace DescartesCircleTheoremOQ01OQ01

/-- The Descartes Circle relation over `ℂ`, among four complex "curvatures"
(or curvature·centre products) `a, b, c, d`. -/
def descartesRelC (a b c d : ℂ) : Prop :=
  (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)

/-- The complex Descartes relation is the quadratic-in-`d` perfect-square condition
`(d - (a+b+c))² = 4(ab+bc+ca)`. A ring identity, valid over any commutative ring. -/
theorem descartesRelC_iff_sq (a b c d : ℂ) :
    descartesRelC a b c d ↔
      (d - (a + b + c)) ^ 2 = 4 * (a * b + b * c + c * a) := by
  unfold descartesRelC
  constructor <;> intro h <;> linear_combination -h

/-- **Soddy solutions over `ℂ`.** For *any* complex square root `s` of the symmetric
product `ab+bc+ca`, the relation `descartesRelC a b c d` holds iff
`d = (a+b+c) + 2s` or `d = (a+b+c) - 2s`.  Unlike the real case this needs no sign
hypothesis: `s` exists for every `a,b,c` because `ℂ` is algebraically closed. -/
theorem descartes_soddy_iff {a b c d s : ℂ} (hs : s ^ 2 = a * b + b * c + c * a) :
    descartesRelC a b c d ↔ d = (a + b + c) + 2 * s ∨ d = (a + b + c) - 2 * s := by
  rw [descartesRelC_iff_sq]
  constructor
  · intro h
    have hfac :
        (d - (a + b + c) - 2 * s) * (d - (a + b + c) + 2 * s) = 0 := by
      linear_combination h - 4 * hs
    rcases mul_eq_zero.mp hfac with h' | h'
    · left; linear_combination h'
    · right; linear_combination h'
  · rintro (h | h) <;> subst h <;> linear_combination 4 * hs

/-- **Unconditional existence over `ℂ`.** Every triple of complex curvatures
`a, b, c` admits a fourth `d` satisfying the Descartes relation — the symmetric
product always has a complex square root, so no discriminant-nonnegativity is
required (contrast the real parent, which needs `0 ≤ ab+bc+ca`). -/
theorem descartes_soddy_exists (a b c : ℂ) : ∃ d : ℂ, descartesRelC a b c d := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (a * b + b * c + c * a) (n := 2) (by norm_num)
  exact ⟨(a + b + c) + 2 * s, (descartes_soddy_iff hs).mpr (Or.inl rfl)⟩

/-- Both Soddy values satisfy the relation, for any complex square root `s` of the
symmetric product. -/
theorem descartes_soddy_both {a b c s : ℂ} (hs : s ^ 2 = a * b + b * c + c * a) :
    descartesRelC a b c ((a + b + c) + 2 * s) ∧
      descartesRelC a b c ((a + b + c) - 2 * s) :=
  ⟨(descartes_soddy_iff hs).mpr (Or.inl rfl), (descartes_soddy_iff hs).mpr (Or.inr rfl)⟩

/-- **Vieta (sum).** The two Soddy curvatures sum to twice the outer-curvature sum. -/
theorem soddy_sumC (a b c s : ℂ) :
    ((a + b + c) + 2 * s) + ((a + b + c) - 2 * s) = 2 * (a + b + c) := by ring

/-- **Vieta (product).** The product of the two Soddy curvatures. -/
theorem soddy_prodC {a b c s : ℂ} (hs : s ^ 2 = a * b + b * c + c * a) :
    ((a + b + c) + 2 * s) * ((a + b + c) - 2 * s) =
      (a + b + c) ^ 2 - 4 * (a * b + b * c + c * a) := by
  linear_combination -4 * hs

/-- **Bridge to the real theorem.** Restricted to real arguments (cast into `ℂ`),
the complex Descartes relation is exactly the parent's real Descartes relation. -/
theorem descartesRelC_ofReal (k₁ k₂ k₃ k₄ : ℝ) :
    descartesRelC (k₁ : ℂ) k₂ k₃ k₄ ↔
      (k₁ + k₂ + k₃ + k₄) ^ 2 = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2) := by
  unfold descartesRelC
  norm_cast

/-- Concrete existence: three unit "curvatures" `a = b = c = 1` admit a fourth
complex Soddy curvature. -/
theorem descartes_soddy_exists_unit : ∃ d : ℂ, descartesRelC 1 1 1 d :=
  descartes_soddy_exists 1 1 1

end DescartesCircleTheoremOQ01OQ01
