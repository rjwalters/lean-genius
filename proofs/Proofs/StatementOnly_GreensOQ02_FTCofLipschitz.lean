/-
Keystone lemma for `greens-theorem-oq-02-oq-02`.

Open question: can the axiom `greens_theorem_l1curl`
(`proofs/Proofs/GreensTheoremOQ02.lean:361`) — Green's theorem on a rectangle
under an L¹ curl + Lipschitz boundary — be discharged using Mathlib's existing
`BoundedVariation` and Radon–Nikodym API?

Prior analysis (`research/problems/greens-theorem-oq-02-oq-02/knowledge.md`)
reduced the whole axiom, via Fubini (`MeasureTheory.integral_prod`), to the
**Fundamental Theorem of Calculus for absolutely continuous functions**:
`f b - f a = ∫ x in a..b, deriv f x` where `deriv f` is only a.e./L¹ defined.
Mathlib's `FundThmCalculus` provides only the continuity / `HasDerivAt`-everywhere
versions and lacks this Lebesgue/AC direction.

This file isolates the cleanest tractable **first building block** of that gap:
the FTC for a **Lipschitz** function. A Lipschitz function on `[a,b]` is
absolutely continuous, is differentiable a.e. (Rademacher / monotone-BV
decomposition), has a bounded — hence L¹ — derivative, and satisfies the FTC.
This is strictly weaker than the general AC version the axiom ultimately needs
(the rectangle Green's reduction only yields AC, not Lipschitz, partials), but
it captures the hard "AC ⟹ FTC" content in a statement Mathlib can express
without a dedicated `AbsolutelyContinuous`-of-functions predicate, and the
rectangle's boundary edges are themselves Lipschitz.

If this lemma can be proved from Mathlib, the keystone gap is real but bounded;
the next step is the general AC statement, then the Fubini discharge of the
axiom.
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open MeasureTheory intervalIntegral

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace GreensOQ02Statement

/-- FTC for Lipschitz functions: a Lipschitz function on `[a,b]` equals the
integral of its (everywhere-defined, a.e.-correct) derivative. Keystone gap
toward Green's theorem on a rectangle with L¹ curl. -/
theorem ftc_of_lipschitzOn (f : ℝ → ℝ) (a b : ℝ) (K : NNReal)
    (hab : a ≤ b) (hf : LipschitzOnWith K f (Set.Icc a b)) :
    f b - f a = ∫ x in a..b, deriv f x := by
  sorry

-- Proof attempt (Rivin scaffolding — Aristotle may ignore or refine this):
-- 1. A Lipschitz function is absolutely continuous on `[a,b]`; in particular it
--    has locally bounded variation, so by Lebesgue's differentiation theorem
--    `f` is differentiable a.e. on `[a,b]` (Mathlib: `LipschitzOnWith`/
--    `LipschitzWith.ae_differentiableAt` via Rademacher in 1D).
-- 2. On the set of differentiability, `deriv f` agrees with the a.e. derivative
--    and is bounded by `K`, hence `IntervalIntegrable (deriv f) volume a b`.
-- 3. Apply an FTC-for-AC bridge. The natural Mathlib hook is
--    `integral_eq_sub_of_hasDeriv_right_of_le`, which needs:
--      • `ContinuousOn f (Set.Icc a b)` — from Lipschitz continuity, and
--      • `∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ioi x) x` — only
--        available a.e., so the everywhere-right-derivative hypothesis is the
--        true obstruction and is exactly what the AC theory must supply.
-- 4. Conclude `f b - f a = ∫ x in a..b, deriv f x`.

end GreensOQ02Statement
