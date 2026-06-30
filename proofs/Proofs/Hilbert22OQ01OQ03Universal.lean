import Mathlib
import Proofs.Hilbert22OQ01OQ03

/-
# Hilbert 22 — OQ-01-OQ-03 (continued): Universal property and the vanishing criterion

## Research Problem: hilbert-22-oq-01-oq-03

The companion file `Hilbert22OQ01OQ03.lean` builds the abstract Kobayashi chain
pseudometric `chainDist c` from a symmetric atomic cost `c : X → X → ℝ≥0∞`
vanishing on the diagonal, and proves it is a `PseudoEMetricSpace` that is
functorial (distance-non-increasing under cost-contracting maps).

This file proves the two structural facts that *characterize* that construction and
that drive every concrete computation of a Kobayashi-type pseudometric — still in
pure `ℝ≥0∞` order theory, with no complex analysis:

* **Universal property.** `chainDist c` is the *greatest* subadditive (triangle-law)
  cost dominated by the atomic cost `c`:
    - `chainDist_le_cost`  : `chainDist c ≤ c`  (a single-edge chain), and
    - `le_chainDist`       : every triangle-law `d` with `d ≤ c` satisfies
                              `d ≤ chainDist c`.
  Together these say `chainDist c = ⨆ { d | d subadditive, d ≤ c }`. This is the
  abstract reason the Kobayashi pseudometric is the largest pseudometric for which
  all holomorphic disks are non-expanding.

* **Vanishing criterion.** `chainDist c p q = 0` as soon as `p` and `q` are joined
  by arbitrarily cheap chains (`chainDist_eq_zero_of_forall`), with the handy
  special cases `c p q = 0` and a one-vertex bridge. This is the order-theoretic
  core of *non-hyperbolicity*: e.g. on `ℂ` the affine maps `z ↦ p + (q-p)z/δ`
  push the disk Poincaré cost to `0`, so `d_ℂ ≡ 0`. Once the disk atomic cost is
  in place, "ℂ is not Kobayashi hyperbolic" reduces to exhibiting such cheap chains
  and applying `chainDist_eq_zero_of_forall`.

No sorries, no axioms beyond Mathlib's foundations.

Tags: complex-geometry, kobayashi-metric, hyperbolic-manifolds, pseudometric,
universal-property, hilbert-problems
-/

namespace Hilbert22OQ01OQ03

open scoped ENNReal

variable {X : Type*}

-- ============================================================
-- Part V: Monotonicity of the chain cost in the atomic cost
-- ============================================================

/-- The cost of a fixed chain is monotone in the atomic cost: a pointwise-smaller
atomic cost gives a smaller chain cost. (This is `chainCost_map` specialised to the
identity map, but stated directly for clarity.) -/
theorem chainCost_mono_cost (c₁ c₂ : X → X → ℝ≥0∞) (h : ∀ a b, c₁ a b ≤ c₂ a b)
    (q : X) (mid : List X) : ∀ p, chainCost c₁ p mid q ≤ chainCost c₂ p mid q := by
  induction mid with
  | nil => intro p; simpa using h p q
  | cons x xs ih =>
      intro p
      simp only [chainCost_cons]
      exact add_le_add (h p x) (ih x)

-- ============================================================
-- Part VI: The universal property
-- ============================================================

/-- The chain pseudometric never exceeds the atomic cost: the single-edge chain
`p ⇝ q` already realises cost `c p q`. -/
theorem chainDist_le_cost (c : X → X → ℝ≥0∞) (p q : X) : chainDist c p q ≤ c p q := by
  simpa using chainDist_le c p q []

/-- **Telescoping.** Any `d` satisfying the triangle law is bounded by the
`d`-cost of every chain: summing the triangle inequalities along the chain. -/
theorem le_chainCost_of_triangle (d : X → X → ℝ≥0∞)
    (htri : ∀ a b e, d a b ≤ d a e + d e b) (q : X) (mid : List X) :
    ∀ p, d p q ≤ chainCost d p mid q := by
  induction mid with
  | nil => intro p; simp
  | cons x xs ih =>
      intro p
      calc d p q ≤ d p x + d x q := htri p q x
        _ ≤ d p x + chainCost d x xs q := add_le_add (le_refl (d p x)) (ih x)
        _ = chainCost d p (x :: xs) q := by rw [chainCost_cons]

/-- **Universal property (maximality).** `chainDist c` is the *greatest* triangle-law
cost dominated by `c`: any `d` that satisfies the triangle inequality and is
pointwise ≤ `c` is pointwise ≤ `chainDist c`. With `chainDist_le_cost`, this says
`chainDist c` is the largest pseudometric-like cost below `c`. -/
theorem le_chainDist (c d : X → X → ℝ≥0∞)
    (htri : ∀ a b e, d a b ≤ d a e + d e b)
    (hdom : ∀ a b, d a b ≤ c a b) (p q : X) :
    d p q ≤ chainDist c p q := by
  refine le_iInf fun mid => ?_
  calc d p q ≤ chainCost d p mid q := le_chainCost_of_triangle d htri q mid p
    _ ≤ chainCost c p mid q := chainCost_mono_cost d c hdom q mid p

-- ============================================================
-- Part VII: The vanishing criterion (abstract non-hyperbolicity)
-- ============================================================

/-- **Vanishing criterion.** If `p` and `q` can be joined by chains of arbitrarily
small total cost, then the chain pseudometric between them is `0`. This is the
order-theoretic core of non-hyperbolicity (e.g. `d_ℂ ≡ 0` via affine maps). -/
theorem chainDist_eq_zero_of_forall (c : X → X → ℝ≥0∞) (p q : X)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ mid : List X, chainCost c p mid q ≤ ε) :
    chainDist c p q = 0 := by
  refine le_antisymm ?_ (zero_le _)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨mid, hmid⟩ := h (ε : ℝ≥0∞) (by exact_mod_cast hε)
  calc chainDist c p q ≤ chainCost c p mid q := chainDist_le c p q mid
    _ ≤ (ε : ℝ≥0∞) := hmid
    _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm

/-- If the atomic cost between `p` and `q` is already `0`, so is the chain
pseudometric. -/
theorem chainDist_eq_zero_of_cost_zero (c : X → X → ℝ≥0∞) (p q : X) (h : c p q = 0) :
    chainDist c p q = 0 :=
  le_antisymm (by simpa [h] using chainDist_le_cost c p q) (zero_le _)

/-- A one-vertex bridge of zero cost forces the chain pseudometric to vanish:
if `c p r = 0` and `c r q = 0`, then `chainDist c p q = 0`. -/
theorem chainDist_eq_zero_of_bridge (c : X → X → ℝ≥0∞) (p r q : X)
    (h1 : c p r = 0) (h2 : c r q = 0) : chainDist c p q = 0 := by
  refine le_antisymm ?_ (zero_le _)
  calc chainDist c p q ≤ chainCost c p [r] q := chainDist_le c p q [r]
    _ = c p r + c r q := by simp [chainCost]
    _ = 0 := by simp [h1, h2]

/-
## Summary

Building on the abstract Kobayashi chain pseudometric of `Hilbert22OQ01OQ03.lean`,
this file adds, in pure `ℝ≥0∞` order theory (0 axioms, 0 sorries):

* `chainCost_mono_cost`  — the chain cost is monotone in the atomic cost.
* `chainDist_le_cost`    — `chainDist c ≤ c`.
* `le_chainCost_of_triangle`, `le_chainDist` — the **universal property**:
  `chainDist c` is the greatest triangle-law cost dominated by `c`.
* `chainDist_eq_zero_of_forall` and corollaries — the **vanishing criterion**, the
  abstract heart of non-hyperbolicity (`d_ℂ ≡ 0`).

Together with the parent file this completes the order-theoretic specification of
the Kobayashi pseudometric: it is a functorial `PseudoEMetricSpace`, it is the
largest pseudometric below the atomic cost, and it collapses precisely when cheap
chains exist. The remaining ingredients (the unit-disk Poincaré metric, Schwarz–Pick,
`d_𝔻 = ρ`, and Picard via the modular λ cover) are the genuinely analytic part and
stay open, absent from Mathlib.
-/

end Hilbert22OQ01OQ03
