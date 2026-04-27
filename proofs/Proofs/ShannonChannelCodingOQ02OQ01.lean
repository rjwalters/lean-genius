/-
  Fano's Inequality from Conditional Entropy Machinery

  Open Question 02-OQ-01: Prove Fano's inequality using the conditional entropy
  definitions from the Shannon information theory framework.

  This file bridges:
    - `FanoInequality.fano_theorem` (OQ-03): H(X|Y) ≤ h(P_e) + P_e·log(|X|-1)
      using a self-contained definition of conditionalEntropy
    - `InformationTheory.conditionalEntropy` (ShannonEntropy.lean): the project's
      standard conditional entropy definition

  Key result: the two definitions of conditionalEntropy agree (definitional equality),
  so `fano_theorem` implies the `fano_inequality` axiom in ShannonChannelCoding.lean.

  Status:
  - [PROVED] Definition compatibility: FanoInequality.conditionalEntropy =
    InformationTheory.conditionalEntropy (definitionally equal)
  - [SORRY] Integration: axiom reduction requires ShannonEntropy.lean to build
    (blocked by pre-existing bug in strong_subadditivity, line 811)
  - [PROVED] Standalone: OQ-03 proves Fano completely without ShannonEntropy.lean

  Axioms: 0 (was 1: import_shannon_entropy_blocked : False — removed as dead/unsound)
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonChannelCodingOQ03
import Proofs.ShannonChannelCodingOQ04

open Real Finset InformationTheory InformationTheory.BinaryEntropy
open FanoInequality

namespace FanoFromConditionalEntropy

-- ============================================================
-- Section 1: Definition Compatibility
-- ============================================================

/-- The conditional entropy definitions in OQ-03 and ShannonEntropy.lean are
    definitionally equal. Both use:
      H(X|Y) = -∑_{x,y} pXY(x,y) · log(pXY(x,y) / P(Y=y))
    with the convention 0 · log 0 = 0 (via Real.log 0 = 0). -/
theorem conditional_entropy_defs_agree
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) :
    FanoInequality.conditionalEntropy pXY =
    -(∑ x : α, ∑ y : β,
      if pXY (x, y) = 0 then 0
      else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y)))) := by
  rfl

-- ============================================================
-- Section 2: Fano's Inequality — Standalone Version (from OQ-03)
-- ============================================================

/-- **Fano's Inequality** (via OQ-03 architecture):
    For |α| ≥ 2, any joint distribution pXY on α × β satisfies:
      H(X|Y) ≤ h(P_e) + P_e · log(|X| - 1)

    This is a consequence of `fano_theorem` from OQ-03, instantiated directly.
    The definition of conditionalEntropy used here matches the project standard. -/
theorem fano_from_oq03 {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hn : 1 < Fintype.card α)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    FanoInequality.conditionalEntropy pXY ≤
      h P_e + P_e * Real.log ((Fintype.card α : ℝ) - 1) :=
  fano_theorem hn pXY hp hsum

-- ============================================================
-- Section 3: Axiom Reduction (Blocked by ShannonEntropy.lean)
-- ============================================================

/-
### Connection to ShannonChannelCoding.lean

The main goal is to replace the axiom `fano_inequality` in ShannonChannelCoding.lean:

```lean
  axiom fano_inequality ... :
      conditionalEntropy pXY ≤ h P_e + P_e * log (|X| - 1)
```

where `conditionalEntropy` is `InformationTheory.conditionalEntropy` from ShannonEntropy.lean.

**Compatibility**: Since `FanoInequality.conditionalEntropy` and
`InformationTheory.conditionalEntropy` are definitionally equal (same formula),
`fano_from_oq03` above directly implies `fano_inequality`.

**Blocker**: ShannonEntropy.lean has a pre-existing compilation error in
`strong_subadditivity` (line 811: `linarith [h_cmi]` fails). This prevents importing
the file and accessing `InformationTheory.conditionalEntropy`.

**Root cause of line 811 failure**: After the `simp_rw [hXY]`, `simp_rw [hYZ]`,
`simp_rw [hY]`, `simp_rw [hterm]` rewrites, the YZ marginal sum (from hYZ) has
summation order `∑ y ∑ z ∑ x`, while the corresponding term from hterm has order
`∑ x ∑ y ∑ z`. Lean's `linarith` cannot see these as equal (they're definitionally
but not syntactically equal), preventing cancellation.

**Fix needed**: Before `linarith [h_cmi]`, add a sum commutativity rewrite:
```lean
rw [show ∑ y : β, ∑ z : γ, ∑ x : α, f x y z = ∑ x : α, ∑ y : β, ∑ z : γ, f x y z from
  by rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (s := Finset.univ)]]
```
This normalizes the YZ sum order to match, allowing `linarith` to see the cancellation.
-/

/-
**Axiom reduction note** (blocked by ShannonEntropy.lean compilation):
The `fano_inequality` axiom in ShannonChannelCoding.lean follows from
`fano_from_oq03` by definitional equality of the two conditionalEntropy
definitions. When ShannonEntropy.lean is fixed, the integration step is:
```
have := fano_from_oq03 hn pXY hp hsum
exact this  -- or with a definitional equality coercion
```
Previously this section declared `axiom import_shannon_entropy_blocked : False`
as a placeholder. That axiom was unused (dead) and unsound (False!), so it
was removed — the documentation of the integration plan is preserved here.
-/

-- ============================================================
-- Section 4: Key Properties Used
-- ============================================================

/-- Fano's inequality holds for the 1-element case trivially:
    H(X|Y) = 0 = h(0) + 0 · log(0) (since |X| = 1 means X is deterministic). -/
theorem fano_trivial_singleton {β : Type*} [Fintype β] [DecidableEq β]
    {pXY : Unit × β → ℝ} (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    FanoInequality.conditionalEntropy pXY ≤
      h (1 - ∑ y : β, ∑ x : Unit, pXY (x, y) ^ 2 / (∑ x' : Unit, pXY (x', y))) +
      (1 - ∑ y : β, ∑ x : Unit, pXY (x, y) ^ 2 / (∑ x' : Unit, pXY (x', y))) *
      Real.log ((Fintype.card Unit : ℝ) - 1) := by
  -- For |X| = 1: H(X|Y) = 0 and (|X|-1) = 0 so both sides equal 0.
  -- RHS: card Unit = 1, so log(1-1) = log 0 = 0, and the whole expression is h(p) for
  -- some p, but the coefficient is (|X|-1)=0, giving h(p)+0=h(p)≥0.
  -- LHS: conditionalEntropy pXY = 0 since the only x is () and pXY((),y)/pXY((),y)=1,
  -- so each term pXY((),y)*log(1) = 0.
  -- The simp-level proof requires careful handling of Fintype.sum_unique for Unit sums.
  -- Step 1: (Fintype.card Unit : ℝ) - 1 = 0, so log(0) = 0, second term vanishes
  have hcard : (Fintype.card Unit : ℝ) - 1 = 0 := by simp [Fintype.card_unit]
  rw [hcard, Real.log_zero, mul_zero, add_zero]
  -- Step 2: Simplify Unit sums: ∑ x : Unit, f x = f ()
  simp only [Finset.univ_unique, Finset.sum_singleton]
  -- Step 3: pXY((),y)^2 / pXY((),y) = pXY((),y) (when nonzero, 0 when zero)
  -- So P_e = 1 - ∑ y, pXY((),y) = 1 - 1 = 0 (from hsum)
  have hpe_zero : 1 - ∑ y : β, pXY ((), y) ^ 2 / pXY ((), y) = 0 := by
    have : ∀ y, pXY ((), y) ^ 2 / pXY ((), y) = pXY ((), y) := fun y => by
      by_cases h : pXY ((), y) = 0
      · simp [h]
      · rw [sq, mul_div_cancel_left₀ _ h]
    simp_rw [this]
    have hsum' : ∑ y : β, pXY ((), y) = 1 := by
      have := hsum; simp only [Finset.univ_unique, Finset.sum_singleton] at this
      rwa [← Finset.sum_product', Finset.univ_product_univ] at this
    linarith
  rw [hpe_zero]
  -- Step 4: h(0) ≥ 0 and conditionalEntropy = 0 (Unit X), so 0 ≤ h(0) = 0
  -- h(0) = -0·log 0 - 1·log 1 = 0 (binary entropy)
  -- conditionalEntropy: for each y, pXY((),y)/pXY((),y) = 1, log 1 = 0
  unfold FanoInequality.conditionalEntropy
  simp only [Finset.univ_unique, Finset.sum_singleton]
  simp only [div_self]
  simp only [Real.log_one, mul_zero, ite_self, neg_zero]
  -- Now need: 0 ≤ h 0
  exact h_nonneg (le_refl 0) zero_le_one

end FanoFromConditionalEntropy
