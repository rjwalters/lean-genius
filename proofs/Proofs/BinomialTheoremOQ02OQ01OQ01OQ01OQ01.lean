/-
# Multinomial PMF Normalization (Proven)

## Open Question (slug: binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01)

The parent file `BinomialTheoremOQ02OQ01OQ01.lean` defines a `Composition`
structure (the support type for the multinomial PMF) and the value
`multinomialPMFVal s p n k`, then defers the normalization

  `∑ k : Composition α s n, multinomialPMFVal s p n k = 1`

to a `sorry` (line 102). This file proves the normalization by routing
through Mathlib's `Finset.sum_pow_eq_sum_piAntidiag` and the sibling
file's `CompositionFintype.sum_composition_eq_piAntidiag_sum` bridge.

## Strategy (S2 ACT-A)

The two `Composition` types — `BinomialTheoremOQ02OQ01OQ01.Composition`
in the parent and `CompositionFintype.Composition` in the sibling — are
structurally identical. We define a one-line `compositionTypeEquiv`
between them, transfer the sum, then apply two stable Mathlib lemmas:

  `sum_composition_eq_piAntidiag_sum` (sibling, line 145 of
  `BinomialTheoremOQ02OQ01OQ01OQ01.lean`):
    `∑ c : Composition α s n, f c.counts = ∑ k ∈ s.piAntidiag n, f k`

  `Finset.sum_pow_eq_sum_piAntidiag` (Mathlib v4.26.0,
  `Mathlib/Data/Nat/Choose/Multinomial.lean` line 301):
    `(∑ i ∈ s, f i) ^ n = ∑ k ∈ s.piAntidiag n, multinomial s k * ∏ i ∈ s, f i ^ k i`

The chain is: transfer the parent sum into the sibling sum via
`Fintype.sum_equiv compositionTypeEquiv`; apply
`sum_composition_eq_piAntidiag_sum` to land on a `piAntidiag` sum;
recognize this as the RHS of `sum_pow_eq_sum_piAntidiag` (in reverse);
fold via the hypothesis `∑ p i = 1` and `1 ^ n = 1`.

## Output

This file does NOT redefine `multinomialPMF` or `multinomialPMFVal`; it
exports a single named theorem `multinomialPMF_sum_eq_one_proved` that
discharges the parent's deferred normalization. Downstream consumers
can either (a) replace the parent's `sorry` by importing this file and
applying the proved theorem, or (b) keep using the parent's existential
`multinomialPMF` definition while citing this file as the proof witness.
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ01
import Proofs.BinomialTheoremOQ02OQ01OQ01OQ01

namespace BinomialTheoremOQ02OQ01OQ01

open Finset BigOperators
open scoped ENNReal

/-! ## Namespace bridge

The parent file's `Composition α s n` and the sibling file's
`CompositionFintype.Composition α s n` have identical fields
(`counts : α → ℕ`, `sum_eq : ∑ i ∈ s, counts i = n`, `counts_outside`).
Their distinct namespacing is purely a layering artefact — the sibling
keeps the bridge-to-`piAntidiag` machinery isolated from the gallery
PMF construction. We expose the trivial type equivalence here so the
two namespaces can share sums via `Fintype.sum_equiv`. -/

/-- Bridge: the parent's `Composition α s n` is canonically equivalent
to the sibling's `CompositionFintype.Composition α s n`. The forward
and inverse maps are the identity on the underlying record. -/
def compositionTypeEquiv (α : Type*) [DecidableEq α] (s : Finset α) (n : ℕ) :
    Composition α s n ≃ CompositionFintype.Composition α s n where
  toFun c := ⟨c.counts, c.sum_eq, c.counts_outside⟩
  invFun c := ⟨c.counts, c.sum_eq, c.counts_outside⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

/-! ## Main theorem -/

/-- **Normalization of the multinomial PMF (proven)**.

The sum `∑ k : Composition α s n, multinomialPMFVal s p n k` equals `1`
whenever `∑ i ∈ s, p i = 1`. This discharges the deferred sorry on
`BinomialTheoremOQ02OQ01OQ01.multinomialPMF_sum_eq_one`.

Proof outline:

  1. Transfer the sum via `compositionTypeEquiv` from
     `BinomialTheoremOQ02OQ01OQ01.Composition` to
     `CompositionFintype.Composition` (record-wise identity, hence
     the summand `multinomialPMFVal s p n` is preserved unchanged on
     the underlying `counts`).
  2. Apply `CompositionFintype.sum_composition_eq_piAntidiag_sum` to
     rewrite the `Composition`-indexed sum as a `piAntidiag`-indexed
     sum on the `counts`-shaped function.
  3. Apply `Finset.sum_pow_eq_sum_piAntidiag` in reverse to fold the
     `piAntidiag` sum into a power.
  4. Substitute `∑ i ∈ s, p i = 1` (hypothesis `hp`) and `(1 : ℝ≥0∞)^n
     = 1` to conclude. -/
theorem multinomialPMF_sum_eq_one_proved {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) :
    ∑ k : Composition α s n, multinomialPMFVal s p n k = 1 := by
  -- Step 1: transfer the Composition-indexed sum via compositionTypeEquiv.
  -- The summand on the RHS spells out `multinomialPMFVal` on the
  -- transported composition's `counts` field, which is `c.counts`
  -- (componentwise identity) — `rfl` matches because both sides
  -- reduce to the same product.
  rw [Fintype.sum_equiv (compositionTypeEquiv α s n)
        (fun c => multinomialPMFVal s p n c)
        (fun c => (Nat.multinomial s c.counts : ℝ≥0∞)
                    * ∏ i ∈ s, p i ^ c.counts i)
        (fun _ => rfl)]
  -- Step 2: use the sibling's bridge to land on a piAntidiag sum.
  rw [CompositionFintype.sum_composition_eq_piAntidiag_sum (M := ℝ≥0∞) s n
        (fun k => (Nat.multinomial s k : ℝ≥0∞) * ∏ i ∈ s, p i ^ k i)]
  -- Step 3: fold the piAntidiag sum into a power via Mathlib.
  rw [← Finset.sum_pow_eq_sum_piAntidiag s p n]
  -- Step 4: use the normalization hypothesis and 1^n = 1.
  rw [hp, one_pow]

end BinomialTheoremOQ02OQ01OQ01
