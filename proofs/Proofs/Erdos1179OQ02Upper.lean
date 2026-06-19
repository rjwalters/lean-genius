/-
Proof: Deterministic upper-bound companion for Erdős #1179 oq-02.
Date: 2026-06-15 (S3)
Research: erdos-1179-oq-02 (researcher-2)

oq-02 asks whether the Erdős–Hall `(1+o(1))` multiplicative factor can be
sharpened to a bounded additive error, `g_ε(N) ≤ log₂ N + O_ε(1)`.  The sibling
file `Erdos1179OQ02.lean` (PR #24551) proved the matching lower bound
`g_ε(N) ≥ log₂ N` at the per-subset level (`clog_le_card_of_epsUniform`).

This file supplies the **upper side at its sharpest**: whenever a subset `A`
gives every group element a *unique* subset-sum representation
(`reprCount A g = 1` for all `g` — e.g. a basis of an elementary abelian
2-group `(ZMod 2)^m`, where `N = 2^m`), `A` is **exactly `0`-uniform** and its
size is **exactly** the lower bound `⌈log₂ N⌉`.  Hence on this infinite family
of groups the conjectured additive sharpening holds with constant `0`, and
*deterministically* (not merely with high probability):

    g_0(N) = log₂ N      for  N = 2^m.

This does not resolve oq-02 (which concerns general/random `G` and a w.h.p.
guarantee), but it pins the optimum on a natural family and certifies the
additive constant cannot be forced positive in general.

Numerical companion: `verify_unique_repr_upper.py` checks reprCount ≡ 1,
0-uniformity, and `|A| = clog₂ N` for bases of `(ZMod 2)^m`, `m = 1..7`.

NOTE: registered in `Proofs.lean` (researcher-1, S4); build-verified by
researcher-2 (2026-06-19, S11) after repairing two latent defects the original
audit missed (the file had never compiled under the Docker blackout): a literal
comment-terminator token inside this docstring that prematurely closed the block
comment, and a stale `Eq.symm` in `card_eq_two_pow_of_unique_repr` whose
orientation no longer matched Mathlib's `Finset.card_univ` normalization.
Confirmed green via `Build completed successfully (7746 jobs)`.
Mathlib bearer name-checked @ pinned rev 2df2f01:
`Nat.clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x`  (Data/Nat/Log.lean:453).
-/

import Proofs.Erdos1179Problem
import Mathlib

namespace Erdos1179

open Finset

/-- A **unique-representation set** forces the group order to be exactly
`2 ^ |A|`: if every `g` has exactly one subset-sum representation, the counts
sum to both `N` (one per element) and `2 ^ |A|` (`total_reprCount`). -/
theorem card_eq_two_pow_of_unique_repr {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (h : ∀ g, reprCount A g = 1) :
    Fintype.card G = 2 ^ A.card := by
  have hsum : (∑ g : G, reprCount A g) = 2 ^ A.card := total_reprCount A
  rw [Finset.sum_congr rfl (fun g _ => h g)] at hsum
  simpa [Finset.card_univ] using hsum

/-- A unique-representation set is **exactly `0`-uniform**: each count equals the
expected count `μ = 2^|A| / N = 1`. -/
theorem epsUniform_zero_of_unique_repr {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (h : ∀ g, reprCount A g = 1) :
    IsEpsUniform A 0 := by
  have hcard : Fintype.card G = 2 ^ A.card := card_eq_two_pow_of_unique_repr A h
  have hμ : expectedReprCount A.card (Fintype.card G) = 1 := by
    have h2 : (Fintype.card G : ℝ) = (2 : ℝ) ^ A.card := by rw [hcard]; push_cast; ring
    unfold expectedReprCount
    rw [h2, div_self (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
  intro g
  rw [h g, hμ]
  norm_num

/-- **Optimality / additive-constant-zero on the unique-representation family.**
A set giving every element a unique representation has size *exactly* the lower
bound `⌈log₂ N⌉ = Nat.clog 2 N`.  Together with `clog_le_card_of_epsUniform`
(the lower bound), this is the equality `g_0(N) = log₂ N` for every group order
`N = 2^m` admitting such a set (e.g. `(ZMod 2)^m` via a basis). -/
theorem unique_repr_card_eq_clog {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (h : ∀ g, reprCount A g = 1) :
    A.card = Nat.clog 2 (Fintype.card G) := by
  rw [card_eq_two_pow_of_unique_repr A h, Nat.clog_pow 2 A.card (by norm_num)]

end Erdos1179
