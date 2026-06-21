/-
  Erdős Problem #131 — Non-Dividing Sets
  Follow-up (oq-01-oq-01): an Erdős–Ginzburg–Ziv structural bound

  Source: https://erdosproblems.com/131
  Companion to: Proofs.Erdos131Problem  (def `Erdos131.IsNonDividing`)

  NOTE.  This file is deliberately SELF-CONTAINED: it re-states `IsNonDividing`
  (verbatim from the parent) rather than importing `Proofs.Erdos131Problem`,
  because the parent file does not currently compile against the pinned Mathlib
  (v4.26.0) — it has orphan docstrings before its `axiom` declarations and uses
  the pre-v4.26 `Finset.card_sdiff` argument order.  Decoupling keeps this
  contribution axiom-free and independently verifiable.  (The parent needs a
  separate mechanic repair.)

  ## What this file adds

  The parent file proves a *parity* constraint:

      `two_in_nondividing_bound` :  2 ∈ A → IsNonDividing A → A.card ≤ 3

  obtained by pigeonholing the elements of `A \ {2}` into the two parity
  classes mod 2 and using that two integers of equal parity have an even sum.

  That argument is exactly the prime case `p = 2` of the **Erdős–Ginzburg–Ziv
  theorem** (EGZ): among any `2p − 1` integers there are `p` whose sum is
  divisible by `p`.  Mathlib has EGZ for *every* modulus
  (`Int.erdos_ginzburg_ziv`), so the parity bound generalises verbatim to an
  arbitrary element of the set:

      **If `a ∈ A`, `a ≥ 2`, and `A` is non-dividing, then `A.card ≤ 2a − 1`.**

  Mechanism.  If `|A| ≥ 2a` then `|A \ {a}| ≥ 2a − 1`, so by EGZ (with modulus
  `n = a`, applied to the integer-valued sequence `i ↦ (i : ℤ)` on `A \ {a}`)
  there is an `a`-element subset `t ⊆ A \ {a}` with `a ∣ ∑_{i ∈ t} i`.  Since
  `a ≥ 2`, that subset has `≥ 2` elements and witnesses a violation of the
  non-dividing property at `a`.

  This is a genuine *structural upper bound* for `F(N)`: the smallest element of
  a non-dividing set controls its size (`nondividing_card_le_two_min` below).
  It subsumes the parent's `a = 2` parity result, which it recovers as a
  one-line corollary, and is sharp at `a = 2` (`{2,4,5}` is non-dividing,
  contains `2`, and has `card = 3 = 2·2 − 1`).

  All results are unconditional and axiom-free: EGZ is a fully proved Mathlib
  theorem (a corollary of Chevalley–Warning).
-/

import Mathlib

namespace Erdos131EGZ

open Finset

/-- A set `A` is *non-dividing* if no `a ∈ A` divides the sum of any subset of
`A \ {a}` of size `≥ 2`.  (Verbatim copy of `Erdos131.IsNonDividing` from the
parent file `Proofs.Erdos131Problem`, lines 45–49.) -/
def IsNonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.card ≥ 2 →
    ¬(a ∣ S.sum id)

/-- **Erdős–Ginzburg–Ziv structural bound for non-dividing sets.**

If `a ∈ A` with `a ≥ 2` and `A` is non-dividing, then `A.card ≤ 2a − 1`.

The proof applies the Erdős–Ginzburg–Ziv theorem with modulus `n = a` to the
integer-cast sequence on `A.erase a`: a non-dividing set with `≥ 2a` elements
would yield an `a`-element subset of `A \ {a}` (hence of size `≥ 2`) whose sum
is divisible by `a`, contradicting `IsNonDividing`. -/
theorem egz_nondividing_card_bound (A : Finset ℕ) (a : ℕ)
    (ha : a ∈ A) (ha2 : 2 ≤ a) (hND : IsNonDividing A) :
    A.card ≤ 2 * a - 1 := by
  by_contra hcon
  push_neg at hcon
  -- `A.erase a` is large enough to feed EGZ at modulus `a`.
  have herase : 2 * a - 1 ≤ (A.erase a).card := by
    rw [Finset.card_erase_of_mem ha]; omega
  -- EGZ: an `a`-element subset of `A \ {a}` with sum divisible by `a` (over ℤ).
  obtain ⟨t, hts, htcard, htdvd⟩ :=
    Int.erdos_ginzburg_ziv (s := A.erase a) (n := a) (fun i => (i : ℤ)) herase
  -- Transport the divisibility back to ℕ.
  have hdvdNat : a ∣ t.sum id := by
    have h2 : (a : ℤ) ∣ ((t.sum id : ℕ) : ℤ) := by
      push_cast
      simpa using htdvd
    exact_mod_cast h2
  -- The subset has `≥ 2` elements, so it violates non-dividing at `a`.
  have htge : 2 ≤ t.card := by rw [htcard]; exact ha2
  exact hND a ha t hts htge hdvdNat

/-- **Smallest-element bound.** A non-dividing set all of whose elements are
`≥ 2` has at most `2·(min) − 1` elements, where `min` is its least element.

Applying `egz_nondividing_card_bound` at the *smallest* element gives the
tightest bound, so the minimum of a non-dividing set controls its size. -/
theorem nondividing_card_le_two_min (A : Finset ℕ) (hA : A.Nonempty)
    (hmin : ∀ x ∈ A, 2 ≤ x) (hND : IsNonDividing A) :
    A.card ≤ 2 * A.min' hA - 1 := by
  have hmem := A.min'_mem hA
  exact egz_nondividing_card_bound A (A.min' hA) hmem (hmin _ hmem) hND

/-- **Recovers the parent parity bound** `two_in_nondividing_bound` as the
`a = 2` special case of the EGZ bound: `2 ∈ A` forces `A.card ≤ 3 = 2·2 − 1`. -/
theorem two_in_card_le_three (A : Finset ℕ) (h2 : 2 ∈ A) (hND : IsNonDividing A) :
    A.card ≤ 3 := by
  have h := egz_nondividing_card_bound A 2 h2 (le_refl 2) hND
  omega

/-- **Contrapositive / certification form.** If a candidate set has more than
`2a − 1` elements for some `a ∈ A` with `a ≥ 2`, it cannot be non-dividing.
Useful as a fast structural filter when searching for non-dividing sets. -/
theorem not_nondividing_of_card_gt (A : Finset ℕ) (a : ℕ)
    (ha : a ∈ A) (ha2 : 2 ≤ a) (hcard : 2 * a - 1 < A.card) :
    ¬ IsNonDividing A := by
  intro hND
  exact absurd (egz_nondividing_card_bound A a ha ha2 hND) (by omega)

/- ## Sharpness at `a = 2` -/

/-- Helper (from the parent): a subset of size `≥ 2` inside a set of size `≤ 2`
equals it. -/
private lemma finset_eq_of_subset_of_card_two {S T : Finset ℕ}
    (hsub : S ⊆ T) (hS : S.card ≥ 2) (hT : T.card ≤ 2) : S = T :=
  Finset.eq_of_subset_of_card_le hsub (by omega)

/-- `{2, 4, 5}` is non-dividing (`2 ∤ 9`, `4 ∤ 7`, `5 ∤ 6`).  Re-proved here to
keep the file self-contained; this is `two_four_five_nondividing` in the parent. -/
theorem two_four_five_nondividing : IsNonDividing ({2, 4, 5} : Finset ℕ) := by
  intro a ha S hS hCard hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · have hle : (({2, 4, 5} : Finset ℕ).erase 2).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 2 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)
  · have hle : (({2, 4, 5} : Finset ℕ).erase 4).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 4 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)
  · have hle : (({2, 4, 5} : Finset ℕ).erase 5).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 5 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)

/-- The EGZ bound is **sharp at `a = 2`**: `{2,4,5}` is non-dividing, contains
`2`, and has `card = 3 = 2·2 − 1`, meeting `two_in_card_le_three` with equality. -/
theorem egz_bound_sharp_at_two :
    (2 : ℕ) ∈ ({2, 4, 5} : Finset ℕ) ∧
    IsNonDividing ({2, 4, 5} : Finset ℕ) ∧
    ({2, 4, 5} : Finset ℕ).card = 2 * 2 - 1 :=
  ⟨by decide, two_four_five_nondividing, by decide⟩

end Erdos131EGZ
