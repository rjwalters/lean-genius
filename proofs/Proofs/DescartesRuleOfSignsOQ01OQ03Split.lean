/-
# Sharp Descartes for split polynomials with positive roots (OQ-01-OQ-03, § 13)

Companion to `DescartesRuleOfSignsOQ01OQ03`, answering that entry's open question 3:
the axiom-free linear validation (`linearReduction` on `X − c`, `c > 0`) extends to
**arbitrary products of positive linear factors**.  For any multiset `s` of positive
reals the monic polynomial

  `P = ∏_{c ∈ s} (X − c)`

satisfies, with no axioms whatsoever:

  * `natDegree P = card s`,
  * `#{positive roots of P} = card s`   (its roots are exactly `s`, all positive),
  * `V(P) = card s`                      (its coefficients strictly alternate in sign).

Hence Descartes' rule holds with **equality and zero even-defect** — the tightest
possible case — for this whole family.  The proof runs through Vieta's formula
(`Multiset.prod_X_sub_C_coeff`): the `k`-th coefficient is `(−1)^{n−k} · e_{n−k}(s)`,
and every elementary symmetric function of a positive multiset is positive
(`esymm_pos_of_pos`), so consecutive coefficients have strictly opposite signs.
Working with a *multiset* of roots subsumes multiplicities as well as the distinct-root
case named in the open question, and generalises the concrete degree-2/3 witnesses
`X² − 3X + 2 = (X−1)(X−2)` and `X³ − X² + X − 1 = (X−1)(X²+1)` already in the base file.
-/

import Proofs.DescartesRuleOfSignsOQ01OQ03
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

namespace DescartesRuleOfSignsOQ01OQ03

open Polynomial
open DescartesRuleOfSigns (countPositiveRoots signChangesInCoeffs)

section SplitPositive

variable {s : Multiset ℝ}

/-- Sum of a non-empty multiset of positive reals is positive. -/
private theorem msum_pos :
    ∀ (M : Multiset ℝ), M ≠ 0 → (∀ x ∈ M, 0 < x) → 0 < M.sum := by
  intro M
  induction M using Multiset.induction_on with
  | empty => intro hne _; exact absurd rfl hne
  | cons a t _ =>
    intro _ hpos
    rw [Multiset.sum_cons]
    have ha : 0 < a := hpos a (Multiset.mem_cons_self a t)
    have hnn : 0 ≤ t.sum :=
      Multiset.sum_nonneg (fun x hx => le_of_lt (hpos x (Multiset.mem_cons_of_mem hx)))
    linarith

/-- **Positivity of elementary symmetric functions of a positive multiset.**  Every
`e_n(s)` with `n ≤ card s` is positive: the defining sum ranges over the non-empty
collection of size-`n` sub-multisets of `s`, each of which has a strictly positive
product (`Multiset.prod_pos`). -/
theorem esymm_pos_of_pos (hs : ∀ x ∈ s, 0 < x) {n : ℕ}
    (hn : n ≤ Multiset.card s) : 0 < s.esymm n := by
  rw [Multiset.esymm]
  refine msum_pos _ ?_ ?_
  · -- the multiset of subset-products is non-empty (there are `C(card s, n) > 0` subsets)
    rw [← Multiset.card_pos, Multiset.card_map, Multiset.card_powersetCard]
    exact Nat.choose_pos hn
  · -- every subset-product is positive
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [Multiset.mem_powersetCard] at ht
    exact Multiset.prod_pos (fun z hz => hs z (Multiset.mem_of_le ht.1 hz))

/-- **The coefficient sign-change count of a positive split product is its degree.**
For `P = ∏_{c∈s}(X − c)` with every `c ∈ s` positive, the coefficients strictly
alternate in sign and never vanish (Vieta: `coeff k = (−1)^{n−k} e_{n−k}(s)` with
`e_{n−k}(s) > 0`), so `V(P) = card s`.  Axiom-free. -/
theorem signChangesInCoeffs_prod_X_sub_C_of_pos (hs : ∀ x ∈ s, 0 < x) :
    signChangesInCoeffs (s.map fun a => X - C a).prod = Multiset.card s := by
  set P : ℝ[X] := (s.map fun a => X - C a).prod with hP
  have hdeg : P.natDegree = Multiset.card s := by
    rw [hP]; exact natDegree_multiset_prod_X_sub_C_eq_card s
  have hmonic : P.Monic := by
    rw [hP]; exact monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hPne : P ≠ 0 := hmonic.ne_zero
  have hcoeff : ∀ k, k ≤ Multiset.card s →
      P.coeff k = (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) := by
    intro k hk; rw [hP]; exact Multiset.prod_X_sub_C_coeff s hk
  rw [signChangesInCoeffs_eq_natDegree_of_alternating hPne ?_ ?_, hdeg]
  · -- (nowhere zero) every coefficient up to the degree is `±e > 0`
    intro k hk
    rw [hdeg] at hk
    rw [hcoeff k hk]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ne_of_gt (esymm_pos_of_pos hs (Nat.sub_le _ _)))
  · -- (strict alternation) consecutive coefficients have opposite signs
    intro k hk
    rw [hdeg] at hk
    have hk0 : k ≤ Multiset.card s := le_of_lt hk
    have hk1 : k + 1 ≤ Multiset.card s := hk
    rw [hcoeff k hk0, hcoeff (k + 1) hk1]
    have hE1 : 0 < s.esymm (Multiset.card s - k) :=
      esymm_pos_of_pos hs (Nat.sub_le _ _)
    have hE2 : 0 < s.esymm (Multiset.card s - (k + 1)) :=
      esymm_pos_of_pos hs (Nat.sub_le _ _)
    have hsign : ((-1 : ℝ) ^ (Multiset.card s - k)) *
        ((-1 : ℝ) ^ (Multiset.card s - (k + 1))) = -1 := by
      rw [← pow_add]
      apply Odd.neg_one_pow
      have he : (Multiset.card s - k) + (Multiset.card s - (k + 1))
          = 2 * (Multiset.card s - (k + 1)) + 1 := by omega
      rw [he]; exact ⟨_, rfl⟩
    have hrw : ((-1 : ℝ) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k)) *
        ((-1) ^ (Multiset.card s - (k + 1)) * s.esymm (Multiset.card s - (k + 1)))
        = (((-1 : ℝ) ^ (Multiset.card s - k)) *
            ((-1) ^ (Multiset.card s - (k + 1)))) *
          (s.esymm (Multiset.card s - k) * s.esymm (Multiset.card s - (k + 1))) := by
      ring
    rw [hrw, hsign]
    have hprod : 0 < s.esymm (Multiset.card s - k) * s.esymm (Multiset.card s - (k + 1)) :=
      mul_pos hE1 hE2
    linarith

/-- **The positive-root count of a positive split product is its degree.**  The roots
of `∏_{c∈s}(X − c)` are exactly `s` (`roots_multiset_prod_X_sub_C`), all positive, so
none are filtered out.  Axiom-free. -/
theorem countPositiveRoots_prod_X_sub_C_of_pos (hs : ∀ x ∈ s, 0 < x) :
    countPositiveRoots (s.map fun a => X - C a).prod = Multiset.card s := by
  have hmonic : ((s.map fun a => X - C a).prod).Monic :=
    monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  unfold countPositiveRoots
  rw [if_neg hmonic.ne_zero, roots_multiset_prod_X_sub_C,
    Multiset.filter_eq_self.mpr (fun x hx => hs x hx)]

/-- **Sharp Descartes for split polynomials with positive roots (axiom-free).**
`#{positive roots of P} = V(P) = card s` for `P = ∏_{c∈s}(X − c)` with every root
positive: Descartes' rule of signs holds with *equality* and zero even-defect for the
whole family.  This is the unconditional, axiom-free instance of the bridge's
conclusion requested by open question 3, upgrading the single linear witness
`linearReduction` to all products of positive linear factors. -/
theorem descartes_sharp_prod_X_sub_C_of_pos (hs : ∀ x ∈ s, 0 < x) :
    countPositiveRoots (s.map fun a => X - C a).prod
      = signChangesInCoeffs (s.map fun a => X - C a).prod := by
  rw [countPositiveRoots_prod_X_sub_C_of_pos hs,
    signChangesInCoeffs_prod_X_sub_C_of_pos hs]

/-- The open question's exact phrasing over an indexing `Finset`: for a finite family
of positive reals `c : ι → ℝ`, the product `∏_{i∈t}(X − cᵢ)` of positive linear
factors realises Descartes' bound sharply.  (Distinctness of the `cᵢ`, the case the
question singles out, is *not* needed for the identity — the multiset engine above
handles repeated factors too.)  Axiom-free. -/
theorem descartes_sharp_finset_prod_X_sub_C_of_pos {ι : Type*} (t : Finset ι)
    (c : ι → ℝ) (hc : ∀ i ∈ t, 0 < c i) :
    countPositiveRoots (∏ i ∈ t, (X - C (c i)))
        = signChangesInCoeffs (∏ i ∈ t, (X - C (c i)))
      ∧ signChangesInCoeffs (∏ i ∈ t, (X - C (c i))) = t.card := by
  have hpos : ∀ x ∈ t.val.map c, 0 < x := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hc i hi
  have hset : (∏ i ∈ t, (X - C (c i))) = ((t.val.map c).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  refine ⟨?_, ?_⟩
  · rw [hset, descartes_sharp_prod_X_sub_C_of_pos hpos]
  · rw [hset, signChangesInCoeffs_prod_X_sub_C_of_pos hpos]
    exact Multiset.card_map c t.val

end SplitPositive

end DescartesRuleOfSignsOQ01OQ03
