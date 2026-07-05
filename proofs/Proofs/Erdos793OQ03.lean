/-
# Erdős Problem #793 — OQ-03: the r-product primitive framework

Follow-up to Erdős Problem #793 (`Erdos793Problem.lean`), open question OQ-03:
*"Asymptotic constant for the r-product primitive-set counting function."*

The parent problem asks about `F(n)`, the maximum size of `A ⊆ {1,…,n}` in which no
element divides the product of **two** other distinct elements, and conjectures a
precise second-order asymptotic
`F(n) = π(n) + (C + o(1)) · n^{2/3} · (log n)^{-2}`.
The generalized function `F_r(n)` replaces "two" by `r`: no element may divide the
product of `r` other distinct elements.  Erdős's exponent `2/3` becomes `2/(r+1)`,
and OQ-03 asks whether `F_r(n) − π(n)`, suitably normalized, converges to a
constant `C_r`.

This file builds the **verified structural core** of that generalized framework —
the facts that hold for *every* `r`, independent of the (open) asymptotic constant:

* `conditionR_hereditary`      : the r-product condition passes to subsets;
* `primes_satisfy_conditionR`  : **any** finset of primes satisfies the condition,
  for every `r` (no size threshold needed) — the source of the trivial lower bound;
* `primePi_le_F_r`             : hence `F_r(n) ≥ π(n)` for all `r ≥ 0`
  (a *verified* lower bound; the parent only stated this axiomatically for `r = 2`);
* `conditionR_antitone`        : if `r < |A|`, the condition for `r` implies it for
  every smaller `r'` — the conditions form a descending chain;
* `conditionR_one_iff_primitive`      : the `r = 1` case is exactly the classical
  primitive-set (divisibility-antichain) condition;
* `conditionR_two_iff_noDividesProduct` : the `r = 2` case is exactly the parent's
  `noDividesProduct`, so `F_r(·,2)` faithfully generalizes `F`;
* `secondaryTermR_nonneg`      : the secondary term `F_r(n) − π(n)` is `≥ 0`,
  so any limiting constant `C_r` (should it exist) is nonnegative.

The genuinely open question — existence of the asymptotic constant — is isolated as
the *unproven* proposition `erdos793ConstantConjectureR`; it is **stated, not
assumed**.  Every theorem in this file is axiom-free (0 sorries, 0 `axiom`s).
-/

import Mathlib
import Proofs.Erdos793Problem

namespace Erdos793RProduct

open Finset

/-! ## Heredity

The r-product condition is preserved under taking subsets: a smaller ground set has
fewer products to avoid.  This is the reason `F_r` is well-defined as a maximum over
all valid subsets. -/

/-- The r-product condition passes to subsets. -/
theorem conditionR_hereditary {A B : Finset ℕ} (hBA : B ⊆ A) {r : ℕ}
    (hA : satisfiesConditionR A r) : satisfiesConditionR B r := by
  intro a ha C hCB hCcard haC
  exact hA a (hBA ha) C (hCB.trans hBA) hCcard haC

/-! ## Primes satisfy the condition for every `r`

A prime `p` can divide a product of distinct primes only by *being* one of them.
Hence any finset all of whose elements are prime satisfies the r-product condition,
with **no** lower size threshold on the primes (contrast the parent file, which
imposed `p > n^{2/3}` and only handled `r = 2`).  This is the structural source of
the trivial lower bound `F_r(n) ≥ π(n)`. -/

/-- Any finset of primes satisfies the r-product condition, for every `r`. -/
theorem primes_satisfy_conditionR (A : Finset ℕ) (hA : ∀ p ∈ A, Nat.Prime p)
    (r : ℕ) : satisfiesConditionR A r := by
  intro a ha B hBA hBcard haB hdvd
  have hpa : Nat.Prime a := hA a ha
  -- a ∣ ∏_{b ∈ B} b  ⟹  ∃ b ∈ B, a ∣ b
  obtain ⟨b, hbB, hab⟩ := (hpa.prime.dvd_finset_prod_iff id).mp hdvd
  have hpb : Nat.Prime b := hA b (hBA hbB)
  -- a ∣ b with both prime forces a = b, contradicting a ∉ B ∋ b
  have hEq : a = b := (Nat.prime_dvd_prime_iff_eq hpa hpb).mp hab
  exact haB (hEq ▸ hbB)

/-- **Verified lower bound.** The primes in `[1,n]` form a valid configuration, so
`F_r(n) ≥ π(n)` for every `r`. -/
theorem primePi_le_F_r (n r : ℕ) : primePi n ≤ F_r n r := by
  -- The set of primes ≤ n.
  set P : Finset ℕ := (Finset.Icc 1 n).filter Nat.Prime with hP
  have hPsub : P ⊆ Icc_nat n := by
    intro x hx; exact (Finset.mem_filter.mp hx).1
  have hPcond : satisfiesConditionR P r :=
    primes_satisfy_conditionR P (fun p hp => (Finset.mem_filter.mp hp).2) r
  have hPcard : P.card = primePi n := rfl
  have hmem : primePi n ∈
      { k : ℕ | ∃ A : Finset ℕ, A ⊆ Icc_nat n ∧ satisfiesConditionR A r ∧ A.card = k } :=
    ⟨P, hPsub, hPcond, hPcard⟩
  -- The value set is bounded above by n = |Icc_nat n|.
  have hbdd : BddAbove
      { k : ℕ | ∃ A : Finset ℕ, A ⊆ Icc_nat n ∧ satisfiesConditionR A r ∧ A.card = k } := by
    refine ⟨n, ?_⟩
    rintro k ⟨A, hAsub, -, rfl⟩
    calc A.card ≤ (Icc_nat n).card := Finset.card_le_card hAsub
      _ = n := by simp [Icc_nat, Nat.card_Icc]
  unfold F_r
  exact le_csSup hbdd hmem

/-! ## The conditions form a descending chain in `r`

If no element divides a product of `r` others, then (provided the ground set is big
enough to pad a short product up to length `r`) no element divides a product of
fewer others either: a short divisible product extends to a long divisible product.
Thus `satisfiesConditionR A r` is *stronger* for larger `r`. -/

/-- Downward monotonicity in `r`: on a ground set of size `> r`, the r-product
condition implies the `r'`-product condition for every `r' ≤ r`.  (The size bound
`r < |A|` is genuinely needed: for `|A| ≤ r` the r-product condition is vacuous.) -/
theorem conditionR_antitone {A : Finset ℕ} {r r' : ℕ}
    (hrr : r' ≤ r) (hcard : r < A.card)
    (hA : satisfiesConditionR A r) : satisfiesConditionR A r' := by
  intro a ha B hBA hBcard haB hdvd
  -- B lives in A \ {a}
  have hBsub' : B ⊆ A \ {a} := by
    intro x hx
    rw [Finset.mem_sdiff]
    exact ⟨hBA hx, by simp only [Finset.mem_singleton]; rintro rfl; exact haB hx⟩
  -- |A \ {a}| = |A| - 1
  have hAa_card : (A \ {a}).card = A.card - 1 := by
    rw [← Finset.erase_eq, Finset.card_erase_of_mem ha]
  -- there is room to pick `r - r'` fresh elements of `A \ {a}` avoiding `B`
  have hDroom : r - r' ≤ ((A \ {a}) \ B).card := by
    rw [Finset.card_sdiff_of_subset hBsub', hAa_card, hBcard]; omega
  obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hDroom
  have hdisj : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro x hxD hxB
    exact (Finset.mem_sdiff.mp (hDsub hxD)).2 hxB
  -- pad B up to a set C of size r inside A \ {a}
  set C : Finset ℕ := B ∪ D with hC
  have hBC : B ⊆ C := Finset.subset_union_left
  have hCsub : C ⊆ A \ {a} :=
    Finset.union_subset hBsub' (hDsub.trans (Finset.sdiff_subset))
  have hCcard : C.card = r := by
    rw [hC, Finset.card_union_of_disjoint hdisj.symm, hBcard, hDcard]; omega
  have hCA : C ⊆ A := hCsub.trans (Finset.sdiff_subset)
  have haC : a ∉ C := by
    intro h
    have h2 := hCsub h
    rw [Finset.mem_sdiff] at h2
    exact h2.2 (Finset.mem_singleton_self a)
  -- the short divisible product extends to a long one
  have hdvdC : a ∣ C.prod id :=
    hdvd.trans (Finset.prod_dvd_prod_of_subset B C id hBC)
  exact hA a ha C hCA hCcard haC hdvdC

/-! ## Endpoints of the framework

The `r = 1` and `r = 2` cases identify the generalized condition with familiar
notions, confirming that `F_r` genuinely extends the classical primitive-set counting
function (`r = 1`) and the parent problem's `F` (`r = 2`). -/

/-- The `r = 1` condition is exactly the classical primitive-set condition: no element
divides another. -/
theorem conditionR_one_iff_primitive (A : Finset ℕ) :
    satisfiesConditionR A 1 ↔ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a ∣ b) := by
  constructor
  · intro h a ha b hb hab
    have hsub : ({b} : Finset ℕ) ⊆ A := by simpa using hb
    have hnotmem : a ∉ ({b} : Finset ℕ) := by simp [hab]
    have := h a ha {b} hsub (by simp) hnotmem
    simpa using this
  · intro h a ha B hBA hBcard haB
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hBcard
    have hbA : b ∈ A := hBA (Finset.mem_singleton_self b)
    have hab : a ≠ b := fun heq => haB (heq ▸ Finset.mem_singleton_self b)
    simpa using h a ha b hbA hab

/-- The `r = 2` condition is exactly the parent file's `noDividesProduct`: no element
divides the product of two *distinct* others. -/
theorem conditionR_two_iff_noDividesProduct (A : Finset ℕ) :
    satisfiesConditionR A 2 ↔ noDividesProduct A := by
  constructor
  · intro h a ha b hb c hc hab hac hbc hdvd
    have hsub : ({b, c} : Finset ℕ) ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hb
      · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hc
    have hcard : ({b, c} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    have hnotmem : a ∉ ({b, c} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hab, hac⟩
    have hprod : ({b, c} : Finset ℕ).prod id = b * c := by
      simp [Finset.prod_pair hbc]
    exact h a ha {b, c} hsub hcard hnotmem (hprod ▸ hdvd)
  · intro h a ha B hBA hBcard haB hdvd
    obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp hBcard
    have hbA : b ∈ A := hBA (by simp)
    have hcA : c ∈ A := hBA (by simp)
    have hab : a ≠ b := fun heq => haB (heq ▸ by simp)
    have hac : a ≠ c := fun heq => haB (heq ▸ by simp)
    have hprod : ({b, c} : Finset ℕ).prod id = b * c := by simp [Finset.prod_pair hbc]
    exact h a ha b hbA c hcA hab hac hbc (hprod ▸ hdvd)

/-! ## The open asymptotic constant (OQ-03)

Everything below is the *statement* of the open problem, together with the one sign
fact we can verify unconditionally.  Nothing here is asserted true. -/

/-- Secondary term `F_r(n) − π(n)`: the number of extra elements beyond the primes. -/
noncomputable def secondaryTermR (n r : ℕ) : ℝ := (F_r n r : ℝ) - primePi n

/-- Secondary term normalized by the conjectured order `n^{2/(r+1)}·(log n)^{-2}`. -/
noncomputable def normalizedSecondaryR (n r : ℕ) : ℝ :=
  secondaryTermR n r / ((n : ℝ) ^ ((2 : ℝ) / (r + 1)) * (Real.log n) ^ (-2 : ℝ))

/-- **OQ-03 (open).** For each `r`, does the normalized secondary term converge to a
constant `C_r`?  Stated as a proposition; deliberately not proved or assumed. -/
def erdos793ConstantConjectureR (r : ℕ) : Prop :=
  ∃ C : ℝ, Filter.Tendsto (fun n => normalizedSecondaryR n r) Filter.atTop (nhds C)

/-- **Verified constraint on the open constant.** The secondary term is nonnegative
(the primes alone already realize `π(n)`), so any limiting constant `C_r` must satisfy
`C_r ≥ 0`. -/
theorem secondaryTermR_nonneg (n r : ℕ) : 0 ≤ secondaryTermR n r := by
  have h : (primePi n : ℝ) ≤ (F_r n r : ℝ) := by exact_mod_cast primePi_le_F_r n r
  unfold secondaryTermR; linarith

#check @primePi_le_F_r
#check @conditionR_antitone
#check @conditionR_one_iff_primitive
#check @conditionR_two_iff_noDividesProduct
#check erdos793ConstantConjectureR

end Erdos793RProduct
