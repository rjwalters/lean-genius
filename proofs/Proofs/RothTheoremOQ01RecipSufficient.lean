import Proofs.RothTheoremOQ01Reciprocal

/-
# A reciprocal-mass sufficient condition for a 3-term progression (roth-theorem-oq-01)

The reciprocal file proves a *uniform* bound: there is one absolute constant
`recipBound = ∑'_k recipMajorant k` such that **every** 3-AP-free set `A ⊆ ℕ`
(with `0 ∉ A`) satisfies `∑'_{a∈A} 1/a ≤ recipBound`
(`RothTheoremOQ01Reciprocal.threeAPFree_tsum_reciprocal_le`).

Read the other way round, that uniform bound is a concrete **sufficient condition**
for the *existence* of a nontrivial three-term arithmetic progression:

> if a set carries more reciprocal mass than the universal constant
> (`recipBound < ∑'_{a∈A} 1/a`), it *cannot* be 3-AP-free, hence contains a
> nontrivial 3-AP `a, a+d, a+2d`.

This is the effective converse of `exists_universal_recip_bound`: rather than
merely asserting that a divergent reciprocal sum forces a progression
(`exists_nontrivial_threeAP_of_not_summable_reciprocal`), it gives an *explicit
numerical threshold* — exceeding the single Bloom–Sisask constant already
guarantees a progression, even for a convergent series.

Along the way we extract the reusable combinatorial unpacking
`exists_threeAP_of_not_threeAPFree` (turn the negation of `ThreeAPFree` into
concrete AP witnesses), lifted verbatim from the verified body of
`exists_nontrivial_threeAP_of_not_summable_reciprocal`.

Rests on exactly the single imported Bloom–Sisask assumption
`RothTheoremOQ02.rothNumberNat_bloom_sisask` (via the reciprocal file); introduces
**no new axiom**.
-/

open RothTheoremOQ01Reciprocal

namespace RothTheoremOQ01RecipSufficient

/-- **Unpack a non-3-AP-free set into explicit progression witnesses.**  If `A ⊆ ℕ`
is *not* 3-AP-free, then it contains a genuinely nontrivial three-term arithmetic
progression `a, a + d, a + 2d` with common difference `d > 0`.  (The middle term of
the witnessed non-progression is the average of the two ends; a case split on which
end is smaller orients the difference to be positive.) -/
theorem exists_threeAP_of_not_threeAPFree {A : Set ℕ} (hnot : ¬ ThreeAPFree A) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  unfold ThreeAPFree at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, hsum, hne⟩ := hnot
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `a < c`: progression starts at `a` with difference `b - a`.
    refine ⟨a, b - a, by omega, ha, ?_, ?_⟩
    · have h : a + (b - a) = b := by omega
      rw [h]; exact hb
    · have h : a + 2 * (b - a) = c := by omega
      rw [h]; exact hc
  · -- `c < a`: progression starts at `c` with difference `b - c`.
    refine ⟨c, b - c, by omega, hc, ?_, ?_⟩
    · have h : c + (b - c) = b := by omega
      rw [h]; exact hb
    · have h : c + 2 * (b - c) = a := by omega
      rw [h]; exact ha

/-- **Reciprocal mass above the universal constant forbids 3-AP-freeness.**  If a set
`A ⊆ ℕ` (with `0 ∉ A`) has reciprocal sum strictly exceeding the absolute Bloom–Sisask
constant `recipBound`, then `A` is not 3-AP-free.  Immediate from the uniform bound
`threeAPFree_tsum_reciprocal_le` (which caps every 3-AP-free set's reciprocal sum by
`recipBound`) by contraposition. -/
theorem not_threeAPFree_of_recipBound_lt_tsum {A : Set ℕ} (hA0 : 0 ∉ A)
    (hbig : recipBound < ∑' a : A, (1 : ℝ) / (a : ℝ)) :
    ¬ ThreeAPFree A := by
  intro hAP
  have hle : ∑' a : A, (1 : ℝ) / (a : ℝ) ≤ recipBound :=
    threeAPFree_tsum_reciprocal_le hAP hA0
  linarith

/-- **Reciprocal-mass threshold for a three-term progression.**  If a set `A ⊆ ℕ`
(with `0 ∉ A`) carries more reciprocal mass than the universal Bloom–Sisask constant,
`recipBound < ∑'_{a∈A} 1/a`, then `A` contains a nontrivial three-term arithmetic
progression `a, a + d, a + 2d` with `d > 0`.

This is an *effective* form of the `k = 3` Erdős consequence: it replaces the
qualitative hypothesis "the reciprocal sum diverges" with a single explicit numerical
threshold — exceeding the one absolute constant `recipBound` already forces a
progression, even for a convergent reciprocal series.  Rests on the single imported
Bloom–Sisask assumption; introduces no new axiom. -/
theorem exists_nontrivial_threeAP_of_recipBound_lt_tsum {A : Set ℕ} (hA0 : 0 ∉ A)
    (hbig : recipBound < ∑' a : A, (1 : ℝ) / (a : ℝ)) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
  exists_threeAP_of_not_threeAPFree (not_threeAPFree_of_recipBound_lt_tsum hA0 hbig)

/-- **A reciprocal-heavy set stays heavy inside any superset.**  If a finite `S ⊆ ℕ`
already carries more reciprocal mass than the absolute constant `recipBound`, then *any*
finite superset `S' ⊇ S` with `0 ∉ S'` contains a nontrivial three-term arithmetic
progression.  Enlarging a reciprocal certificate can only add nonnegative mass
(`Finset.sum_le_sum_of_subset_of_nonneg`), so `S'` also clears the threshold and
`exists_threeAP_of_finite_recip_sum_gt` applies.  This makes the finite reciprocal
criterion *stable under enlargement*: one may exhibit the over-threshold mass on a small,
convenient subset yet conclude the progression lives in the whole ambient set. -/
theorem exists_threeAP_of_subset_recip_sum_gt
    (S S' : Finset ℕ) (hsub : S ⊆ S') (hS'0 : 0 ∉ S')
    (hgt : recipBound < ∑ a ∈ S, (1 : ℝ) / (a : ℝ)) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ S' ∧ a + d ∈ S' ∧ a + 2 * d ∈ S' := by
  have hmono : ∑ a ∈ S, (1 : ℝ) / (a : ℝ) ≤ ∑ a ∈ S', (1 : ℝ) / (a : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  exact exists_threeAP_of_finite_recip_sum_gt S' hS'0 (lt_of_lt_of_le hgt hmono)

#check @exists_threeAP_of_not_threeAPFree
#check @not_threeAPFree_of_recipBound_lt_tsum
#check @exists_nontrivial_threeAP_of_recipBound_lt_tsum
#check @exists_threeAP_of_subset_recip_sum_gt

-- Axiom audit: rests on exactly the single imported Bloom–Sisask assumption
-- `RothTheoremOQ02.rothNumberNat_bloom_sisask` (via the reciprocal file); no new axiom.
#print axioms exists_nontrivial_threeAP_of_recipBound_lt_tsum

end RothTheoremOQ01RecipSufficient
