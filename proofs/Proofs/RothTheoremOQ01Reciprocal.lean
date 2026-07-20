import Proofs.RothTheoremOQ01
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
# Erdős reciprocal-sum consequence of the Bloom–Sisask bound (roth-theorem-oq-01)

The genuine headline consequence of the Bloom–Sisask density theorem
`r₃(N) ≪ N / (log N)^{1+c}` is the resolution of the `k = 3` case of the
**Erdős conjecture on arithmetic progressions**:

> every 3-AP-free set `A ⊆ ℕ` has a *convergent* reciprocal sum `∑_{a ∈ A} 1/a < ∞`.

(Contrapositively: any `A` with `∑ 1/a = ∞` contains a nontrivial 3-term AP.)  The
qualitative Roth bound `r₃(N) = o(N)` is *not* strong enough for this — the reciprocal
sum needs a saving of a full power of `log`, exactly what Bloom–Sisask (2020) provides.

This file derives that statement from the gallery's `threeAPFree_card_le_blasi`
(the arbitrary-set form of the Bloom–Sisask bound, itself resting on the single imported
axiom `RothTheoremOQ02.rothNumberNat_bloom_sisask`).  **No new axiom** is introduced; the
main result `threeAPFree_summable_reciprocal` inherits exactly that one assumption.

## Method — dyadic partial summation

Partition `A` by the dyadic block index `k = ⌊log₂ a⌋`, so `a ∈ [2^k, 2^{k+1})`.  The
block `A ∩ [2^k, 2^{k+1})` is 3-AP-free with all elements `< 2^{k+1}`, so the density
bound gives at most `2^{k+1} / ((k+1)·log 2)^{1+c}` elements, each contributing `≤ 2^{-k}`.
Hence the block's reciprocal contribution is `≤ 2 / ((k+1)·log 2)^{1+c} =: recipMajorant k`,
and `∑_k recipMajorant k` converges because the exponent `1 + c > 1` (a `p`-series).
Uniform boundedness of the finite partial sums then yields summability.
-/

open Asymptotics Filter Topology Finset
open scoped BigOperators

namespace RothTheoremOQ01Reciprocal

open RothTheoremOQ01 RothTheoremOQ02

/-- The dyadic majorant `recipMajorant k = 2 / ((k+1)·log 2)^{1 + blasiConst}`.  This bounds
the reciprocal contribution of the `k`-th dyadic block of any 3-AP-free set, and is summable
because the exponent `1 + blasiConst > 1`. -/
noncomputable def recipMajorant (k : ℕ) : ℝ :=
  2 / (((k : ℝ) + 1) * Real.log 2) ^ (1 + RothTheoremOQ02.blasiConst)

/-- Positivity of the base `(k+1)·log 2` of the majorant. -/
theorem recipMajorant_base_pos (k : ℕ) : (0 : ℝ) < ((k : ℝ) + 1) * Real.log 2 :=
  mul_pos (by positivity) (Real.log_pos (by norm_num))

/-- The rpow denominator of the majorant is positive. -/
theorem recipMajorant_denom_pos (k : ℕ) :
    (0 : ℝ) < (((k : ℝ) + 1) * Real.log 2) ^ (1 + RothTheoremOQ02.blasiConst) :=
  Real.rpow_pos_of_pos (recipMajorant_base_pos k) _

/-- Nonnegativity of the majorant. -/
theorem recipMajorant_nonneg (k : ℕ) : 0 ≤ recipMajorant k := by
  unfold recipMajorant
  exact le_of_lt (div_pos (by norm_num) (recipMajorant_denom_pos k))

/-- **The dyadic majorant is summable** (`p`-series with `p = 1 + blasiConst > 1`). -/
theorem summable_recipMajorant : Summable recipMajorant := by
  have hp : (1 : ℝ) < 1 + RothTheoremOQ02.blasiConst := by
    have := RothTheoremOQ02.blasiConst_pos; linarith
  -- Base `p`-series `∑ 1/(n+1)^p` converges.
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + RothTheoremOQ02.blasiConst)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (1 + RothTheoremOQ02.blasiConst)).mpr hp
    have heq : (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 + RothTheoremOQ02.blasiConst))
        = (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + RothTheoremOQ02.blasiConst)) := by
      funext n; rw [abs_of_nonneg (by positivity)]
    rwa [heq] at h
  -- Rewrite the majorant into the separable constant × `p`-series form.
  have hrw : recipMajorant =
      fun k : ℕ => (2 / Real.log 2 ^ (1 + RothTheoremOQ02.blasiConst)) *
        (1 / ((k : ℝ) + 1) ^ (1 + RothTheoremOQ02.blasiConst)) := by
    funext k
    unfold recipMajorant
    rw [Real.mul_rpow (by positivity) (Real.log_nonneg (by norm_num))]
    ring
  rw [hrw]
  exact hbase.mul_left _

/-- **Per-block reciprocal bound.**  For any finite 3-AP-free `T` with `0 ∉ T`, the reciprocal
sum over the `k`-th dyadic fiber `{a ∈ T : ⌊log₂ a⌋ = k}` is at most `recipMajorant k`. -/
theorem fiber_sum_le (T : Finset ℕ) (hT : ThreeAPFree (T : Set ℕ)) (hT0 : 0 ∉ T) (k : ℕ) :
    ∑ a ∈ T.filter (fun a => Nat.log 2 a = k), (1 : ℝ) / a ≤ recipMajorant k := by
  classical
  set F := T.filter (fun a => Nat.log 2 a = k) with hF
  have hFsub : F ⊆ T := Finset.filter_subset _ _
  have hne : ∀ a ∈ F, a ≠ 0 := fun a ha h => hT0 (h ▸ hFsub ha)
  have hlog : ∀ a ∈ F, Nat.log 2 a = k := fun a ha => (Finset.mem_filter.mp ha).2
  -- Every fiber element lies in `[2^k, 2^{k+1})`.
  have hlow : ∀ a ∈ F, (2 : ℝ) ^ k ≤ (a : ℝ) := by
    intro a ha
    have h := Nat.pow_log_le_self 2 (hne a ha)
    rw [hlog a ha] at h
    calc (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (a : ℝ) := by exact_mod_cast h
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  -- Step 1: termwise `1/a ≤ 1/2^k`, hence sum `≤ card/2^k`.
  have hstep1 : ∑ a ∈ F, (1 : ℝ) / a ≤ (F.card : ℝ) * (1 / (2 : ℝ) ^ k) := by
    calc ∑ a ∈ F, (1 : ℝ) / a ≤ ∑ _a ∈ F, (1 / (2 : ℝ) ^ k) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          exact one_div_le_one_div_of_le h2k (hlow a ha)
      _ = (F.card : ℝ) * (1 / (2 : ℝ) ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hk : k = 0
  · -- k = 0: the fiber is contained in `{1}`.
    subst hk
    have hone : ∀ a ∈ F, a = 1 := by
      intro a ha
      have hlt : a < 2 ^ (Nat.log 2 a).succ := Nat.lt_pow_succ_log_self (by norm_num) a
      rw [hlog a ha] at hlt
      have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (hne a ha)
      simp only [Nat.succ_eq_add_one, Nat.zero_add, pow_one] at hlt
      omega
    have hle1 : ∑ a ∈ F, (1 : ℝ) / a ≤ 1 := by
      calc ∑ a ∈ F, (1 : ℝ) / a = ∑ a ∈ F, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun a ha => ?_); rw [hone a ha]; norm_num
        _ = (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 1 := by
            have : F.card ≤ 1 :=
              Finset.card_le_one.mpr (fun a ha b hb => by rw [hone a ha, hone b hb])
            exact_mod_cast this
    refine hle1.trans ?_
    have hpos : (0 : ℝ) < Real.log 2 ^ (1 + RothTheoremOQ02.blasiConst) :=
      Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hz : (0 : ℝ) ≤ 1 + RothTheoremOQ02.blasiConst := by
      have := RothTheoremOQ02.blasiConst_pos; linarith
    unfold recipMajorant
    rw [Nat.cast_zero, zero_add, one_mul, le_div_iff₀ hpos, one_mul]
    calc Real.log 2 ^ (1 + RothTheoremOQ02.blasiConst)
        ≤ 1 := Real.rpow_le_one (Real.log_nonneg (by norm_num)) hlog2le1 hz
      _ ≤ 2 := by norm_num
  · -- k ≥ 1: apply the density bound at `N = 2^{k+1} ≥ 3`.
    have hN3 : 3 ≤ 2 ^ (k + 1) := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsub : ∀ x ∈ F, x < 2 ^ (k + 1) := by
      intro x hx
      have hlt : x < 2 ^ (Nat.log 2 x).succ := Nat.lt_pow_succ_log_self (by norm_num) x
      rwa [hlog x hx, Nat.succ_eq_add_one] at hlt
    have hFAP : ThreeAPFree (F : Set ℕ) := ThreeAPFree.mono (Finset.coe_subset.mpr hFsub) hT
    have hdens := threeAPFree_card_le_blasi hFAP hN3 hsub
    -- Normalise the ℕ-cast numerator and the `log (2^{k+1})` denominator.
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add, Nat.cast_one] at hdens
    -- Combine card bound with `1/a ≤ 1/2^k`.
    have hDpos := recipMajorant_denom_pos k
    have h2kne : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h2k
    have hDne : (((k : ℝ) + 1) * Real.log 2) ^ (1 + RothTheoremOQ02.blasiConst) ≠ 0 := ne_of_gt hDpos
    calc ∑ a ∈ F, (1 : ℝ) / a
        ≤ (F.card : ℝ) * (1 / (2 : ℝ) ^ k) := hstep1
      _ ≤ ((2 : ℝ) ^ (k + 1) / (((k : ℝ) + 1) * Real.log 2) ^ (1 + RothTheoremOQ02.blasiConst)) *
            (1 / (2 : ℝ) ^ k) := by
            exact mul_le_mul_of_nonneg_right hdens (by positivity)
      _ = recipMajorant k := by
            unfold recipMajorant
            rw [pow_succ]
            field_simp

/-- **Uniform bound on finite reciprocal sums.**  For every finite 3-AP-free `T` (`0 ∉ T`),
`∑_{a ∈ T} 1/a ≤ ∑'_k recipMajorant k`, a bound independent of `T`. -/
theorem finite_recip_sum_le (T : Finset ℕ) (hT : ThreeAPFree (T : Set ℕ)) (hT0 : 0 ∉ T) :
    ∑ a ∈ T, (1 : ℝ) / a ≤ ∑' k, recipMajorant k := by
  classical
  have hmaps : ∀ a ∈ T, Nat.log 2 a ∈ T.image (Nat.log 2) :=
    fun a ha => Finset.mem_image_of_mem _ ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (1 : ℝ) / a)]
  calc ∑ k ∈ T.image (Nat.log 2), ∑ a ∈ T.filter (fun a => Nat.log 2 a = k), (1 : ℝ) / a
      ≤ ∑ k ∈ T.image (Nat.log 2), recipMajorant k :=
        Finset.sum_le_sum (fun k _ => fiber_sum_le T hT hT0 k)
    _ ≤ ∑' k, recipMajorant k :=
        Summable.sum_le_tsum _ (fun k _ => recipMajorant_nonneg k) summable_recipMajorant

/-- **Erdős reciprocal-sum theorem for 3-term progressions (k = 3 case).**

Every 3-AP-free set `A ⊆ ℕ` (with `0 ∉ A`) has a convergent reciprocal sum
`∑_{a ∈ A} 1/a < ∞`.  This is the genuine headline consequence of the Bloom–Sisask
density bound (`RothTheoremOQ02.rothNumberNat_bloom_sisask`), and is strictly stronger
than what the qualitative `r₃(N) = o(N)` bound can deliver.

Rests on the single imported Bloom–Sisask assumption; introduces **no new axiom**. -/
theorem threeAPFree_summable_reciprocal
    {A : Set ℕ} (hA : ThreeAPFree A) (hA0 : 0 ∉ A) :
    Summable (fun a : A => (1 : ℝ) / a) := by
  classical
  rw [show (fun a : A => (1 : ℝ) / (a : ℝ)) = (fun n : ℕ => (1 : ℝ) / (n : ℝ)) ∘ Subtype.val from rfl,
    summable_subtype_iff_indicator]
  refine summable_of_sum_range_le (c := ∑' k, recipMajorant k)
    (fun n => by rw [Set.indicator_apply]; split_ifs <;> positivity) (fun n => ?_)
  -- Partial sum over `range n` equals a reciprocal sum over a finite 3-AP-free set.
  have hcov : ∑ i ∈ Finset.range n, A.indicator (fun m => (1 : ℝ) / m) i
      = ∑ a ∈ (Finset.range n).filter (· ∈ A), (1 : ℝ) / a := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i _ => by simp [Set.indicator_apply])
  rw [hcov]
  have hsubA : (↑((Finset.range n).filter (· ∈ A)) : Set ℕ) ⊆ A := by
    intro x hx; rw [Finset.coe_filter] at hx; exact hx.2
  have hTAP : ThreeAPFree (((Finset.range n).filter (· ∈ A) : Finset ℕ) : Set ℕ) :=
    ThreeAPFree.mono hsubA hA
  have hT0 : (0 : ℕ) ∉ (Finset.range n).filter (· ∈ A) := by
    simp only [Finset.mem_filter]; rintro ⟨_, h0⟩; exact hA0 h0
  exact finite_recip_sum_le _ hTAP hT0

/-- **Erdős `k = 3` conjecture, contrapositive form.**  Any set `A ⊆ ℕ` (with `0 ∉ A`)
whose reciprocal sum *diverges* is not 3-AP-free.  This is the direct contrapositive of
`threeAPFree_summable_reciprocal`, and the form in which the Erdős conjecture is usually
quoted ("a divergent reciprocal sum forces an arithmetic progression"). -/
theorem not_threeAPFree_of_not_summable_reciprocal
    {A : Set ℕ} (hA0 : 0 ∉ A) (hdiv : ¬ Summable (fun a : A => (1 : ℝ) / a)) :
    ¬ ThreeAPFree A :=
  fun hAP => hdiv (threeAPFree_summable_reciprocal hAP hA0)

/-- **Erdős `k = 3` conjecture, explicit-progression form.**  Any set `A ⊆ ℕ` (with
`0 ∉ A`) whose reciprocal sum diverges contains a *nontrivial* three-term arithmetic
progression `a, a + d, a + 2d` with common difference `d > 0`.  This unpacks the abstract
`¬ ThreeAPFree A` into concrete AP witnesses — the statement of the conjecture as it is
usually phrased.  Rests on the single imported Bloom–Sisask assumption; no new axiom. -/
theorem exists_nontrivial_threeAP_of_not_summable_reciprocal
    {A : Set ℕ} (hA0 : 0 ∉ A) (hdiv : ¬ Summable (fun a : A => (1 : ℝ) / a)) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  have hnot : ¬ ThreeAPFree A := not_threeAPFree_of_not_summable_reciprocal hA0 hdiv
  unfold ThreeAPFree at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, hsum, hne⟩ := hnot
  -- `hsum : a + c = b + b`, `hne : a ≠ c`; the middle term `b` is the average.
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

/-- The **absolute reciprocal-sum constant** `B := ∑'_k recipMajorant k`.  This single real
number simultaneously bounds the reciprocal sum of *every* 3-AP-free subset of `ℕ` (with
`0 ∉ A`); see `threeAPFree_tsum_reciprocal_le` and `exists_universal_recip_bound`.  It is
finite (`summable_recipMajorant`) and positive (`recipBound_pos`). -/
noncomputable def recipBound : ℝ := ∑' k, recipMajorant k

/-- The absolute reciprocal-sum constant is strictly positive (its `k = 0` term already is). -/
theorem recipBound_pos : 0 < recipBound := by
  have h0 : 0 < recipMajorant 0 := by
    unfold recipMajorant
    exact div_pos (by norm_num) (recipMajorant_denom_pos 0)
  exact summable_recipMajorant.tsum_pos recipMajorant_nonneg 0 h0

/-- **Uniform quantitative reciprocal bound.**  For *every* 3-AP-free set `A ⊆ ℕ` with
`0 ∉ A`, the full (infinite) reciprocal sum is bounded by the single absolute constant
`∑'_k recipMajorant k`, independently of `A`:
`∑'_{a ∈ A} 1/a ≤ ∑'_k recipMajorant k`.

This strengthens `threeAPFree_summable_reciprocal` from a qualitative "convergent" statement
to an explicit *uniform* upper bound — the same finite constant works for all 3-AP-free sets
at once.  Proof: `Summable.tsum_le_of_sum_le` reduces to bounding every finite partial sum,
and each finite partial sum ranges over a finite 3-AP-free subset of `ℕ`, to which
`finite_recip_sum_le` applies.  Rests on the single imported Bloom–Sisask assumption; no new
axiom. -/
theorem threeAPFree_tsum_reciprocal_le
    {A : Set ℕ} (hA : ThreeAPFree A) (hA0 : 0 ∉ A) :
    ∑' a : A, (1 : ℝ) / (a : ℝ) ≤ ∑' k, recipMajorant k := by
  classical
  refine (threeAPFree_summable_reciprocal hA hA0).tsum_le_of_sum_le (fun s => ?_)
  -- The finite index set `s : Finset A` maps to a finite 3-AP-free `T ⊆ ℕ` with `0 ∉ T`.
  set T : Finset ℕ := s.image Subtype.val with hT
  -- Reciprocal sum over `s` equals the reciprocal sum over its image `T`
  -- (`Subtype.val` is injective, so `sum_image` applies with no loss).
  have hsum_eq : ∑ i ∈ s, (1 : ℝ) / (i : ℝ) = ∑ a ∈ T, (1 : ℝ) / (a : ℝ) := by
    rw [hT, Finset.sum_image (Subtype.val_injective.injOn)]
  rw [hsum_eq]
  have hTsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    rw [hT, Finset.coe_image, Set.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact i.property
  have hTAP : ThreeAPFree (T : Set ℕ) := ThreeAPFree.mono hTsub hA
  have hT0 : (0 : ℕ) ∉ T := by
    intro h0
    rw [hT, Finset.mem_image] at h0
    obtain ⟨i, _, hi⟩ := h0
    exact hA0 (by rw [← hi]; exact i.property)
  exact finite_recip_sum_le T hTAP hT0

/-- **Universal reciprocal-sum bound (packaged form).**  There is an *absolute* constant
`B > 0` — independent of the set — such that every 3-AP-free `A ⊆ ℕ` with `0 ∉ A` satisfies
`∑'_{a ∈ A} 1/a ≤ B`.  This is the strongest quantitative form of the `k = 3` Erdős
consequence obtainable from the Bloom–Sisask bound: not only is each reciprocal sum finite,
they are all bounded by one common constant. -/
theorem exists_universal_recip_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (A : Set ℕ), ThreeAPFree A → 0 ∉ A →
      ∑' a : A, (1 : ℝ) / (a : ℝ) ≤ B :=
  ⟨recipBound, recipBound_pos, fun _A hA hA0 => threeAPFree_tsum_reciprocal_le hA hA0⟩

/-- **Finite checkable criterion (contrapositive of the uniform bound).**  A *finite* set
`S ⊆ ℕ` (with `0 ∉ S`) whose reciprocal sum already *exceeds* the absolute constant
`recipBound` cannot be 3-AP-free: `recipBound < ∑_{a ∈ S} 1/a → ¬ ThreeAPFree S`.

Where `not_threeAPFree_of_not_summable_reciprocal` needs the full infinite sum to *diverge*,
this only needs one finite over-threshold partial sum — a concrete, computable certificate
that forces a three-term progression.  Immediate contrapositive of `finite_recip_sum_le`
(`∑_{a ∈ S} 1/a ≤ recipBound` for every finite 3-AP-free `S`). -/
theorem not_threeAPFree_of_finite_recip_sum_gt
    (S : Finset ℕ) (hS0 : 0 ∉ S)
    (hgt : recipBound < ∑ a ∈ S, (1 : ℝ) / (a : ℝ)) :
    ¬ ThreeAPFree (S : Set ℕ) := by
  intro hAP
  have hle : ∑ a ∈ S, (1 : ℝ) / (a : ℝ) ≤ recipBound := by
    unfold recipBound
    exact finite_recip_sum_le S hAP hS0
  linarith

/-- **Finite explicit-progression criterion.**  A finite set `S ⊆ ℕ` (with `0 ∉ S`) whose
reciprocal sum exceeds `recipBound` contains a *nontrivial* three-term arithmetic progression
`a, a + d, a + 2d` with `d > 0`.  The finite, computable analogue of
`exists_nontrivial_threeAP_of_not_summable_reciprocal`: rather than a divergent infinite sum,
a single finite reciprocal sum over the absolute threshold `recipBound` already exhibits the
progression.  Unpacks `not_threeAPFree_of_finite_recip_sum_gt` into concrete AP witnesses. -/
theorem exists_threeAP_of_finite_recip_sum_gt
    (S : Finset ℕ) (hS0 : 0 ∉ S)
    (hgt : recipBound < ∑ a ∈ S, (1 : ℝ) / (a : ℝ)) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ S ∧ a + d ∈ S ∧ a + 2 * d ∈ S := by
  have hnot : ¬ ThreeAPFree (S : Set ℕ) :=
    not_threeAPFree_of_finite_recip_sum_gt S hS0 hgt
  unfold ThreeAPFree at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, hsum, hne⟩ := hnot
  -- `hsum : a + c = b + b`, `hne : a ≠ c`; the middle term `b` is the average.
  rcases lt_or_gt_of_ne hne with hlt | hgt'
  · -- `a < c`: progression starts at `a` with difference `b - a`.
    refine ⟨a, b - a, by omega, Finset.mem_coe.mp ha, ?_, ?_⟩
    · have h : a + (b - a) = b := by omega
      rw [h]; exact Finset.mem_coe.mp hb
    · have h : a + 2 * (b - a) = c := by omega
      rw [h]; exact Finset.mem_coe.mp hc
  · -- `c < a`: progression starts at `c` with difference `b - c`.
    refine ⟨c, b - c, by omega, Finset.mem_coe.mp hc, ?_, ?_⟩
    · have h : c + (b - c) = b := by omega
      rw [h]; exact Finset.mem_coe.mp hb
    · have h : c + 2 * (b - c) = a := by omega
      rw [h]; exact Finset.mem_coe.mp ha

/-
## Dilation covariance of the reciprocal bound

The 3-AP-free property is preserved by the dilation `x ↦ k·x` (`k ≠ 0`): scaling every
element by a common factor cannot create a 3-term progression, because `k·a, k·b, k·c`
form one iff `a, b, c` do (`k` cancels).  Under the same dilation the reciprocal sum
scales by *exactly* `1/k`, so the dilate `k·A` obeys the **sharper** bound
`∑' 1/(k·a) ≤ recipBound/k`.  This exhibits the universal reciprocal bound as
dilation-covariant, and shows the family of dilates `k·A` (`k ≥ 2`) satisfies strictly
smaller reciprocal bounds than the uniform constant — structural information orthogonal
to the (subset-)monotone universal bound, which only ever gives the single constant
`recipBound`.
-/

/-- **Dilation preserves 3-AP-freeness.**  For `k ≠ 0` the image of a 3-AP-free set under
`x ↦ k·x` is again 3-AP-free: `k·a + k·c = 2·k·b ⟺ a + c = 2b`, so a progression in the
dilate forces one in the original. -/
theorem threeAPFree_nat_mul_image {k : ℕ} (hk : k ≠ 0) {A : Set ℕ} (hA : ThreeAPFree A) :
    ThreeAPFree ((fun a => k * a) '' A) := by
  rw [threeAPFree_iff_eq_right]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hsum
  have hac : a + c = b + b := by
    have hmul : k * (a + c) = k * (b + b) := by rw [Nat.mul_add, Nat.mul_add]; exact hsum
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) hmul
  have hEq : a = c := threeAPFree_iff_eq_right.mp hA ha hb hc hac
  rw [hEq]

/-- `0 ∉ k·A` when `0 ∉ A` and `k ≠ 0` (the only preimage of `0` under `x ↦ k·x` is `0`). -/
theorem zero_notMem_nat_mul_image {k : ℕ} (hk : k ≠ 0) {A : Set ℕ} (hA0 : 0 ∉ A) :
    (0 : ℕ) ∉ (fun a => k * a) '' A := by
  rintro ⟨a, ha, h0⟩
  have ha0 : a = 0 := by
    rcases Nat.mul_eq_zero.mp h0 with hk0 | ha0
    · exact absurd hk0 hk
    · exact ha0
  exact hA0 (ha0 ▸ ha)

/-- **Reciprocal-sum covariance under dilation.**  For `k ≠ 0` and any `A ⊆ ℕ`, the
reciprocal sum of the dilate `k·A` is exactly `1/k` times that of `A`:
`∑'_{x ∈ k·A} 1/x = (1/k)·∑'_{a ∈ A} 1/a`. -/
theorem dilate_tsum_reciprocal_eq {k : ℕ} (hk : k ≠ 0) (A : Set ℕ) :
    ∑' x : ((fun a => k * a) '' A), (1 : ℝ) / (x : ℝ)
      = (1 / (k : ℝ)) * ∑' a : A, (1 : ℝ) / (a : ℝ) := by
  have hinj : Function.Injective (fun a : ℕ => k * a) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h
  let e := Equiv.Set.image (fun a : ℕ => k * a) A hinj
  rw [← Equiv.tsum_eq e (fun x : ((fun a => k * a) '' A) => (1 : ℝ) / (x : ℝ)),
    ← tsum_mul_left]
  refine tsum_congr (fun a => ?_)
  have hcoe : ((e a : ((fun a => k * a) '' A)) : ℕ) = k * (a : ℕ) := rfl
  rw [hcoe, Nat.cast_mul, div_mul_div_comm, one_mul]

/-- **Sharper (dilation-covariant) reciprocal bound.**  A 3-AP-free set dilated by `k ≥ 1`
obeys `∑'_{x ∈ k·A} 1/x ≤ recipBound / k` — strictly smaller than the uniform constant
`recipBound` for `k ≥ 2`.  Combines dilation covariance with the universal bound on `A`. -/
theorem dilate_tsum_reciprocal_le {k : ℕ} (hk : k ≠ 0) {A : Set ℕ}
    (hA : ThreeAPFree A) (hA0 : 0 ∉ A) :
    ∑' x : ((fun a => k * a) '' A), (1 : ℝ) / (x : ℝ) ≤ (1 / (k : ℝ)) * recipBound := by
  rw [dilate_tsum_reciprocal_eq hk A]
  exact mul_le_mul_of_nonneg_left (threeAPFree_tsum_reciprocal_le hA hA0) (by positivity)

/-
## Effective tail decay of the reciprocal bound (concentration at height `2^m`)

The universal bound `∑'_{a ∈ A} 1/a ≤ recipBound` is a single constant.  A finer, orthogonal
question is *where* the reciprocal mass of a 3-AP-free set can sit.  Define the **tail majorant**

  `recipTail m := ∑'_k recipMajorant (k + m)`   (the dyadic majorant summed from block `m` on).

If a 3-AP-free set `A` lives entirely at height `≥ 2^m` (every element `2^m ≤ a`), then all its
dyadic blocks have index `≥ m`, so its reciprocal sum is bounded by `recipTail m`, *not merely*
by the full `recipBound`.  Since `recipMajorant` is summable, `recipTail m → 0` as `m → ∞`
(`tendsto_sum_nat_add`).  Hence the reciprocal mass carried by 3-AP-free sets of large minimum
element vanishes — uniformly and at an explicit rate — a quantitative *concentration* statement
that neither the total-sum bound nor the dilation covariance provides.
-/

/-- The **tail majorant** `recipTail m = ∑'_k recipMajorant (k + m)`: the dyadic majorant summed
over blocks of index `≥ m`.  `recipTail 0 = recipBound`, and `recipTail m → 0` as `m → ∞`. -/
noncomputable def recipTail (m : ℕ) : ℝ := ∑' k, recipMajorant (k + m)

/-- The shifted majorant `k ↦ recipMajorant (k + m)` is summable (shift of a summable series). -/
theorem summable_recipMajorant_add (m : ℕ) : Summable (fun k => recipMajorant (k + m)) :=
  (summable_nat_add_iff m).2 summable_recipMajorant

/-- The tail majorant is nonnegative. -/
theorem recipTail_nonneg (m : ℕ) : 0 ≤ recipTail m :=
  tsum_nonneg (fun k => recipMajorant_nonneg _)

/-- At `m = 0` the tail majorant is the full absolute constant `recipBound`. -/
theorem recipTail_zero : recipTail 0 = recipBound := by
  unfold recipTail recipBound
  simp

/-- **Tail reciprocal bound (finite form).**  A finite 3-AP-free set `T` (`0 ∉ T`) whose elements
all sit at height `≥ 2^m` has reciprocal sum bounded by the *tail* majorant `recipTail m`.  This
sharpens `finite_recip_sum_le` (which only gives `recipBound = recipTail 0`) whenever `m ≥ 1`.

Proof: every element `a ∈ T` has `2^m ≤ a`, so its dyadic index `k = ⌊log₂ a⌋ ≥ m`
(`Nat.le_log_iff_pow_le`); the fiber decomposition of `T` therefore ranges over block indices
`k ≥ m` only.  Bounding each fiber by `recipMajorant k` and reindexing `k ↦ k - m` identifies the
resulting finite sum with a partial sum of `∑'_k recipMajorant (k + m) = recipTail m`. -/
theorem finite_recip_sum_le_of_min_ge (T : Finset ℕ) (hT : ThreeAPFree (T : Set ℕ)) (hT0 : 0 ∉ T)
    (m : ℕ) (hmin : ∀ a ∈ T, 2 ^ m ≤ a) :
    ∑ a ∈ T, (1 : ℝ) / a ≤ recipTail m := by
  classical
  have hmaps : ∀ a ∈ T, Nat.log 2 a ∈ T.image (Nat.log 2) :=
    fun a ha => Finset.mem_image_of_mem _ ha
  -- Every block index appearing in `T` is `≥ m`.
  have hK : ∀ k ∈ T.image (Nat.log 2), m ≤ k := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨a, ha, rfl⟩ := hk
    have ha0 : a ≠ 0 := fun h => hT0 (h ▸ ha)
    exact (Nat.le_log_iff_pow_le (by norm_num) ha0).mpr (hmin a ha)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (1 : ℝ) / a)]
  -- Fiberwise bound, then reindex the block sum against the tail tsum.
  have hfib : ∑ k ∈ T.image (Nat.log 2), ∑ a ∈ T.filter (fun a => Nat.log 2 a = k), (1 : ℝ) / a
      ≤ ∑ k ∈ T.image (Nat.log 2), recipMajorant k :=
    Finset.sum_le_sum (fun k _ => fiber_sum_le T hT hT0 k)
  refine hfib.trans ?_
  -- `∑_{k ∈ K} recipMajorant k = ∑_{j ∈ K.image (·-m)} recipMajorant (j+m)` (reindex by `-m`).
  have hinj : ∀ x ∈ T.image (Nat.log 2), ∀ y ∈ T.image (Nat.log 2), x - m = y - m → x = y := by
    intro x hx y hy h
    have hxm := hK x hx; have hym := hK y hy; omega
  have hreindex : ∑ k ∈ T.image (Nat.log 2), recipMajorant k
      = ∑ j ∈ (T.image (Nat.log 2)).image (· - m), recipMajorant (j + m) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkm : k - m + m = k := by have := hK k hk; omega
    rw [hkm]
  rw [hreindex]
  exact Summable.sum_le_tsum _ (fun j _ => recipMajorant_nonneg _) (summable_recipMajorant_add m)

/-- **Tail reciprocal bound (infinite form).**  Every 3-AP-free set `A ⊆ ℕ` (`0 ∉ A`) whose
elements all sit at height `≥ 2^m` satisfies `∑'_{a ∈ A} 1/a ≤ recipTail m`.  The tail constant
shrinks to `0` as `m → ∞` (`recipTail_tendsto_zero`), so this is a genuine height-indexed
sharpening of the uniform bound `threeAPFree_tsum_reciprocal_le`. -/
theorem threeAPFree_tsum_reciprocal_le_of_min_ge
    {A : Set ℕ} (hA : ThreeAPFree A) (hA0 : 0 ∉ A) (m : ℕ) (hmin : ∀ a ∈ A, 2 ^ m ≤ a) :
    ∑' a : A, (1 : ℝ) / (a : ℝ) ≤ recipTail m := by
  classical
  refine (threeAPFree_summable_reciprocal hA hA0).tsum_le_of_sum_le (fun s => ?_)
  set T : Finset ℕ := s.image Subtype.val with hT
  have hsum_eq : ∑ i ∈ s, (1 : ℝ) / (i : ℝ) = ∑ a ∈ T, (1 : ℝ) / (a : ℝ) := by
    rw [hT, Finset.sum_image (Subtype.val_injective.injOn)]
  rw [hsum_eq]
  have hTsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    rw [hT, Finset.coe_image, Set.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact i.property
  have hTAP : ThreeAPFree (T : Set ℕ) := ThreeAPFree.mono hTsub hA
  have hT0 : (0 : ℕ) ∉ T := by
    intro h0
    rw [hT, Finset.mem_image] at h0
    obtain ⟨i, _, hi⟩ := h0
    exact hA0 (by rw [← hi]; exact i.property)
  have hTmin : ∀ a ∈ T, 2 ^ m ≤ a := by
    intro a ha
    rw [hT, Finset.mem_image] at ha
    obtain ⟨i, _, rfl⟩ := ha
    exact hmin _ i.property
  exact finite_recip_sum_le_of_min_ge T hTAP hT0 m hTmin

/-- **The tail majorant vanishes.**  `recipTail m → 0` as `m → ∞`.  Immediate from
`tendsto_sum_nat_add` applied to the summable `recipMajorant`. -/
theorem recipTail_tendsto_zero : Filter.Tendsto recipTail Filter.atTop (nhds 0) := by
  have h := tendsto_sum_nat_add recipMajorant
  exact h

/-- **Uniform reciprocal concentration.**  For every `ε > 0` there is a height threshold `m` such
that *every* 3-AP-free set `A ⊆ ℕ` (`0 ∉ A`) living entirely at height `≥ 2^m` has reciprocal sum
`≤ ε`.  A single `m` works for all such sets at once: the reciprocal mass carried by high 3-AP-free
sets is uniformly negligible.  Combines the tail bound with `recipTail_tendsto_zero`. -/
theorem exists_height_recip_small (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ (A : Set ℕ), ThreeAPFree A → 0 ∉ A → (∀ a ∈ A, 2 ^ m ≤ a) →
      ∑' a : A, (1 : ℝ) / (a : ℝ) ≤ ε := by
  have hev : ∀ᶠ n in Filter.atTop, recipTail n < ε :=
    (tendsto_order.1 recipTail_tendsto_zero).2 ε hε
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨m, fun A hA hA0 hAmin =>
    (threeAPFree_tsum_reciprocal_le_of_min_ge hA hA0 m hAmin).trans hm.le⟩

/-!
### Monotone structure of the tail majorant (`recipTail`)

The tail constant `recipTail m = ∑'_k recipMajorant (k + m)` obeys a clean one-step recurrence
`recipTail m = recipMajorant m + recipTail (m + 1)`: peeling the `k = 0` block off the shifted
series leaves the next tail.  Equivalently `recipTail (m + 1) = recipTail m − recipMajorant m`.
Because every block majorant is *strictly* positive, the tail is strictly decreasing in the
height index `m`, and never exceeds the full absolute constant `recipBound = recipTail 0`.
This upgrades the qualitative `recipTail_tendsto_zero` into an exact monotone descent — the
structural prerequisite for an explicit closed-form decay rate (integral comparison for the
`p`-series tail via `AntitoneOn.sum_le_integral`; see the next-steps note in `state.md`).
-/

/-- The block majorant is strictly positive. -/
theorem recipMajorant_pos (k : ℕ) : 0 < recipMajorant k := by
  unfold recipMajorant
  exact div_pos (by norm_num) (recipMajorant_denom_pos k)

/-- **One-step recurrence for the tail majorant.**  Peeling the `k = 0` block off the shifted
series `∑'_k recipMajorant (k + m)` leaves the next tail:
`recipTail m = recipMajorant m + recipTail (m + 1)`. -/
theorem recipTail_succ (m : ℕ) :
    recipTail m = recipMajorant m + recipTail (m + 1) := by
  have h := (summable_recipMajorant_add m).tsum_eq_zero_add
  have hcongr : (fun b : ℕ => recipMajorant (b + 1 + m))
      = (fun b : ℕ => recipMajorant (b + (m + 1))) := by
    funext b; congr 1; omega
  unfold recipTail
  rw [h, zero_add, hcongr]

/-- **Exact one-step decrement.**  `recipTail (m + 1) = recipTail m − recipMajorant m`. -/
theorem recipTail_succ_eq_sub (m : ℕ) :
    recipTail (m + 1) = recipTail m - recipMajorant m := by
  rw [recipTail_succ m]; ring

/-- **The tail majorant is antitone**: `recipTail` decreases (weakly) as the height index grows. -/
theorem recipTail_antitone : Antitone recipTail := by
  refine antitone_nat_of_succ_le (fun m => ?_)
  rw [recipTail_succ_eq_sub m]
  linarith [recipMajorant_nonneg m]

/-- **The tail majorant is strictly antitone**: each step strictly decreases the tail, since the
peeled block majorant `recipMajorant m` is strictly positive. -/
theorem recipTail_strictAnti : StrictAnti recipTail := by
  refine strictAnti_nat_of_succ_lt (fun m => ?_)
  rw [recipTail_succ_eq_sub m]
  linarith [recipMajorant_pos m]

/-- The tail majorant never exceeds the full absolute constant `recipBound = recipTail 0`. -/
theorem recipTail_le_recipBound (m : ℕ) : recipTail m ≤ recipBound := by
  rw [← recipTail_zero]
  exact recipTail_antitone (Nat.zero_le m)

/-- For `m ≥ 1` the tail bound is *strictly* better than the absolute constant `recipBound`:
forcing a 3-AP-free set up to height `≥ 2^m` genuinely lowers its reciprocal ceiling. -/
theorem recipTail_lt_recipBound {m : ℕ} (hm : 0 < m) : recipTail m < recipBound := by
  rw [← recipTail_zero]
  exact recipTail_strictAnti hm

#check @threeAPFree_summable_reciprocal
#check @finite_recip_sum_le
#check @fiber_sum_le
#check @summable_recipMajorant
#check @threeAPFree_tsum_reciprocal_le
#check @exists_universal_recip_bound
#check @finite_recip_sum_le_of_min_ge
#check @threeAPFree_tsum_reciprocal_le_of_min_ge
#check @recipTail_tendsto_zero
#check @exists_height_recip_small
#check @recipTail_succ
#check @recipTail_succ_eq_sub
#check @recipTail_strictAnti
#check @recipTail_le_recipBound

-- Axiom audit: the reciprocal-sum theorem rests on exactly the single imported Bloom–Sisask
-- assumption `RothTheoremOQ02.rothNumberNat_bloom_sisask` — no new axiom, no `sorryAx`.
#print axioms threeAPFree_summable_reciprocal
#print axioms summable_recipMajorant
#print axioms exists_nontrivial_threeAP_of_not_summable_reciprocal
#print axioms threeAPFree_tsum_reciprocal_le
#print axioms exists_universal_recip_bound
#print axioms threeAPFree_nat_mul_image
#print axioms dilate_tsum_reciprocal_le
#print axioms threeAPFree_tsum_reciprocal_le_of_min_ge
#print axioms exists_height_recip_small
#print axioms recipTail_succ
#print axioms recipTail_strictAnti

end RothTheoremOQ01Reciprocal
