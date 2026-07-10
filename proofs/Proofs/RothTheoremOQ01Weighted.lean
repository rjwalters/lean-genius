import Proofs.RothTheoremOQ01Reciprocal
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
# Log-weighted reciprocal sums for 3-AP-free sets (roth-theorem-oq-01)

The companion file `RothTheoremOQ01Reciprocal.lean` uses the Bloom–Sisask density bound
`r₃(N) ≪ N / (log N)^{1+c}` to prove the `k = 3` Erdős reciprocal-sum theorem: every
3-AP-free `A ⊆ ℕ` has `∑_{a ∈ A} 1/a < ∞`.  That statement uses only that the saving
`1 + c` exceeds `1`.

This file exploits the *full strength* of the power-of-log saving.  Because Bloom–Sisask
saves a whole power of log — not merely a single `log log` (Roth 1953) and not merely
"some" saving — one can afford to **re-inflate** each reciprocal by up to `c` powers of
`log a` and still converge:

> for every `0 ≤ s < c`, every 3-AP-free `A ⊆ ℕ` (with `0 ∉ A`) has
> `∑_{a ∈ A} (log a)^s / a < ∞`,

with a single absolute bound independent of `A`.  This is strictly stronger than the plain
reciprocal-sum theorem (the `s = 0` case) and is *false* for a saving of only one power of
log (`c = 0`): the exponent of the majorant `p`-series is exactly `1 + c − s`, which
exceeds `1` **iff `s < c`**.  So the weighted statement is a faithful quantitative witness
that the Bloom–Sisask saving is a genuine *power* of log, converting each extra fraction of
that power directly into a log-weight the reciprocal sum can absorb.

## Method

Identical dyadic partial summation to the unweighted file.  On the `k`-th dyadic block
`A ∩ [2^k, 2^{k+1})` every element `a` satisfies `log a ≤ (k+1)·log 2`, so the weight
`(log a)^s ≤ ((k+1)·log 2)^s`; combining with the density count
`≤ 2^{k+1}/((k+1)·log 2)^{1+c}` and `1/a ≤ 2^{-k}` gives the block contribution
`≤ 2 / ((k+1)·log 2)^{1+c-s} =: weightedMajorant s k`, whose sum over `k` is a convergent
`p`-series exactly when `s < c`.

No new axiom: everything rests on the single imported
`RothTheoremOQ02.rothNumberNat_bloom_sisask` via `threeAPFree_card_le_blasi`.
-/

open Asymptotics Filter Topology Finset
open scoped BigOperators

namespace RothTheoremOQ01Weighted

open RothTheoremOQ01 RothTheoremOQ02 RothTheoremOQ01Reciprocal

variable {s : ℝ}

/-- The **log-weighted dyadic majorant**
`weightedMajorant s k = 2 / ((k+1)·log 2)^{1 + blasiConst − s}`.  It bounds the
`(log a)^s`-weighted reciprocal contribution of the `k`-th dyadic block of any 3-AP-free
set, and is summable in `k` precisely because the exponent `1 + blasiConst − s > 1` when
`s < blasiConst`. -/
noncomputable def weightedMajorant (s : ℝ) (k : ℕ) : ℝ :=
  2 / (((k : ℝ) + 1) * Real.log 2) ^ (1 + RothTheoremOQ02.blasiConst - s)

/-- The rpow denominator of the weighted majorant is positive. -/
theorem weightedMajorant_denom_pos (k : ℕ) :
    (0 : ℝ) < (((k : ℝ) + 1) * Real.log 2) ^ (1 + RothTheoremOQ02.blasiConst - s) :=
  Real.rpow_pos_of_pos (RothTheoremOQ01Reciprocal.recipMajorant_base_pos k) _

/-- Nonnegativity of the weighted majorant. -/
theorem weightedMajorant_nonneg (k : ℕ) : 0 ≤ weightedMajorant s k := by
  unfold weightedMajorant
  exact le_of_lt (div_pos (by norm_num) (weightedMajorant_denom_pos k))

/-- **The weighted dyadic majorant is summable** whenever `s < blasiConst`
(`p`-series with `p = 1 + blasiConst − s > 1`). -/
theorem summable_weightedMajorant (hs : s < RothTheoremOQ02.blasiConst) :
    Summable (weightedMajorant s) := by
  have hp : (1 : ℝ) < 1 + RothTheoremOQ02.blasiConst - s := by linarith
  have hbase : Summable
      (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + RothTheoremOQ02.blasiConst - s)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (1 + RothTheoremOQ02.blasiConst - s)).mpr hp
    have heq : (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 + RothTheoremOQ02.blasiConst - s))
        = (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + RothTheoremOQ02.blasiConst - s)) := by
      funext n; rw [abs_of_nonneg (by positivity)]
    rwa [heq] at h
  have hrw : weightedMajorant s =
      fun k : ℕ => (2 / Real.log 2 ^ (1 + RothTheoremOQ02.blasiConst - s)) *
        (1 / ((k : ℝ) + 1) ^ (1 + RothTheoremOQ02.blasiConst - s)) := by
    funext k
    unfold weightedMajorant
    rw [Real.mul_rpow (by positivity) (Real.log_nonneg (by norm_num))]
    ring
  rw [hrw]
  exact hbase.mul_left _

/-- **Per-block weighted reciprocal bound.**  For any finite 3-AP-free `T` with `0 ∉ T` and
weight exponent `0 ≤ s`, the `(log a)^s`-weighted reciprocal sum over the `k`-th dyadic
fiber `{a ∈ T : ⌊log₂ a⌋ = k}` is at most `weightedMajorant s k`. -/
theorem weighted_fiber_sum_le (hs0 : 0 ≤ s)
    (T : Finset ℕ) (hT : ThreeAPFree (T : Set ℕ)) (hT0 : 0 ∉ T) (k : ℕ) :
    ∑ a ∈ T.filter (fun a => Nat.log 2 a = k), (Real.log a) ^ s / (a : ℝ)
      ≤ weightedMajorant s k := by
  classical
  set F := T.filter (fun a => Nat.log 2 a = k) with hF
  have hFsub : F ⊆ T := Finset.filter_subset _ _
  have hne : ∀ a ∈ F, a ≠ 0 := fun a ha h => hT0 (h ▸ hFsub ha)
  have hlog : ∀ a ∈ F, Nat.log 2 a = k := fun a ha => (Finset.mem_filter.mp ha).2
  have hbpos : (0 : ℝ) < ((k : ℝ) + 1) * Real.log 2 :=
    RothTheoremOQ01Reciprocal.recipMajorant_base_pos k
  -- Every fiber element lies in `[2^k, 2^{k+1})`.
  have hlow : ∀ a ∈ F, (2 : ℝ) ^ k ≤ (a : ℝ) := by
    intro a ha
    have h := Nat.pow_log_le_self 2 (hne a ha)
    rw [hlog a ha] at h
    calc (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (a : ℝ) := by exact_mod_cast h
  have hupp : ∀ a ∈ F, (a : ℝ) < (2 : ℝ) ^ (k + 1) := by
    intro a ha
    have hlt : a < 2 ^ (Nat.log 2 a).succ := Nat.lt_pow_succ_log_self (by norm_num) a
    rw [hlog a ha, Nat.succ_eq_add_one] at hlt
    calc (a : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
      _ = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  -- Weight bound: for `a ∈ F`, `(log a)^s ≤ ((k+1)·log 2)^s`.
  have hwt : ∀ a ∈ F, (Real.log a) ^ s ≤ (((k : ℝ) + 1) * Real.log 2) ^ s := by
    intro a ha
    have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
      have : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (hne a ha)
      exact_mod_cast this
    have hlognn : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg ha1
    have hub : Real.log (a : ℝ) ≤ ((k : ℝ) + 1) * Real.log 2 := by
      have hle : (a : ℝ) ≤ (2 : ℝ) ^ (k + 1) := le_of_lt (hupp a ha)
      calc Real.log (a : ℝ) ≤ Real.log ((2 : ℝ) ^ (k + 1)) :=
            Real.log_le_log (by positivity) hle
        _ = ((k : ℝ) + 1) * Real.log 2 := by
            rw [Real.log_pow]; push_cast; ring
    exact Real.rpow_le_rpow hlognn hub hs0
  have hWnn : (0 : ℝ) ≤ (((k : ℝ) + 1) * Real.log 2) ^ s :=
    Real.rpow_nonneg (le_of_lt hbpos) s
  -- Termwise: `(log a)^s / a ≤ ((k+1)·log 2)^s · (1/2^k)`, hence sum `≤ card · that`.
  have hstep1 : ∑ a ∈ F, (Real.log a) ^ s / (a : ℝ)
      ≤ (F.card : ℝ) * ((((k : ℝ) + 1) * Real.log 2) ^ s * (1 / (2 : ℝ) ^ k)) := by
    calc ∑ a ∈ F, (Real.log a) ^ s / (a : ℝ)
        ≤ ∑ _a ∈ F, (((k : ℝ) + 1) * Real.log 2) ^ s * (1 / (2 : ℝ) ^ k) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          rw [div_eq_mul_one_div]
          exact mul_le_mul (hwt a ha) (one_div_le_one_div_of_le h2k (hlow a ha))
            (by positivity) hWnn
      _ = (F.card : ℝ) * ((((k : ℝ) + 1) * Real.log 2) ^ s * (1 / (2 : ℝ) ^ k)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hk : k = 0
  · -- k = 0: the fiber is contained in `{1}`, where `log 1 = 0` and the weight vanishes.
    subst hk
    have hone : ∀ a ∈ F, a = 1 := by
      intro a ha
      have hlt : a < 2 ^ (Nat.log 2 a).succ := Nat.lt_pow_succ_log_self (by norm_num) a
      rw [hlog a ha] at hlt
      have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (hne a ha)
      simp only [Nat.succ_eq_add_one, Nat.zero_add, pow_one] at hlt
      omega
    have hle1 : ∑ a ∈ F, (Real.log a) ^ s / (a : ℝ) ≤ 1 := by
      calc ∑ a ∈ F, (Real.log a) ^ s / (a : ℝ) ≤ ∑ _a ∈ F, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun a ha => ?_)
            rw [hone a ha]
            simp only [Nat.cast_one, Real.log_one, div_one]
            exact Real.rpow_le_one le_rfl (by norm_num) hs0
        _ = (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 1 := by
            have : F.card ≤ 1 :=
              Finset.card_le_one.mpr (fun a ha b hb => by rw [hone a ha, hone b hb])
            exact_mod_cast this
    refine hle1.trans ?_
    have hz : (0 : ℝ) ≤ 1 + RothTheoremOQ02.blasiConst - s := by
      have := RothTheoremOQ02.blasiConst_pos; linarith
    have hpos : (0 : ℝ) < Real.log 2 ^ (1 + RothTheoremOQ02.blasiConst - s) :=
      Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    unfold weightedMajorant
    rw [Nat.cast_zero, zero_add, one_mul, le_div_iff₀ hpos, one_mul]
    calc Real.log 2 ^ (1 + RothTheoremOQ02.blasiConst - s)
        ≤ 1 := Real.rpow_le_one (Real.log_nonneg (by norm_num)) hlog2le1 hz
      _ ≤ 2 := by norm_num
  · -- k ≥ 1: apply the density bound at `N = 2^{k+1} ≥ 3`.
    have hN3 : 3 ≤ 2 ^ (k + 1) := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsubN : ∀ x ∈ F, x < 2 ^ (k + 1) := by
      intro x hx
      have hlt : x < 2 ^ (Nat.log 2 x).succ := Nat.lt_pow_succ_log_self (by norm_num) x
      rwa [hlog x hx, Nat.succ_eq_add_one] at hlt
    have hFAP : ThreeAPFree (F : Set ℕ) := ThreeAPFree.mono (Finset.coe_subset.mpr hFsub) hT
    have hdens := threeAPFree_card_le_blasi hFAP hN3 hsubN
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add, Nat.cast_one] at hdens
    have hDpos := RothTheoremOQ01Reciprocal.recipMajorant_denom_pos k
    calc ∑ a ∈ F, (Real.log a) ^ s / (a : ℝ)
        ≤ (F.card : ℝ) * ((((k : ℝ) + 1) * Real.log 2) ^ s * (1 / (2 : ℝ) ^ k)) := hstep1
      _ ≤ ((2 : ℝ) ^ (k + 1) / (((k : ℝ) + 1) * Real.log 2) ^ (1 + RothTheoremOQ02.blasiConst)) *
            ((((k : ℝ) + 1) * Real.log 2) ^ s * (1 / (2 : ℝ) ^ k)) := by
            exact mul_le_mul_of_nonneg_right hdens (by positivity)
      _ = weightedMajorant s k := by
            unfold weightedMajorant
            rw [pow_succ, Real.rpow_sub hbpos]
            field_simp
            ring

/-- **Uniform bound on finite weighted reciprocal sums.**  For every finite 3-AP-free `T`
(`0 ∉ T`) and `0 ≤ s < blasiConst`, the `(log a)^s`-weighted reciprocal sum is bounded by
the single constant `∑'_k weightedMajorant s k`, independently of `T`. -/
theorem weighted_finite_sum_le (hs0 : 0 ≤ s) (hs : s < RothTheoremOQ02.blasiConst)
    (T : Finset ℕ) (hT : ThreeAPFree (T : Set ℕ)) (hT0 : 0 ∉ T) :
    ∑ a ∈ T, (Real.log a) ^ s / (a : ℝ) ≤ ∑' k, weightedMajorant s k := by
  classical
  have hmaps : ∀ a ∈ T, Nat.log 2 a ∈ T.image (Nat.log 2) :=
    fun a ha => Finset.mem_image_of_mem _ ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (Real.log a) ^ s / (a : ℝ))]
  calc ∑ k ∈ T.image (Nat.log 2), ∑ a ∈ T.filter (fun a => Nat.log 2 a = k),
          (Real.log a) ^ s / (a : ℝ)
      ≤ ∑ k ∈ T.image (Nat.log 2), weightedMajorant s k :=
        Finset.sum_le_sum (fun k _ => weighted_fiber_sum_le hs0 T hT hT0 k)
    _ ≤ ∑' k, weightedMajorant s k :=
        Summable.sum_le_tsum _ (fun k _ => weightedMajorant_nonneg k)
          (summable_weightedMajorant hs)

/-- **Log-weighted Erdős reciprocal-sum theorem (k = 3 case).**

For every weight exponent `0 ≤ s < blasiConst`, every 3-AP-free set `A ⊆ ℕ` (with `0 ∉ A`)
has a *convergent* log-weighted reciprocal sum `∑_{a ∈ A} (log a)^s / a < ∞`.

This is strictly stronger than the plain reciprocal-sum theorem
(`RothTheoremOQ01Reciprocal.threeAPFree_summable_reciprocal`, the `s = 0` case): it uses the
full *power-of-log* saving of Bloom–Sisask, since the majorant `p`-series has exponent
`1 + blasiConst − s`, which exceeds `1` exactly when `s < blasiConst`.  Rests on the single
imported Bloom–Sisask assumption; introduces **no new axiom**. -/
theorem threeAPFree_summable_log_weighted_reciprocal
    (hs0 : 0 ≤ s) (hs : s < RothTheoremOQ02.blasiConst)
    {A : Set ℕ} (hA : ThreeAPFree A) (hA0 : 0 ∉ A) :
    Summable (fun a : A => (Real.log a) ^ s / (a : ℝ)) := by
  classical
  rw [show (fun a : A => (Real.log (a : ℝ)) ^ s / (a : ℝ))
        = (fun n : ℕ => (Real.log (n : ℝ)) ^ s / (n : ℝ)) ∘ Subtype.val from rfl,
    summable_subtype_iff_indicator]
  refine summable_of_sum_range_le (c := ∑' k, weightedMajorant s k) (fun n => ?_) (fun n => ?_)
  · -- Nonnegativity of the indicator summand.
    rw [Set.indicator_apply]
    split_ifs with h
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have hne : n ≠ 0 := fun h0 => hA0 (h0 ▸ h)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      have hlognn : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      exact div_nonneg (Real.rpow_nonneg hlognn s) (by positivity)
    · exact le_rfl
  · -- Each partial sum ranges over a finite 3-AP-free subset of `ℕ`.
    have hcov : ∑ i ∈ Finset.range n, A.indicator (fun m => (Real.log (m : ℝ)) ^ s / (m : ℝ)) i
        = ∑ a ∈ (Finset.range n).filter (· ∈ A), (Real.log (a : ℝ)) ^ s / (a : ℝ) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun i _ => by simp [Set.indicator_apply])
    rw [hcov]
    have hsubA : (↑((Finset.range n).filter (· ∈ A)) : Set ℕ) ⊆ A := by
      intro x hx; rw [Finset.coe_filter] at hx; exact hx.2
    have hTAP : ThreeAPFree (((Finset.range n).filter (· ∈ A) : Finset ℕ) : Set ℕ) :=
      ThreeAPFree.mono hsubA hA
    have hT0 : (0 : ℕ) ∉ (Finset.range n).filter (· ∈ A) := by
      simp only [Finset.mem_filter]; rintro ⟨_, h0⟩; exact hA0 h0
    exact weighted_finite_sum_le hs0 hs _ hTAP hT0

/-- The **absolute log-weighted reciprocal-sum constant**
`weightedRecipBound s := ∑'_k weightedMajorant s k` (finite for `s < blasiConst`).  A single
real number bounding the `(log a)^s`-weighted reciprocal sum of *every* 3-AP-free `A ⊆ ℕ`
(with `0 ∉ A`); see `threeAPFree_tsum_log_weighted_reciprocal_le`. -/
noncomputable def weightedRecipBound (s : ℝ) : ℝ := ∑' k, weightedMajorant s k

/-- **Uniform quantitative log-weighted reciprocal bound.**  For every `0 ≤ s < blasiConst`
and every 3-AP-free `A ⊆ ℕ` with `0 ∉ A`, the full (infinite) weighted reciprocal sum is
bounded by the single absolute constant `weightedRecipBound s`, independently of `A`. -/
theorem threeAPFree_tsum_log_weighted_reciprocal_le
    (hs0 : 0 ≤ s) (hs : s < RothTheoremOQ02.blasiConst)
    {A : Set ℕ} (hA : ThreeAPFree A) (hA0 : 0 ∉ A) :
    ∑' a : A, (Real.log (a : ℝ)) ^ s / (a : ℝ) ≤ weightedRecipBound s := by
  classical
  unfold weightedRecipBound
  refine (threeAPFree_summable_log_weighted_reciprocal hs0 hs hA hA0).tsum_le_of_sum_le
    (fun t => ?_)
  set T : Finset ℕ := t.image Subtype.val with hT
  have hsum_eq : ∑ i ∈ t, (Real.log (i : ℝ)) ^ s / (i : ℝ)
      = ∑ a ∈ T, (Real.log (a : ℝ)) ^ s / (a : ℝ) := by
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
  exact weighted_finite_sum_le hs0 hs T hTAP hT0

/-- The absolute log-weighted reciprocal-sum constant `weightedRecipBound s` is strictly
positive for every admissible weight exponent `s < blasiConst` — its `k = 0` term already is.
The weighted analogue of `RothTheoremOQ01Reciprocal.recipBound_pos`. -/
theorem weightedRecipBound_pos (hs : s < RothTheoremOQ02.blasiConst) :
    0 < weightedRecipBound s := by
  unfold weightedRecipBound
  have h0 : 0 < weightedMajorant s 0 := by
    unfold weightedMajorant
    exact div_pos (by norm_num) (weightedMajorant_denom_pos 0)
  exact (summable_weightedMajorant hs).tsum_pos weightedMajorant_nonneg 0 h0

/-- **Universal log-weighted reciprocal-sum bound (packaged form).**  For every admissible
weight exponent `0 ≤ s < blasiConst` there is a single *absolute* constant `B > 0` —
independent of the set — such that every 3-AP-free `A ⊆ ℕ` with `0 ∉ A` satisfies
`∑'_{a ∈ A} (log a)^s / a ≤ B`.  The weighted analogue of
`RothTheoremOQ01Reciprocal.exists_universal_recip_bound`: one common constant simultaneously
bounds the log-weighted reciprocal sums of all 3-AP-free sets at once.  Rests on the single
imported Bloom–Sisask assumption; introduces **no new axiom**. -/
theorem exists_universal_log_weighted_recip_bound
    (hs0 : 0 ≤ s) (hs : s < RothTheoremOQ02.blasiConst) :
    ∃ B : ℝ, 0 < B ∧ ∀ (A : Set ℕ), ThreeAPFree A → 0 ∉ A →
      ∑' a : A, (Real.log (a : ℝ)) ^ s / (a : ℝ) ≤ B :=
  ⟨weightedRecipBound s, weightedRecipBound_pos hs,
    fun _A hA hA0 => threeAPFree_tsum_log_weighted_reciprocal_le hs0 hs hA hA0⟩

/-- **Log-weighted Erdős `k = 3` conjecture, contrapositive form.**  For every admissible
weight exponent `0 ≤ s < blasiConst`, any set `A ⊆ ℕ` (with `0 ∉ A`) whose *log-weighted*
reciprocal sum `∑_{a ∈ A} (log a)^s / a` diverges is not 3-AP-free.  This is the direct
contrapositive of `threeAPFree_summable_log_weighted_reciprocal`, and the weighted analogue
of `RothTheoremOQ01Reciprocal.not_threeAPFree_of_not_summable_reciprocal`.  It is strictly
sharper than the unweighted `s = 0` form: because the extra `(log a)^s` weight only *inflates*
the summand, divergence of the weighted sum is an easier certificate to meet, so more sets are
forced to contain a three-term progression.  Rests on the single imported Bloom–Sisask
assumption; introduces **no new axiom**. -/
theorem not_threeAPFree_of_not_summable_log_weighted_reciprocal
    (hs0 : 0 ≤ s) (hs : s < RothTheoremOQ02.blasiConst)
    {A : Set ℕ} (hA0 : 0 ∉ A)
    (hdiv : ¬ Summable (fun a : A => (Real.log (a : ℝ)) ^ s / (a : ℝ))) :
    ¬ ThreeAPFree A :=
  fun hAP => hdiv (threeAPFree_summable_log_weighted_reciprocal hs0 hs hAP hA0)

#check @threeAPFree_summable_log_weighted_reciprocal
#check @threeAPFree_tsum_log_weighted_reciprocal_le
#check @weightedRecipBound_pos
#check @exists_universal_log_weighted_recip_bound
#check @not_threeAPFree_of_not_summable_log_weighted_reciprocal
#check @weighted_finite_sum_le
#check @weighted_fiber_sum_le
#check @summable_weightedMajorant

-- Axiom audit: the log-weighted reciprocal-sum theorem rests on exactly the single imported
-- Bloom–Sisask assumption `RothTheoremOQ02.rothNumberNat_bloom_sisask` — no new axiom.
#print axioms threeAPFree_summable_log_weighted_reciprocal
#print axioms summable_weightedMajorant
#print axioms threeAPFree_tsum_log_weighted_reciprocal_le
#print axioms exists_universal_log_weighted_recip_bound
#print axioms not_threeAPFree_of_not_summable_log_weighted_reciprocal

end RothTheoremOQ01Weighted
