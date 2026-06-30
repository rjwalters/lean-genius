/-
  Exact count of fitting APs and a factor-2 sharpening of the van der Waerden
  first-moment lower bound (open question van-der-waerden-first-moment-oq-01)

  The base entry `Proofs.VanDerWaerdenFirstMoment` bounds the number of length-`k`
  arithmetic progressions that fit in `[n]` by the deliberately loose count `n²`
  (`card_vdwFamily_le`): it allows every pair `(a, d)` of first term and step.
  That gives the union-bound threshold `n² < 2^(k-1)`, i.e. `W(k) ≳ 2^((k-1)/2)`.

  The open question asks to sharpen this to `~ n²/(k-1)` by bounding the AP step.
  We go further and compute the family's parameter count *exactly*, then extract a
  bound that beats the requested `n²/(k-1)` by a further factor of `2`.

  For a length-`k` AP with step `d` to fit we need `a + (k-1)d < n` with `a ≥ 0`,
  so for each `d` exactly `n - (k-1)d` first terms `a` are admissible (and `0`
  once `(k-1)d ≥ n` — handled automatically by truncated ℕ-subtraction).  Summing
  over `d` gives the exact parameter count

        |{(a,d) fitting}|  =  ∑_{d=1}^{n} (n - (k-1)·d)        (vdwFilter_card_eq_sum)

  a triangular sum.  A telescoping-of-squares argument
  (`2(k-1)(n - (k-1)d) ≤ (n-(k-1)(d-1))² - (n-(k-1)d)²`) collapses it to

        2·(k-1)·|family|  ≤  n²                               (card_vdwFamily_two_mul_le)

  i.e. at most `n²/(2(k-1))` length-`k` APs fit in `[n]` — twice as sharp as the
  `n²/(k-1)` the question asked for, and a factor `(2(k-1))` improvement on the
  base `n²` count.  Feeding this back through the verified Property-B engine widens
  the admissible range of `n` from `n² < 2^(k-1)` to

        n² < 2·(k-1)·2^(k-1)                                  (vdw_lower_bound_sharp)

  a factor-`√(2(k-1))` improvement, giving `W(k) ≳ √(2(k-1))·2^((k-1)/2)`.

  Everything here is elementary counting layered on top of the base entry's
  verified `vdwAP` / `vdwFamily` / `vdw_two_coloring_exists`; the probabilistic
  core remains the gallery's Property-B engine consumed as a black box.

  Status: 0 sorries, 0 axioms, no `native_decide`.  #print axioms reports only
  `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.VanDerWaerdenFirstMoment

namespace ProbMethod.VanDerWaerden

open Finset
open ProbMethod.PropertyB (Mono property_b_two_colorable)
open scoped Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- **Fiber count.** Of the `n` first terms `a ∈ {0,…,n-1}`, exactly `n - c` satisfy
`a + c < n` (and none once `c ≥ n`, via truncated ℕ-subtraction). -/
theorem card_filter_lt (N c : ℕ) :
    ((Finset.range N).filter (fun a => a + c < N)).card = N - c := by
  have : (Finset.range N).filter (fun a => a + c < N) = Finset.range (N - c) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

/-- **Exact parameter count of the fitting `(a, d)` box.**
Grouping the fitting pairs by their step `d` and counting admissible first terms
`a` fiberwise (`card_filter_lt`) yields the triangular sum `∑_{d=1}^{n} (n-(k-1)d)`
— the precise number of `(a, d)` parameters, sharpening the base entry's loose
`n²` overcount. -/
theorem vdwFilter_card_eq_sum (N k : ℕ) :
    (((Finset.range N) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => p.1 + (k - 1) * p.2 < N)).card
      = ∑ d ∈ Finset.Icc 1 N, (N - (k - 1) * d) := by
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [← Finset.card_filter]
  exact card_filter_lt N ((k - 1) * d)

/-- **Family bounded by the exact parameter sum.** The AP family is the image of
the fitting `(a, d)` box, so its cardinality is at most the exact box count. -/
theorem card_vdwFamily_le_sum (k : ℕ) :
    (vdwFamily n k).card ≤ ∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d) := by
  refine le_trans ?_ (le_of_eq (vdwFilter_card_eq_sum n k))
  rw [vdwFamily]
  exact Finset.card_image_le

/-- **Telescoping-of-squares bound on the triangular sum.**
For every cutoff `m` and step `c`,
`2c·∑_{d=1}^{m}(N - c·d) + (N - c·m)² ≤ N²`.
The square slack telescopes: `2c(N-cd) ≤ (N-c(d-1))² - (N-cd)²`, so the partial
sums stay below `N²`.  Specialising `m = c = ` the relevant values gives the family
bound. -/
theorem two_mul_sum_sq_le (N c m : ℕ) :
    2 * c * (∑ d ∈ Finset.Icc 1 m, (N - c * d)) + (N - c * m) ^ 2 ≤ N ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    -- Per-step square slack: `2c·(N - c(m+1)) + (N - c(m+1))² ≤ (N - c·m)²`.
    have hcm : c * (m + 1) = c * m + c := by ring
    have key : 2 * c * (N - c * (m + 1)) + (N - c * (m + 1)) ^ 2 ≤ (N - c * m) ^ 2 := by
      rcases le_or_gt N (c * (m + 1)) with h | h
      · have hz : N - c * (m + 1) = 0 := by omega
        rw [hz]; simp
      · have hw : N - c * m = (N - c * (m + 1)) + c := by omega
        rw [hw]; nlinarith [sq_nonneg c]
    have hexp : 2 * c * ((∑ d ∈ Finset.Icc 1 m, (N - c * d)) + (N - c * (m + 1)))
              = 2 * c * (∑ d ∈ Finset.Icc 1 m, (N - c * d)) + 2 * c * (N - c * (m + 1)) := by
      rw [Nat.mul_add]
    rw [hexp]
    linarith [ih, key]

/-- **Factor-2 sharpened AP-family bound.** `2·(k-1)·|family| ≤ n²`, i.e. at most
`n²/(2(k-1))` length-`k` APs fit in `[n]`.  This beats the open question's requested
`n²/(k-1)` by a further factor of `2`, and improves the base entry's loose `n²`
count by a factor `2(k-1)`.  (No hypothesis on `k` is needed: for `k ≤ 1` the
factor `2(k-1)` is `0` and the bound is vacuous.) -/
theorem card_vdwFamily_two_mul_le (k : ℕ) :
    2 * (k - 1) * (vdwFamily n k).card ≤ n ^ 2 := by
  calc 2 * (k - 1) * (vdwFamily n k).card
      ≤ 2 * (k - 1) * (∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d)) := by
        gcongr
        exact card_vdwFamily_le_sum k
    _ ≤ n ^ 2 := by
        have h := two_mul_sum_sq_le n (k - 1) n
        omega

/-- **Sharpened first-moment van der Waerden lower bound.**
If `n² < 2·(k-1)·2^(k-1)` then there is a 2-colouring of `[n]` under which every
length-`k` arithmetic progression with positive step contains both colours.

This widens the admissible range of `n` by a factor `√(2(k-1))` over the base
`vdw_lower_bound` (which requires `n² < 2^(k-1)`): the factor-2 family count
`2(k-1)·|family| ≤ n²` lets a single cancellation of `2(k-1)` turn the hypothesis
into `|family| < 2^(k-1)`.  The resulting witness is `W(k) ≳ √(2(k-1))·2^((k-1)/2)`. -/
theorem vdw_lower_bound_sharp {k : ℕ} (hk : 2 ≤ k)
    (hnk : n ^ 2 < 2 * (k - 1) * 2 ^ (k - 1)) :
    ∃ c : Fin n → Bool, ∀ a d : ℕ, 1 ≤ d → a + (k - 1) * d < n →
      ¬ Mono (vdwAP n a d k) c := by
  -- Cancel `2(k-1)` from `2(k-1)·|family| ≤ n² < 2(k-1)·2^(k-1)`.
  have hcard : (vdwFamily n k).card < 2 ^ (k - 1) := by
    have h2 : 2 * (k - 1) * (vdwFamily n k).card < 2 * (k - 1) * 2 ^ (k - 1) :=
      lt_of_le_of_lt (card_vdwFamily_two_mul_le k) hnk
    exact lt_of_mul_lt_mul_left h2 (Nat.zero_le _)
  obtain ⟨c, hc⟩ := vdw_two_coloring_exists (by omega) hcard
  refine ⟨c, fun a d hd hb => ?_⟩
  apply hc
  -- The AP `vdwAP n a d k` belongs to the family (same membership as the base).
  rw [vdwFamily, Finset.mem_image]
  refine ⟨(a, d), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  have hdn : d ≤ (k - 1) * d := Nat.le_mul_of_pos_left d (by omega)
  exact ⟨⟨by omega, hd, by omega⟩, hb⟩

/-! ## Exact AP count: the parametrization is injective on the fitting box

The bounds above use `card_vdwFamily_le_sum`, the *inequality* `|family| ≤ ∑ …`,
which only needs `Finset.card_image_le`.  In fact the parametrization
`(a, d) ↦ vdwAP n a d k` is *injective* on the fitting box (for `k ≥ 2`): a length-`k`
AP with positive step is an increasing list, so its first term `a` is the minimum of
the set and its last term `a + (k-1)d` is the maximum.  From the set alone one recovers
both extremes, hence `a` and (cancelling `k-1`) the step `d`.  Injectivity upgrades the
image-cardinality inequality to an **exact count**:

      |{length-`k` APs in [n]}|  =  ∑_{d=1}^{n} (n - (k-1)·d).      (card_vdwFamily_eq_sum)

So the triangular sum is not merely an upper bound on the number of fitting APs — it is
their exact number, and the factor-2 estimate `2(k-1)|family| ≤ n²` is the *exact* count
fed through `two_mul_sum_sq_le`. -/

/-- The first term `↑a` is a point of the AP (the `i = 0` term). -/
theorem vdwAP_mem_first {a d k : ℕ} (hk : 1 ≤ k) :
    (↑a : Fin n) ∈ vdwAP n a d k := by
  rw [vdwAP, Finset.mem_image]
  exact ⟨0, Finset.mem_range.2 (by omega), by simp⟩

/-- The last term `↑(a + (k-1)d)` is a point of the AP (the `i = k-1` term). -/
theorem vdwAP_mem_last {a d k : ℕ} (hk : 1 ≤ k) :
    (↑(a + (k - 1) * d) : Fin n) ∈ vdwAP n a d k := by
  rw [vdwAP, Finset.mem_image]
  exact ⟨k - 1, Finset.mem_range.2 (by omega), rfl⟩

/-- **`↑a` is the minimum.** Every point of a fitting AP is `≥ ↑a`: the `i`-th term has
value `a + i·d ≥ a`, and both stay below `n` so the `Fin n` order matches ℕ order. -/
theorem vdwAP_first_le {a d k : ℕ} (_hd : 1 ≤ d) (hbound : a + (k - 1) * d < n) :
    ∀ x ∈ vdwAP n a d k, (↑a : Fin n) ≤ x := by
  intro x hx
  rw [vdwAP, Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range] at hi
  have hidx : a + i * d < n := by
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  rw [Fin.le_iff_val_le_val, Fin.val_cast_of_lt (by omega : a < n), Fin.val_cast_of_lt hidx]
  omega

/-- **`↑(a + (k-1)d)` is the maximum.** Every point of a fitting AP is `≤ ↑(a+(k-1)d)`:
the `i`-th term has value `a + i·d ≤ a + (k-1)d`, both below `n`. -/
theorem vdwAP_le_last {a d k : ℕ} (_hd : 1 ≤ d) (hbound : a + (k - 1) * d < n) :
    ∀ x ∈ vdwAP n a d k, x ≤ (↑(a + (k - 1) * d) : Fin n) := by
  intro x hx
  rw [vdwAP, Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range] at hi
  have hle : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
  have hidx : a + i * d < n := by omega
  rw [Fin.le_iff_val_le_val, Fin.val_cast_of_lt hidx, Fin.val_cast_of_lt hbound]
  omega

/-- **The parametrization is injective on the fitting box.**
For `k ≥ 2`, distinct fitting pairs `(a, d)` give distinct APs.  Recover `a` as the set's
minimum (`vdwAP_first_le` + `vdwAP_mem_first`) and `a + (k-1)d` as its maximum
(`vdwAP_le_last` + `vdwAP_mem_last`); cancelling `k-1` recovers `d`. -/
theorem vdwFamily_param_injOn {k : ℕ} (hk : 2 ≤ k) :
    Set.InjOn (fun p : ℕ × ℕ => vdwAP n p.1 p.2 k)
      (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
        (fun p => p.1 + (k - 1) * p.2 < n) : Finset (ℕ × ℕ)) := by
  intro p hp q hq hpq
  obtain ⟨a₁, d₁⟩ := p
  obtain ⟨a₂, d₂⟩ := q
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hp hq
  obtain ⟨⟨ha1n, hd1lo, _⟩, hb1⟩ := hp
  obtain ⟨⟨ha2n, hd2lo, _⟩, hb2⟩ := hq
  simp only at hpq
  -- Recover the first term `a` as the common minimum.
  have hmem2_in_1 : (↑a₂ : Fin n) ∈ vdwAP n a₁ d₁ k := by
    rw [hpq]; exact vdwAP_mem_first (by omega)
  have hmem1_in_2 : (↑a₁ : Fin n) ∈ vdwAP n a₂ d₂ k := by
    rw [← hpq]; exact vdwAP_mem_first (by omega)
  have hcasta : (↑a₁ : Fin n) = ↑a₂ :=
    le_antisymm (vdwAP_first_le hd1lo hb1 _ hmem2_in_1)
      (vdwAP_first_le hd2lo hb2 _ hmem1_in_2)
  have ha : a₁ = a₂ := by
    have := congrArg Fin.val hcasta
    rwa [Fin.val_cast_of_lt (by omega : a₁ < n), Fin.val_cast_of_lt (by omega : a₂ < n)] at this
  -- Recover the last term `a + (k-1)d` as the common maximum.
  have hmemL2_in_1 : (↑(a₂ + (k - 1) * d₂) : Fin n) ∈ vdwAP n a₁ d₁ k := by
    rw [hpq]; exact vdwAP_mem_last (by omega)
  have hmemL1_in_2 : (↑(a₁ + (k - 1) * d₁) : Fin n) ∈ vdwAP n a₂ d₂ k := by
    rw [← hpq]; exact vdwAP_mem_last (by omega)
  have hcastL : (↑(a₁ + (k - 1) * d₁) : Fin n) = ↑(a₂ + (k - 1) * d₂) :=
    le_antisymm (vdwAP_le_last hd2lo hb2 _ hmemL1_in_2)
      (vdwAP_le_last hd1lo hb1 _ hmemL2_in_1)
  have hL : a₁ + (k - 1) * d₁ = a₂ + (k - 1) * d₂ := by
    have := congrArg Fin.val hcastL
    rwa [Fin.val_cast_of_lt (by omega), Fin.val_cast_of_lt (by omega)] at this
  -- `a₁ = a₂` and equal last terms ⟹ `(k-1)d₁ = (k-1)d₂` ⟹ `d₁ = d₂`.
  have hd : d₁ = d₂ := by
    have hmul : (k - 1) * d₁ = (k - 1) * d₂ := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  rw [ha, hd]

/-- **Exact count of length-`k` APs in `[n]`.** For `k ≥ 2` the family cardinality is
*exactly* the triangular sum `∑_{d=1}^{n} (n - (k-1)d)` — not merely bounded by it.
This is `card_vdwFamily_le_sum` made an equality via injectivity of the parametrization. -/
theorem card_vdwFamily_eq_sum {k : ℕ} (hk : 2 ≤ k) :
    (vdwFamily n k).card = ∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d) := by
  rw [vdwFamily, Finset.card_image_of_injOn (vdwFamily_param_injOn hk)]
  exact vdwFilter_card_eq_sum n k

/-- **Crude exact lower bound.** Keeping only the step-`1` fiber (the `n - (k-1)` APs with
common difference `1`) gives `n - (k-1) ≤ |family|`.  Paired with the factor-2 upper bound
`2(k-1)|family| ≤ n²`, this shows the AP count is genuinely positive whenever `k - 1 < n`
(so the union-bound regime is non-vacuous); the matching `Θ(n²/(k-1))` lower bound is left
as a follow-up. -/
theorem card_vdwFamily_ge {k : ℕ} (hk : 2 ≤ k) :
    n - (k - 1) ≤ (vdwFamily n k).card := by
  rw [card_vdwFamily_eq_sum hk]
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]; exact ⟨le_refl 1, NeZero.one_le⟩
  calc n - (k - 1) = n - (k - 1) * 1 := by rw [Nat.mul_one]
    _ ≤ ∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d) :=
        Finset.single_le_sum (f := fun d => n - (k - 1) * d) (fun _ _ => Nat.zero_le _) h1

end ProbMethod.VanDerWaerden
