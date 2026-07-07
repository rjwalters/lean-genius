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

/-- **The literal first-moment bound `|family| ≤ n · ⌊(n-1)/(k-1)⌋`** asked for by the
open question, proved directly by bounding the AP step.  A length-`k` AP of step `d`
fits in `[n]` only when `(k-1)·d ≤ n-1`, i.e. `d ≤ ⌊(n-1)/(k-1)⌋`; so there are at most
`⌊(n-1)/(k-1)⌋` admissible steps, each pairing with at most `n` first terms `a`.

This records the exact shape the question states (the chained `≤ n²/(k-1)` is then just
`⌊(n-1)/(k-1)⌋ ≤ (n-1)/(k-1) ≤ n/(k-1)`).  It is **not** dominated by the sharper
telescoping bound `card_vdwFamily_two_mul_le`: in the regime `n ≤ k-1` *no* AP of
positive step fits, and this lemma returns the **exact** value `0` (the floor is `0`),
whereas `n²/(2(k-1))` is strictly positive there. -/
theorem card_vdwFamily_le_floor {k : ℕ} (hk : 2 ≤ k) :
    (vdwFamily n k).card ≤ n * ((n - 1) / (k - 1)) := by
  have hk1 : 0 < k - 1 := by omega
  refine le_trans (card_vdwFamily_le_sum k) ?_
  -- Replace each triangular term by `n` on the support `(k-1)d < n` and `0` off it.
  have hbound : ∀ d ∈ Finset.Icc 1 n,
      n - (k - 1) * d ≤ (if (k - 1) * d < n then n else 0) := by
    intro d _
    split
    · exact Nat.sub_le n _
    · omega
  refine le_trans (Finset.sum_le_sum hbound) ?_
  -- The indicator sum is `n · |{d ∈ Icc 1 n : (k-1)d < n}|`, and that filter is
  -- exactly `Icc 1 ⌊(n-1)/(k-1)⌋`.
  have hfilter : (Finset.Icc 1 n).filter (fun d => (k - 1) * d < n)
      = Finset.Icc 1 ((n - 1) / (k - 1)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      refine ⟨h1, ?_⟩
      rw [Nat.le_div_iff_mul_le hk1]
      have hc : (k - 1) * d = d * (k - 1) := Nat.mul_comm _ _
      omega
    · rintro ⟨h1, h2⟩
      have h2' : d * (k - 1) ≤ n - 1 := (Nat.le_div_iff_mul_le hk1).1 h2
      have hc : (k - 1) * d = d * (k - 1) := Nat.mul_comm _ _
      have hdle : d ≤ (k - 1) * d := Nat.le_mul_of_pos_left d hk1
      exact ⟨⟨h1, by omega⟩, by omega⟩
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, smul_eq_mul,
      Nat.card_Icc, Nat.add_sub_cancel]
  exact le_of_eq (Nat.mul_comm _ n)

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

end ProbMethod.VanDerWaerden

-- Axiom audit: foundational axioms only; no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms ProbMethod.VanDerWaerden.card_vdwFamily_le_floor
