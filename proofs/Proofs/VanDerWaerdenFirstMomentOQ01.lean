/-
  Sharpening the AP-family count in the van der Waerden first-moment lower bound
  (open question van-der-waerden-first-moment-oq-01)

  The base entry `Proofs.VanDerWaerdenFirstMoment` bounds the number of length-`k`
  arithmetic progressions that fit in `[n]` by the deliberately loose count `n²`
  (`card_vdwFamily_le`): it allows every pair `(a, d)` of first term and step.
  That gives the clean union-bound threshold `n² < 2^(k-1)`, i.e.
  `W(k) ≳ 2^((k-1)/2)`.

  But the step `d` is heavily constrained.  For a length-`k` AP to fit we need
  `a + (k-1)d < n`, and since `a ≥ 0` this already forces

        (k-1)·d  <  n,      hence   d ≤ (n-1)/(k-1).

  So the step ranges over only `(n-1)/(k-1)` values, not `n`.  Intersecting the
  `(a, d)`-parameter box with this sharper step range improves the family bound by
  a full factor of `(k-1)`:

        |family|              ≤ n · ⌊(n-1)/(k-1)⌋          (card_vdwFamily_le_div)
        |family| · (k-1)      ≤ n · (n-1)                  (card_vdwFamily_mul_le)

  i.e. at most `n(n-1)/(k-1) < n²/(k-1)` APs fit — exactly the `~n²/(k-1)` count
  the open question asks for.  Feeding this back through the verified Property-B
  engine widens the admissible range of `n` from `n² < 2^(k-1)` to

        n(n-1) < (k-1)·2^(k-1)        (vdw_lower_bound_sharp)

  a factor-`√(k-1)` improvement, giving `W(k) ≳ √(k-1)·2^((k-1)/2)`.

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

/-- **Sharper AP-family bound via the step constraint.**
A fitting length-`k` AP (`k ≥ 2`) has step `d ≤ (n-1)/(k-1)`: from
`a + (k-1)d < n` and `a ≥ 0` we get `(k-1)d < n`, hence `d ≤ (n-1)/(k-1)`.
Restricting the `(a, d)`-parameter box to this step range bounds the family by
`n · ⌊(n-1)/(k-1)⌋`, a factor-`(k-1)` improvement on the base `n²` count. -/
theorem card_vdwFamily_le_div {k : ℕ} (hk : 2 ≤ k) :
    (vdwFamily n k).card ≤ n * ((n - 1) / (k - 1)) := by
  have hk1 : 0 < k - 1 := by omega
  calc (vdwFamily n k).card
      ≤ (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
          (fun p => p.1 + (k - 1) * p.2 < n)).card := Finset.card_image_le
    _ ≤ ((Finset.range n) ×ˢ (Finset.Icc 1 ((n - 1) / (k - 1)))).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at hp
        obtain ⟨⟨ha, hd1, _hdn⟩, hbound⟩ := hp
        have hX : (k - 1) * p.2 < n := by omega
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
        refine ⟨ha, hd1, ?_⟩
        rw [Nat.le_div_iff_mul_le hk1, Nat.mul_comm]
        omega
    _ = n * ((n - 1) / (k - 1)) := by
        rw [Finset.card_product, Finset.card_range, Nat.card_Icc,
          Nat.add_sub_cancel]

/-- **Division-free sharpened count.** `|family| · (k-1) ≤ n(n-1)`, i.e. at most
`n(n-1)/(k-1) < n²/(k-1)` length-`k` APs fit in `[n]` — a factor-`(k-1)`
improvement on the base entry's loose `n²` bound. -/
theorem card_vdwFamily_mul_le {k : ℕ} (hk : 2 ≤ k) :
    (vdwFamily n k).card * (k - 1) ≤ n * (n - 1) := by
  calc (vdwFamily n k).card * (k - 1)
      ≤ (n * ((n - 1) / (k - 1))) * (k - 1) := by
        gcongr
        exact card_vdwFamily_le_div hk
    _ = n * (((n - 1) / (k - 1)) * (k - 1)) := by ring
    _ ≤ n * (n - 1) := by
        gcongr
        exact Nat.div_mul_le_self _ _

/-- **Sharpened first-moment van der Waerden lower bound.**
If `n(n-1) < (k-1)·2^(k-1)` then there is a 2-colouring of `[n]` under which every
length-`k` arithmetic progression with positive step contains both colours.

This widens the admissible range of `n` by a factor `√(k-1)` over the base
`vdw_lower_bound` (which requires `n² < 2^(k-1)`): the sharper family count
`|family|·(k-1) ≤ n(n-1)` lets a single cancellation of `(k-1)` turn the
hypothesis into `|family| < 2^(k-1)`.  The resulting witness is
`W(k) ≳ √(k-1)·2^((k-1)/2)`. -/
theorem vdw_lower_bound_sharp {k : ℕ} (hk : 2 ≤ k)
    (hnk : n * (n - 1) < (k - 1) * 2 ^ (k - 1)) :
    ∃ c : Fin n → Bool, ∀ a d : ℕ, 1 ≤ d → a + (k - 1) * d < n →
      ¬ Mono (vdwAP n a d k) c := by
  have hk1 : 0 < k - 1 := by omega
  -- Cancel (k-1) from |family|·(k-1) ≤ n(n-1) < (k-1)·2^(k-1).
  have hcard : (vdwFamily n k).card < 2 ^ (k - 1) := by
    have h1 : (vdwFamily n k).card * (k - 1) < 2 ^ (k - 1) * (k - 1) := by
      have := lt_of_le_of_lt (card_vdwFamily_mul_le hk) hnk
      rwa [Nat.mul_comm (k - 1) (2 ^ (k - 1))] at this
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
  obtain ⟨c, hc⟩ := vdw_two_coloring_exists (by omega) hcard
  refine ⟨c, fun a d hd hb => ?_⟩
  apply hc
  -- The AP `vdwAP n a d k` belongs to the family (same membership as the base).
  rw [vdwFamily, Finset.mem_image]
  refine ⟨(a, d), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  have hdn : d ≤ (k - 1) * d := Nat.le_mul_of_pos_left d (by omega)
  exact ⟨⟨by omega, hd, by omega⟩, hb⟩

/-! ### The AP-family count is exact

The bounds above (`card_vdwFamily_le_div`) are *inequalities*: they cap the family
size by `n · ⌊(n-1)/(k-1)⌋`, which over-counts because for a fixed step `d` the
first term `a` ranges only over `n - (k-1)d` values, not all of `n`.  We now show
the `(a, d)`-parametrisation is in fact a **bijection** onto the family — distinct
admissible pairs give distinct progressions — so the family count is *exactly* the
number of fitting `(a, d)` pairs, which evaluates to the closed sum

      |vdwFamily(n, k)|  =  ∑_{d=1}^{⌊(n-1)/(k-1)⌋} (n - (k-1)·d).

This upgrades the open question's `≤ n²/(k-1)` to an equality and pins down the
first-moment AP count precisely. -/

/-- **Membership in `vdwAP`.** A point lies in the length-`k` AP exactly when it is
`a + i·d` (cast into `Fin n`) for some index `i < k`. -/
theorem mem_vdwAP {a d k : ℕ} {x : Fin n} :
    x ∈ vdwAP n a d k ↔ ∃ i, i < k ∧ ((a + i * d : ℕ) : Fin n) = x := by
  unfold vdwAP
  simp only [Finset.mem_image, Finset.mem_range]

/-- **The `(a, d)`-parametrisation is injective on fitting pairs (`k ≥ 2`).**
A length-`≥ 2` arithmetic progression determines its first term (its least element,
recovered at `i = 0`) and its step (the gap to the next element, recovered at
`i = 1`): if two admissible pairs yield the same AP, comparing least elements forces
`a = a'`, and then comparing the second elements forces `i·d' = d` and `j·d = d'` for
indices `i, j < k`, whence `(i·j)·d = d`, so `i = j = 1` and `d = d'`. -/
theorem vdwFamily_param_injOn {k : ℕ} (hk : 2 ≤ k) :
    Set.InjOn (fun p : ℕ × ℕ => vdwAP n p.1 p.2 k)
      (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
        (fun p => p.1 + (k - 1) * p.2 < n) : Finset (ℕ × ℕ)) := by
  -- An in-range natural cast into `Fin n` is injective.
  have castinj : ∀ x y : ℕ, x < n → y < n → ((x : Fin n) = (y : Fin n)) → x = y := by
    intro x y hx hy h
    have := congrArg Fin.val h
    rwa [Fin.val_cast_of_lt hx, Fin.val_cast_of_lt hy] at this
  -- Every term `a + i·d` of a fitting AP stays below `n`.
  have hterm : ∀ b e : ℕ, b + (k - 1) * e < n → ∀ i, i < k → b + i * e < n := by
    intro b e hbe i hi
    have : i * e ≤ (k - 1) * e := Nat.mul_le_mul_right e (by omega)
    omega
  intro p hp q hq hpq
  obtain ⟨a, d⟩ := p
  obtain ⟨a', d'⟩ := q
  simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_Icc, Set.mem_setOf_eq] at hp hq
  obtain ⟨⟨hpa, hpd1, _hpdn⟩, hpb⟩ := hp
  obtain ⟨⟨hqa, hqd1, _hqdn⟩, hqb⟩ := hq
  dsimp only at hpq
  -- Step 1: `a = a'` by comparing least elements (index 0).
  have ha_le : a ≤ a' := by
    -- `a'` is the least element of `vdwAP n a' d' k = vdwAP n a d k`, so `a' = a + i·d`.
    have hmem : ((a' : ℕ) : Fin n) ∈ vdwAP n a' d' k := by
      rw [mem_vdwAP]; exact ⟨0, by omega, by simp⟩
    rw [← hpq, mem_vdwAP] at hmem
    obtain ⟨i, hi, hival⟩ := hmem
    have hb : a + i * d < n := hterm a d hpb i hi
    have := castinj _ _ hb hqa hival
    omega
  have ha_ge : a' ≤ a := by
    -- `a` is the least element of `vdwAP n a d k = vdwAP n a' d' k`, so `a = a' + i·d'`.
    have hmem : ((a : ℕ) : Fin n) ∈ vdwAP n a d k := by
      rw [mem_vdwAP]; exact ⟨0, by omega, by simp⟩
    rw [hpq, mem_vdwAP] at hmem
    obtain ⟨i, hi, hival⟩ := hmem
    have hb : a' + i * d' < n := hterm a' d' hqb i hi
    have := castinj _ _ hb hpa hival
    omega
  have haa : a = a' := le_antisymm ha_le ha_ge
  subst haa
  -- Step 2: `d = d'` by comparing second elements (index 1).
  have hkpos : (1 : ℕ) < k := by omega
  have hi_eq : ∃ i, i < k ∧ a + i * d' = a + d := by
    have hmem : ((a + 1 * d : ℕ) : Fin n) ∈ vdwAP n a d k := by
      rw [mem_vdwAP]; exact ⟨1, hkpos, rfl⟩
    rw [hpq, mem_vdwAP] at hmem
    obtain ⟨i, hi, hival⟩ := hmem
    have hb1 : a + i * d' < n := hterm a d' hqb i hi
    have hb2 : a + 1 * d < n := by have := hterm a d hpb 1 hkpos; simpa using this
    refine ⟨i, hi, ?_⟩
    have := castinj _ _ hb1 hb2 hival
    simpa using this
  have hj_eq : ∃ j, j < k ∧ a + j * d = a + d' := by
    have hmem : ((a + 1 * d' : ℕ) : Fin n) ∈ vdwAP n a d' k := by
      rw [mem_vdwAP]; exact ⟨1, hkpos, rfl⟩
    rw [← hpq, mem_vdwAP] at hmem
    obtain ⟨j, hj, hjval⟩ := hmem
    have hb1 : a + j * d < n := hterm a d hpb j hj
    have hb2 : a + 1 * d' < n := by have := hterm a d' hqb 1 hkpos; simpa using this
    refine ⟨j, hj, ?_⟩
    have := castinj _ _ hb1 hb2 hjval
    simpa using this
  obtain ⟨i, _hi, hid⟩ := hi_eq
  obtain ⟨j, _hj, hjd⟩ := hj_eq
  have hid' : i * d' = d := by omega
  have hjd' : j * d = d' := by omega
  have hij : (i * j) * d = 1 * d := by
    have : (i * j) * d = i * (j * d) := by ring
    rw [this, hjd', hid', one_mul]
  have hij1 : i * j = 1 := Nat.eq_of_mul_eq_mul_right (by omega) hij
  have hi1 : i = 1 := Nat.dvd_one.mp ⟨j, hij1.symm⟩
  have hdd : d = d' := by rw [← hid', hi1, one_mul]
  rw [hdd]

/-- **The AP family is in bijection with the fitting `(a, d)` pairs (`k ≥ 2`),**
hence its cardinality equals the number of such pairs. -/
theorem card_vdwFamily_eq {k : ℕ} (hk : 2 ≤ k) :
    (vdwFamily n k).card =
      (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
        (fun p => p.1 + (k - 1) * p.2 < n)).card := by
  unfold vdwFamily
  exact Finset.card_image_of_injOn (vdwFamily_param_injOn hk)

omit [NeZero n] in
/-- **The fitting-pair count is a closed sum over the step.** For each step `d` the
first term ranges over the `n - (k-1)d` values with `a + (k-1)d < n`. -/
theorem card_fitting_pairs (k : ℕ) :
    (((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
        (fun p => p.1 + (k - 1) * p.2 < n)).card
      = ∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d) := by
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.card_filter]
  have hrw : (Finset.range n).filter (fun a => a + (k - 1) * d < n)
        = Finset.range (n - (k - 1) * d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hrw, Finset.card_range]

/-- **Exact AP-family count (`k ≥ 2`).** Combining the bijection with the closed
sum: the number of length-`k` arithmetic progressions fitting in `[n]` is exactly
`∑_{d=1}^{n} (n - (k-1)d)` (terms with `(k-1)d ≥ n` contributing `0`). -/
theorem card_vdwFamily_eq_sum {k : ℕ} (hk : 2 ≤ k) :
    (vdwFamily n k).card = ∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d) := by
  rw [card_vdwFamily_eq hk, card_fitting_pairs]

/-- **Exact AP-family count over the admissible step range.** The same exact count,
with the sum restricted to the genuinely admissible steps `1 ≤ d ≤ ⌊(n-1)/(k-1)⌋`
(the only `d` for which any AP fits); beyond this range every term vanishes. -/
theorem card_vdwFamily_eq_sum_div {k : ℕ} (hk : 2 ≤ k) :
    (vdwFamily n k).card
      = ∑ d ∈ Finset.Icc 1 ((n - 1) / (k - 1)), (n - (k - 1) * d) := by
  have hk1 : 0 < k - 1 := by omega
  rw [card_vdwFamily_eq_sum hk]
  symm
  apply Finset.sum_subset
  · intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 (le_trans (Nat.div_le_self _ _) (by omega))⟩
  · intro d hd hdnot
    rw [Finset.mem_Icc] at hd
    rw [Finset.mem_Icc, not_and] at hdnot
    have hdD : (n - 1) / (k - 1) < d := by
      have := hdnot hd.1
      omega
    have : n - 1 < d * (k - 1) := (Nat.div_lt_iff_lt_mul hk1).mp hdD
    have : n ≤ (k - 1) * d := by
      rw [Nat.mul_comm]; omega
    omega

end ProbMethod.VanDerWaerden
