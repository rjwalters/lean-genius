/-
  Exact enumeration of the fitting van der Waerden AP family
  (open question van-der-waerden-first-moment-oq-01-oq-01)

  The sibling entry `Proofs.VanDerWaerdenFirstMomentOQ01` sharpens the base
  first-moment count: it bounds the length-`k` AP family by the exact parameter
  sum

        |vdwFamily n k|  ≤  ∑_{d=1}^{n} (n - (k-1)·d)         (`card_vdwFamily_le_sum`)

  via `Finset.card_image_le` — the family is the *image* of the fitting parameter
  box `{(a,d) : a + (k-1)d < n}` under `(a,d) ↦ vdwAP n a d k`, and an image can
  only shrink the count.  The open question this file answers: **is that inequality
  an equality?**  Equivalently, is the parametrization `(a, d) ↦ AP` injective on
  the fitting box — does every fitting `(a, d)` give a *distinct* progression?

  It does, for `k ≥ 2`.  A fitting AP `{a, a+d, …, a+(k-1)d}` has no wraparound in
  `Fin n` (all terms are `< n`), so reading off its **least** element recovers the
  first term `a`, and its **greatest** element recovers `a + (k-1)d`; with `k ≥ 2`
  the factor `k-1 ≥ 1` then recovers the step `d`.  Hence the map is injective and

        |vdwFamily n k|  =  ∑_{d=1}^{n} (n - (k-1)·d)         (`card_vdwFamily_eq_sum`)

  — the sibling's upper bound is **tight**.  This is the matching *lower* bound the
  gallery previously lacked: the family has *exactly* the triangular parameter
  count, not merely at most it.  A clean closed-form consequence is the lower bound
  `n - (k-1) ≤ |vdwFamily n k|` (`card_vdwFamily_ge`), the `d = 1` slice of length-`k`
  intervals.

  The recovery is phrased without `Finset.min'`/`max'` machinery: an element is the
  least exactly when it is a member below every member, a property transported
  across the equality of two AP sets directly.

  Status: 0 sorries, 0 axioms, no `native_decide`.  #print axioms reports only
  `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.VanDerWaerdenFirstMoment
import Proofs.VanDerWaerdenFirstMomentOQ01

namespace ProbMethod.VanDerWaerden

open Finset
open scoped BigOperators
open scoped Fin.NatCast

variable {n : ℕ} [NeZero n]

/-! ## Endpoint recovery for a fitting arithmetic progression

A fitting AP (`a + (k-1)d < n`) has all terms below `n`, so casting to `Fin n`
introduces no wraparound and the `Fin n` order coincides with the natural order on
the terms.  We isolate the two endpoints: the first term `a` is a member below
every member, and the last term `a + (k-1)d` is a member above every member. -/

/-- The first term `a` is a member of the AP (the `i = 0` term). -/
private theorem vdwAP_fst_mem {a d k : ℕ} (hk : 1 ≤ k) :
    (Nat.cast a : Fin n) ∈ vdwAP n a d k := by
  rw [vdwAP, Finset.mem_image]
  exact ⟨0, Finset.mem_range.mpr hk, by simp⟩

/-- The first term `a` is `≤` every member of a fitting AP: each term `a + i·d`
is a natural `< n`, so the `Fin n` casts compare as naturals. -/
private theorem vdwAP_fst_le {a d k : ℕ} (hk : 1 ≤ k) (hbound : a + (k - 1) * d < n) :
    ∀ y ∈ vdwAP n a d k, (Nat.cast a : Fin n) ≤ y := by
  intro y hy
  rw [vdwAP, Finset.mem_image] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  rw [Finset.mem_range] at hi
  have hbi : a + i * d < n := by
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  have han : a < n := by
    have : a ≤ a + (k - 1) * d := Nat.le_add_right _ _
    omega
  rw [Fin.le_def, Fin.val_cast_of_lt han, Fin.val_cast_of_lt hbi]
  omega

/-- The last term `a + (k-1)d` is a member of the AP (the `i = k-1` term). -/
private theorem vdwAP_last_mem {a d k : ℕ} (hk : 1 ≤ k) :
    (Nat.cast (a + (k - 1) * d) : Fin n) ∈ vdwAP n a d k := by
  rw [vdwAP, Finset.mem_image]
  exact ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩

/-- The last term `a + (k-1)d` is `≥` every member of a fitting AP. -/
private theorem vdwAP_last_ge {a d k : ℕ} (hbound : a + (k - 1) * d < n) :
    ∀ y ∈ vdwAP n a d k, y ≤ (Nat.cast (a + (k - 1) * d) : Fin n) := by
  intro y hy
  rw [vdwAP, Finset.mem_image] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  rw [Finset.mem_range] at hi
  have hile : i ≤ k - 1 := by omega
  have hbi : a + i * d < n := by
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d hile
    omega
  have hid : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d hile
  rw [Fin.le_def, Fin.val_cast_of_lt hbi, Fin.val_cast_of_lt hbound]
  omega

/-! ## Injectivity of the parametrization on the fitting box -/

/-- **The fitting parametrization is injective.** On the parameter box
`{(a, d) ∈ [0,n) × [1,n] : a + (k-1)d < n}`, the map `(a, d) ↦ vdwAP n a d k` is
injective for `k ≥ 2`: from the AP set one recovers its least element `a` and its
greatest element `a + (k-1)d`, and `k - 1 ≥ 1` then recovers `d`. -/
private theorem vdwAP_injOn (k : ℕ) (hk : 2 ≤ k) :
    Set.InjOn (fun p : ℕ × ℕ => vdwAP n p.1 p.2 k)
      ↑(((Finset.range n) ×ˢ (Finset.Icc 1 n)).filter
          (fun p => p.1 + (k - 1) * p.2 < n)) := by
  intro p hp q hq hpq
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_Icc] at hp hq
  obtain ⟨⟨hpa, _hpd1, _⟩, hpb⟩ := hp
  obtain ⟨⟨hqa, _hqd1, _⟩, hqb⟩ := hq
  have hk1 : 1 ≤ k := by omega
  change vdwAP n p.1 p.2 k = vdwAP n q.1 q.2 k at hpq
  -- Recover the first term: `↑p.1 = ↑q.1`.
  have hqa_in_p : (Nat.cast q.1 : Fin n) ∈ vdwAP n p.1 p.2 k := by
    rw [hpq]; exact vdwAP_fst_mem hk1
  have hpa_in_q : (Nat.cast p.1 : Fin n) ∈ vdwAP n q.1 q.2 k := by
    rw [← hpq]; exact vdwAP_fst_mem hk1
  have h1 : (Nat.cast p.1 : Fin n) ≤ (Nat.cast q.1 : Fin n) := vdwAP_fst_le hk1 hpb _ hqa_in_p
  have h2 : (Nat.cast q.1 : Fin n) ≤ (Nat.cast p.1 : Fin n) := vdwAP_fst_le hk1 hqb _ hpa_in_q
  have hfa : (Nat.cast p.1 : Fin n) = (Nat.cast q.1 : Fin n) := le_antisymm h1 h2
  have ha : p.1 = q.1 := by
    have := congrArg Fin.val hfa
    rwa [Fin.val_cast_of_lt hpa, Fin.val_cast_of_lt hqa] at this
  -- Recover the last term: `↑(p.1+(k-1)p.2) = ↑(q.1+(k-1)q.2)`.
  have hql_in_p : (Nat.cast (q.1 + (k - 1) * q.2) : Fin n) ∈ vdwAP n p.1 p.2 k := by
    rw [hpq]; exact vdwAP_last_mem hk1
  have hpl_in_q : (Nat.cast (p.1 + (k - 1) * p.2) : Fin n) ∈ vdwAP n q.1 q.2 k := by
    rw [← hpq]; exact vdwAP_last_mem hk1
  have h3 : (Nat.cast (p.1 + (k - 1) * p.2) : Fin n) ≤ (Nat.cast (q.1 + (k - 1) * q.2) : Fin n) :=
    vdwAP_last_ge hqb _ hpl_in_q
  have h4 : (Nat.cast (q.1 + (k - 1) * q.2) : Fin n) ≤ (Nat.cast (p.1 + (k - 1) * p.2) : Fin n) :=
    vdwAP_last_ge hpb _ hql_in_p
  have hfl : (Nat.cast (p.1 + (k - 1) * p.2) : Fin n) = (Nat.cast (q.1 + (k - 1) * q.2) : Fin n) :=
    le_antisymm h3 h4
  have hl : p.1 + (k - 1) * p.2 = q.1 + (k - 1) * q.2 := by
    have := congrArg Fin.val hfl
    rwa [Fin.val_cast_of_lt hpb, Fin.val_cast_of_lt hqb] at this
  -- Combine: equal first terms + equal last terms + `k-1 ≥ 1` ⟹ equal steps.
  have hd2 : p.2 = q.2 := by
    have hmul : (k - 1) * p.2 = (k - 1) * q.2 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  exact Prod.ext ha hd2

/-! ## Exact count -/

/-- **Exact enumeration of the fitting AP family.** For `k ≥ 2`, the number of
length-`k` arithmetic progressions fitting in `[n]` is *exactly* the triangular
parameter sum:
`|vdwFamily n k| = ∑_{d=1}^{n} (n - (k-1)·d)`.

This upgrades the sibling `card_vdwFamily_le_sum`'s upper bound to an equality: the
parametrization `(a, d) ↦ AP` is injective (`vdwAP_injOn`), so the image has the
same cardinality as the fitting box, whose size is the triangular sum
(`vdwFilter_card_eq_sum`). -/
theorem card_vdwFamily_eq_sum (k : ℕ) (hk : 2 ≤ k) :
    (vdwFamily n k).card = ∑ d ∈ Finset.Icc 1 n, (n - (k - 1) * d) := by
  rw [vdwFamily, Finset.card_image_of_injOn (vdwAP_injOn k hk)]
  exact vdwFilter_card_eq_sum n k

/-- **Closed-form lower bound on the family size.** Taking just the `d = 1` slice
(the length-`k` intervals `[a, a+k-1]`) shows at least `n - (k-1)` length-`k` APs
fit in `[n]`. Combined with the sibling factor-2 upper bound
`2(k-1)·|family| ≤ n²`, the family size is pinned between `n-(k-1)` and
`n²/(2(k-1))`. -/
theorem card_vdwFamily_ge (k : ℕ) (hk : 2 ≤ k) :
    n - (k - 1) ≤ (vdwFamily n k).card := by
  rw [card_vdwFamily_eq_sum k hk]
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 n :=
    Finset.mem_Icc.mpr ⟨le_refl 1, Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)⟩
  have := Finset.single_le_sum (f := fun d => n - (k - 1) * d)
    (fun i _ => Nat.zero_le _) h1
  simpa using this

end ProbMethod.VanDerWaerden
