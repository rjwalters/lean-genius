import Proofs.Erdos1204Problem
import Proofs.Erdos1204A4
import Proofs.Erdos1204A5

/-
# Erdős #1204 — the second extremal quantity `B(k)`

Problem #1204 asks about *two* extremal quantities of admissible `k`-tuples
`0 ≤ a₁ < ⋯ < a_k`:

* `A(k) = min a_k` — the minimal *largest* element (formalized in
  `Erdos1204Problem.lean`, with exact values `A(2)=2, …, A(7)=20`), and
* `B(k) = min (a₁ + ⋯ + a_k)/k` — the minimal *average* element.

Every prior session worked on `A(k)`; the average `B(k)` was untouched. This file
introduces `B(k)` in Lean and establishes its basic theory, mirroring the `A(k)`
development.

The natural carrier is the **minimal sum**
`S(k) = min (a₁ + ⋯ + a_k)` over admissible `k`-sets, an `ℕ`-valued object;
then `B(k) = S(k)/k`. (Translating an admissible set down to start at `0`
preserves admissibility and only decreases the sum, so the minimum is attained
by a set with least element `0`; the `sInf` handles this automatically.)

**What is proved here (all `0` axioms / `0` sorries):**

* `S`, `B` defined; the defining family is nonempty and the infimum attained
  (`S_mem`), with `S(k)` a genuine lower bound on every admissible sum (`S_le`).
* **General lower bound** `k·(k-1) ≤ S(k)`, equivalently `k-1 ≤ B(k)`
  (`sub_mul_le_S`, `sub_one_le_B`). This is the sum-analogue of the diameter
  bound `2(k-1) ≤ A(k)`: the prime `2` forces every admissible set to be
  single-parity, so its `k` distinct elements, translated to start at `0`, are
  `≥ 0, 2, 4, …, 2(k-1)`, whose sum is `k(k-1)`. Proved by strong induction
  removing the maximum, reusing `admissible_two_mul_card_sub_one_le_sup`.
* **Exact small values** `S(0)=S(1)=0`, `S(2)=2` (so `B(2)=1`, where the general
  bound is *tight*), `S(3)=8` (so `B(3)=8/3`) — the first place the average
  is forced strictly above the parity floor `k-1=2`, by the same mod-`3`
  obstruction that makes `A(3)=6` — and `S(4)=16` (so `B(4)=4`), via the bootstrap
  `S(k) ≥ A(k) + S(k-1)` off the already-proven `A(4)=8`.

The asymptotic estimate for `B(k)` (like `A(k) ∼ k log k`) needs sieve theory and
remains **OPEN**; it is not asserted here.

Reference: https://erdosproblems.com/1204
-/

namespace Erdos1204

open Finset

/- ## The minimal admissible sum -/

/-- **General lower bound on the admissible sum.** Every admissible set has
`a.sum id ≥ card·(card-1)`. Proof by strong induction on `a`: remove the maximum
`M`, which satisfies `M ≥ 2(card-1)` by the parity diameter bound
(`admissible_two_mul_card_sub_one_le_sup`), and apply the inductive hypothesis to
the (still admissible) remainder of size `card-1`; the arithmetic
`2(k-1) + (k-1)(k-2) = k(k-1)` closes the step. This is the sum-analogue of the
`A(k) ≥ 2(k-1)` diameter bound. -/
theorem admissible_sum_ge : ∀ (a : Finset ℕ), Admissible a →
    a.card * (a.card - 1) ≤ a.sum id := by
  intro a
  induction a using Finset.strongInduction with
  | _ s ih =>
    intro ha
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · -- the maximum element `M`
      set M := s.max' hne with hMdef
      have hMmem : M ∈ s := s.max'_mem hne
      -- `M ≥ 2(card - 1)`: it dominates `s.sup id`, which is `≥ 2(card-1)`
      have hsupM : s.sup id ≤ M :=
        Finset.sup_le (fun x hx => by simpa using s.le_max' x hx)
      have hMge : 2 * (s.card - 1) ≤ M :=
        le_trans (admissible_two_mul_card_sub_one_le_sup ha) hsupM
      -- the remainder `s.erase M` is admissible of size `card - 1`
      have haer : Admissible (s.erase M) := ha.subset (s.erase_subset M)
      have hcarderase : (s.erase M).card = s.card - 1 := Finset.card_erase_of_mem hMmem
      have hih := ih (s.erase M) (Finset.erase_ssubset hMmem) haer
      rw [hcarderase] at hih
      -- split off `M` from the sum
      have hsum : s.sum id = M + (s.erase M).sum id := by
        rw [← Finset.add_sum_erase s id hMmem]; simp
      -- write `card = j + 1` and discharge the nat arithmetic
      obtain ⟨j, hj⟩ : ∃ j, s.card = j + 1 :=
        ⟨s.card - 1, by have := Finset.card_pos.mpr hne; omega⟩
      rw [hj] at hih hMge ⊢
      simp only [Nat.add_sub_cancel] at hih hMge ⊢
      rw [hsum]
      cases j with
      | zero => simp
      | succ c =>
        simp only [Nat.add_sub_cancel] at hih
        nlinarith [hih, hMge]

/-- **`S(k)`**, the minimal sum `a₁ + ⋯ + a_k` over admissible `k`-element sets.
The minimization is over a nonempty family (`exists_admissible_card`), so the
infimum is attained (`S_mem`). `B(k) = S(k)/k` is the minimal average. -/
noncomputable def S (k : ℕ) : ℕ :=
  sInf { m | ∃ a : Finset ℕ, a.card = k ∧ Admissible a ∧ a.sum id = m }

/-- The family of achievable sums is nonempty (an admissible `k`-set always exists). -/
theorem S_set_nonempty (k : ℕ) :
    { m | ∃ a : Finset ℕ, a.card = k ∧ Admissible a ∧ a.sum id = m }.Nonempty := by
  obtain ⟨a, hcard, ha⟩ := exists_admissible_card k
  exact ⟨a.sum id, a, hcard, ha, rfl⟩

/-- The infimum defining `S(k)` is **attained**: there is an admissible `k`-set
whose element sum equals `S(k)`. -/
theorem S_mem (k : ℕ) :
    ∃ a : Finset ℕ, a.card = k ∧ Admissible a ∧ a.sum id = S k :=
  Nat.sInf_mem (S_set_nonempty k)

/-- `S(k)` is a lower bound: any admissible `k`-set has element sum at least `S(k)`. -/
theorem S_le {k : ℕ} {a : Finset ℕ} (hcard : a.card = k) (ha : Admissible a) :
    S k ≤ a.sum id :=
  Nat.sInf_le ⟨a, hcard, ha, rfl⟩

/-- **One-step monotonicity of the minimal sum.** `S(k) ≤ S(k+1)`: deleting one
element from an optimal admissible `(k+1)`-set leaves an admissible `k`-set
(`Admissible.subset`) whose element sum is no larger
(`Finset.sum_le_sum_of_subset`, as all elements are nonnegative), so its sum —
which is `≥ S(k)` — bounds `S(k+1)` from above. The average-analogue of
`A_le_A_succ` from the `A(k)` theory. -/
theorem S_le_S_succ (k : ℕ) : S k ≤ S (k + 1) := by
  obtain ⟨a, hcard, ha, hsum⟩ := S_mem (k + 1)
  have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  obtain ⟨x, hx⟩ := hne
  have hsub : a.erase x ⊆ a := fun y hy => Finset.mem_of_mem_erase hy
  have hcard' : (a.erase x).card = k := by
    rw [Finset.card_erase_of_mem hx, hcard, Nat.add_sub_cancel]
  have ha' : Admissible (a.erase x) := ha.subset hsub
  calc S k ≤ (a.erase x).sum id := S_le hcard' ha'
    _ ≤ a.sum id := Finset.sum_le_sum_of_subset hsub
    _ = S (k + 1) := hsum

/-- **`S` is monotone.** The minimal-sum function `S(k)` is non-decreasing in `k`:
a larger admissible tuple can only need a larger element sum. Immediate from the
one-step bound `S_le_S_succ`; mirrors `A_monotone`. -/
theorem S_monotone : Monotone S :=
  monotone_nat_of_le_succ S_le_S_succ

/-- **General lower bound on `S(k)`: `k·(k-1) ≤ S(k)`.** Immediate from the
attained minimizer and `admissible_sum_ge`. Equivalently `B(k) ≥ k-1`
(`sub_one_le_B`): twice the trivial packing sum, forced by the prime-`2`
single-parity constraint. Sharp at `k = 2` (`S 2 = 2`). -/
theorem sub_mul_le_S (k : ℕ) : k * (k - 1) ≤ S k := by
  obtain ⟨a, hcard, ha, hsum⟩ := S_mem k
  have h := admissible_sum_ge a ha
  rw [hcard, hsum] at h
  exact h

/-- `S(0) = 0` (the only admissible `0`-set is `∅`, with sum `0`). -/
theorem S_zero : S 0 = 0 :=
  Nat.le_zero.mp (by simpa using S_le (a := (∅ : Finset ℕ)) Finset.card_empty admissible_empty)

/-- `S(1) = 0` (the singleton `{0}` is admissible with sum `0`). -/
theorem S_one : S 1 = 0 := by
  refine Nat.le_zero.mp ?_
  simpa using S_le (a := ({0} : Finset ℕ)) (by simp) (admissible_singleton 0)

/-- **`S(2) = 2`.** Upper bound from the witness `{0, 2}` (sum `2`); lower bound
`2 ≤ S 2` is the general parity bound `k(k-1) = 2` (`sub_mul_le_S`), which is
*tight* here — the average `B(2) = 1` equals the parity floor `k - 1 = 1`. -/
theorem S_two : S 2 = 2 := by
  apply le_antisymm
  · have h := S_le (k := 2) (a := ({0, 2} : Finset ℕ)) (by decide) admissible_zero_two
    have hs : ({0, 2} : Finset ℕ).sum id = 2 := by decide
    rwa [hs] at h
  · simpa using sub_mul_le_S 2

/-- **Lower-bound core for `S(3)`.** Every admissible `3`-set has element sum at
least `8`. The maximum `M` is `≥ 6` (`admissible_three_sup_ge`, the `A(3)` lower
bound), and the remaining admissible `2`-set has sum `≥ 2` (`admissible_sum_ge`),
so the total is `≥ 6 + 2 = 8`. Unlike `S(2)`, this exceeds the parity floor
`k(k-1) = 6`: the mod-`3` obstruction that forces `A(3) = 6 > 4` also pushes the
minimal sum from `6` to `8`. -/
theorem admissible_three_sum_ge {a : Finset ℕ} (hcard : a.card = 3)
    (ha : Admissible a) : 8 ≤ a.sum id := by
  have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  set M := a.max' hne with hMdef
  have hMmem : M ∈ a := a.max'_mem hne
  -- `M ≥ 6` from the `A(3)` lower bound `sup ≥ 6`
  have hsup6 : 6 ≤ a.sup id := admissible_three_sup_ge hcard ha
  have hsupM : a.sup id ≤ M :=
    Finset.sup_le (fun x hx => by simpa using a.le_max' x hx)
  have hM6 : 6 ≤ M := le_trans hsup6 hsupM
  -- the erased `2`-set has sum `≥ 2`
  have haer : Admissible (a.erase M) := ha.subset (a.erase_subset M)
  have hcarderase : (a.erase M).card = 2 := by
    rw [Finset.card_erase_of_mem hMmem, hcard]
  have h2 : 2 ≤ (a.erase M).sum id := by
    have h := admissible_sum_ge (a.erase M) haer
    rw [hcarderase] at h
    simpa using h
  have hsum : a.sum id = M + (a.erase M).sum id := by
    rw [← Finset.add_sum_erase a id hMmem]; simp
  omega

/-- **`S(3) = 8`.** Upper bound from the witness `{0, 2, 6}` (sum `8`); lower
bound `8 ≤ S 3` from `admissible_three_sum_ge`. So the minimal average is
`B(3) = 8/3`, strictly above the parity floor `k - 1 = 2`. -/
theorem S_three : S 3 = 8 := by
  apply le_antisymm
  · have h := S_le (k := 3) (a := ({0, 2, 6} : Finset ℕ)) (by decide) admissible_zero_two_six
    have hs : ({0, 2, 6} : Finset ℕ).sum id = 8 := by decide
    rwa [hs] at h
  · obtain ⟨a, hcard, ha, hsum⟩ := S_mem 3
    have hge := admissible_three_sum_ge hcard ha
    omega

/-- **Lower-bound core for `S(4)`.** Every admissible `4`-set has element sum at
least `16`. The maximum `M` is `≥ 8` (`admissible_four_sup_ge`, the `A(4)` lower
bound), and the remaining admissible `3`-set has sum `≥ 8` (`admissible_three_sum_ge`),
so the total is `≥ 8 + 8 = 16`. This continues the bootstrap `S(k) ≥ A(k) + S(k-1)`:
each exact `S(k)` is the `A(k)` sup bound plus the previous minimal sum, needing no
fresh mod-`p` enumeration beyond the already-proven `A(k)` values. -/
theorem admissible_four_sum_ge {a : Finset ℕ} (hcard : a.card = 4)
    (ha : Admissible a) : 16 ≤ a.sum id := by
  have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  set M := a.max' hne with hMdef
  have hMmem : M ∈ a := a.max'_mem hne
  -- `M ≥ 8` from the `A(4)` lower bound `sup ≥ 8`
  have hsup8 : 8 ≤ a.sup id := admissible_four_sup_ge hcard ha
  have hsupM : a.sup id ≤ M :=
    Finset.sup_le (fun x hx => by simpa using a.le_max' x hx)
  have hM8 : 8 ≤ M := le_trans hsup8 hsupM
  -- the erased `3`-set has sum `≥ 8`
  have haer : Admissible (a.erase M) := ha.subset (a.erase_subset M)
  have hcarderase : (a.erase M).card = 3 := by
    rw [Finset.card_erase_of_mem hMmem, hcard]
  have h3 : 8 ≤ (a.erase M).sum id := admissible_three_sum_ge hcarderase haer
  have hsum : a.sum id = M + (a.erase M).sum id := by
    rw [← Finset.add_sum_erase a id hMmem]; simp
  omega

/-- **Lower-bound core for `S(5)`.** Every admissible `5`-set has element sum at least
`28`. The maximum `M` is `≥ 12` (`admissible_five_sup_ge`, the `A(5)` lower bound), and
the remaining admissible `4`-set has sum `≥ 16` (`admissible_four_sum_ge`), so the total
is `≥ 12 + 16 = 28`. The same bootstrap `S(k) ≥ A(k) + S(k-1)` as at `k = 4`, now with the
`A(5) = 12` diameter value. -/
theorem admissible_five_sum_ge {a : Finset ℕ} (hcard : a.card = 5)
    (ha : Admissible a) : 28 ≤ a.sum id := by
  have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  set M := a.max' hne with hMdef
  have hMmem : M ∈ a := a.max'_mem hne
  -- `M ≥ 12` from the `A(5)` lower bound `sup ≥ 12`
  have hsup12 : 12 ≤ a.sup id := admissible_five_sup_ge hcard ha
  have hsupM : a.sup id ≤ M :=
    Finset.sup_le (fun x hx => by simpa using a.le_max' x hx)
  have hM12 : 12 ≤ M := le_trans hsup12 hsupM
  -- the erased `4`-set has sum `≥ 16`
  have haer : Admissible (a.erase M) := ha.subset (a.erase_subset M)
  have hcarderase : (a.erase M).card = 4 := by
    rw [Finset.card_erase_of_mem hMmem, hcard]
  have h4 : 16 ≤ (a.erase M).sum id := admissible_four_sum_ge hcarderase haer
  have hsum : a.sum id = M + (a.erase M).sum id := by
    rw [← Finset.add_sum_erase a id hMmem]; simp
  omega

/-- **`S(5) = 28`.** Upper bound from the witness `{0, 2, 6, 8, 12}` (sum `28`, the
`A(5)` extremal set from `Erdos1204A5.lean`); lower bound `28 ≤ S 5` from
`admissible_five_sum_ge`. So `S(5) = A(5) + S(4) = 12 + 16 = 28` — the bootstrap stays
sharp, and the minimal-diameter set `{0,2,6,8,12}` is again *also* the minimal-sum set
(its sum `28` meets the lower bound exactly), so the min-diameter and min-average optima
continue to coincide at `k = 5`. -/
theorem S_five : S 5 = 28 := by
  apply le_antisymm
  · have h := S_le (k := 5) (a := ({0, 2, 6, 8, 12} : Finset ℕ)) (by decide)
      admissible_witness_five
    have hs : ({0, 2, 6, 8, 12} : Finset ℕ).sum id = 28 := by decide
    rwa [hs] at h
  · obtain ⟨a, hcard, ha, hsum⟩ := S_mem 5
    have hge := admissible_five_sum_ge hcard ha
    omega

/-- **`S(4) = 16`.** Upper bound from the witness `{0, 2, 6, 8}` (sum `16`, the
`A(4)` extremal set); lower bound `16 ≤ S 4` from `admissible_four_sum_ge`. So the
minimal average is `B(4) = 4`, again strictly above the parity floor `k - 1 = 3`. -/
theorem S_four : S 4 = 16 := by
  apply le_antisymm
  · have h := S_le (k := 4) (a := ({0, 2, 6, 8} : Finset ℕ)) (by decide)
      admissible_zero_two_six_eight
    have hs : ({0, 2, 6, 8} : Finset ℕ).sum id = 16 := by decide
    rwa [hs] at h
  · obtain ⟨a, hcard, ha, hsum⟩ := S_mem 4
    have hge := admissible_four_sum_ge hcard ha
    omega

/- ## The minimal average `B(k)` -/

/-- **`B(k) = S(k)/k`**, the minimal average `(a₁ + ⋯ + a_k)/k` over admissible
`k`-element sets — the second extremal quantity of Problem #1204. -/
noncomputable def B (k : ℕ) : ℚ := (S k : ℚ) / k

/-- **General lower bound `B(k) ≥ k - 1`** (for `k ≥ 1`), the average analogue of
`A(k) ≥ 2(k-1)`. Divide the sum bound `k(k-1) ≤ S(k)` by `k`. Sharp at `k = 2`
(`B 2 = 1`). -/
theorem sub_one_le_B (k : ℕ) (hk : 1 ≤ k) : (k : ℚ) - 1 ≤ B k := by
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  rw [B, le_div_iff₀ hkpos]
  have hcast : (((k * (k - 1) : ℕ)) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one]
  have h2 : (k : ℚ) * ((k : ℚ) - 1) ≤ (S k : ℚ) := by
    rw [← hcast]; exact_mod_cast sub_mul_le_S k
  calc ((k : ℚ) - 1) * (k : ℚ) = (k : ℚ) * ((k : ℚ) - 1) := by ring
    _ ≤ (S k : ℚ) := h2

/-- **`B(2) = 1`.** The parity floor `k - 1 = 1` is attained: the densest
admissible `2`-set is `{0, 2}`, average `1`. -/
theorem B_two : B 2 = 1 := by
  rw [B, S_two]; norm_num

/-- **`B(3) = 8/3 ≈ 2.667`.** Strictly above the parity floor `k - 1 = 2`: the
mod-`3` obstruction forces the minimal average up, mirroring `A(3) = 6`. -/
theorem B_three : B 3 = 8 / 3 := by
  rw [B, S_three]; norm_num

/-- **`B(4) = 4`.** From `S(4) = 16`. Like `B(3)`, this sits strictly above the
parity floor `k - 1 = 3`; the extremal set `{0, 2, 6, 8}` (which also realizes
`A(4) = 8`) is here the minimal-sum set as well, so at `k = 4` the min-average and
min-diameter optima still coincide. -/
theorem B_four : B 4 = 4 := by
  rw [B, S_four]; norm_num

/-- **`B(5) = 28/5 = 5.6`.** From `S(5) = 28`. Strictly above the parity floor
`k - 1 = 4`; as at `k = 3, 4` the extremal set `{0,2,6,8,12}` (which also realizes
`A(5) = 12`) is here the minimal-sum set as well, so the min-average and min-diameter
optima still coincide at `k = 5`. -/
theorem B_five : B 5 = 28 / 5 := by
  rw [B, S_five]; norm_num

/-- **Diameter is dominated by sum (pointwise).** For every admissible `k`-set `a`,
the minimal diameter `A(k)` is at most the element sum `∑ a`. The largest element
`a.sup id` is one of the (nonnegative) summands, hence `a.sup id ≤ ∑ a`, and
`A(k) ≤ a.sup id` by definition of `A`. This is the bridge between the two extremal
quantities of Erdős #1204: the diameter side and the sum side. -/
theorem A_le_sum {k : ℕ} {a : Finset ℕ} (hcard : a.card = k) (ha : Admissible a) :
    A k ≤ a.sum id :=
  le_trans (A_le hcard ha)
    (Finset.sup_le fun x hx => Finset.single_le_sum (fun i _ => Nat.zero_le i) hx)

/-- **The minimal diameter is at most the minimal sum: `A(k) ≤ S(k)`.** Instantiating
`A_le_sum` at the sum-minimizer (`S_mem`) shows the diameter extremal `A(k)` never
exceeds the sum extremal `S(k)`. Equivalently `(A k : ℚ) ≤ k · B(k)`, since
`B(k) = S(k)/k`: the least attainable largest-element is bounded by the least
attainable total. -/
theorem A_le_S (k : ℕ) : A k ≤ S k := by
  obtain ⟨a, hcard, ha, hsum⟩ := S_mem k
  rw [← hsum]
  exact A_le_sum hcard ha

/-- **Sum–diameter bootstrap: `A(k+1) + S(k) ≤ S(k+1)`.** Peeling the maximum `M`
off a sum-minimizing admissible `(k+1)`-set splits its total as `M + ∑(rest)`; the
maximum dominates the whole set's largest element, so `M ≥ A(k+1)` (the diameter
lower bound `A_le`), and the remaining admissible `k`-set has sum `≥ S(k)` (`S_le`).
Adding gives `S(k+1) ≥ A(k+1) + S(k)`.

This is the **general form of the recurrence** that the exact-value proofs
`admissible_three_sum_ge` (`A(3)=6`, `S(2)=2 ⟹ S(3)≥8`) and `admissible_four_sum_ge`
(`A(4)=8`, `S(3)=8 ⟹ S(4)≥16`) each instantiate by hand: every exact `S(k)` is the
already-proven diameter value `A(k)` plus the previous minimal sum, needing no fresh
mod-`p` enumeration. Iterated, it yields `S(k) ≥ A(k)+A(k-1)+⋯+A(2)`, sharpening the
parity floor `k(k-1) ≤ S(k)` wherever the `A`-values exceed `2(j-1)`. -/
theorem A_add_S_le_S_succ (k : ℕ) : A (k + 1) + S k ≤ S (k + 1) := by
  obtain ⟨a, hcard, ha, hsum⟩ := S_mem (k + 1)
  have hne : a.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  set M := a.max' hne with hMdef
  have hMmem : M ∈ a := a.max'_mem hne
  -- `M ≥ A(k+1)`: `M` dominates `a.sup id`, which is `≥ A(k+1)` by `A_le`
  have hsupM : a.sup id ≤ M :=
    Finset.sup_le (fun x hx => by simpa using a.le_max' x hx)
  have hAM : A (k + 1) ≤ M := le_trans (A_le hcard ha) hsupM
  -- the erased `k`-set is admissible with sum `≥ S(k)`
  have haer : Admissible (a.erase M) := ha.subset (a.erase_subset M)
  have hcarderase : (a.erase M).card = k := by
    rw [Finset.card_erase_of_mem hMmem, hcard, Nat.add_sub_cancel]
  have hSk : S k ≤ (a.erase M).sum id := S_le hcarderase haer
  -- split the optimal sum off `M`
  have hsplit : a.sum id = M + (a.erase M).sum id := by
    rw [← Finset.add_sum_erase a id hMmem]; simp
  rw [← hsum, hsplit]
  omega

/- ## Open Problem

The asymptotic behaviour of `B(k) = min (a₁ + ⋯ + a_k)/k` over admissible
`k`-tuples is **OPEN** (like `A(k) ∼ k log k`); the exact-value frontier here
(`B(2)=1`, `B(3)=8/3`, …) is bracketed below by the parity bound `B(k) ≥ k-1`.
Estimating `B(k)` requires analytic number theory and is not formalized here. -/

end Erdos1204

#print axioms Erdos1204.admissible_sum_ge
#print axioms Erdos1204.S_three
#print axioms Erdos1204.B_three
#print axioms Erdos1204.sub_one_le_B
#print axioms Erdos1204.S_four
#print axioms Erdos1204.B_four
#print axioms Erdos1204.admissible_five_sum_ge
#print axioms Erdos1204.S_five
#print axioms Erdos1204.B_five
#print axioms Erdos1204.A_le_sum
#print axioms Erdos1204.A_le_S
#print axioms Erdos1204.A_add_S_le_S_succ
