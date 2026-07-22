/-
  Erdős Problem #46 — Small-divisor completeness: unit-fraction representations
  of 1 with arbitrarily large minimum denominator.

  Source: https://erdosproblems.com/46
  Parents: `Proofs/Erdos46Problem.lean` (defines `IsUnitFractionRepr`, the
  divisor-sum bridge `isUnitFractionRepr_of_divisorSum` / `divisorSum_min_gt`,
  and the harmonic block bound `sum_Ico_inv_ge_one`) and
  `Proofs/Erdos18WIP01.lean` (practical numbers: `factorial_practical`, the
  divisor coin-chain `divisor_chain_of_practical`, and the subset-sum engine
  `finset_chain_covers`).

  This file resolves the vein's registered crux — **a representation of exactly
  `1` by distinct unit fractions with every denominator `> N`** — via the
  "practical-number completeness" route recorded as the open next step on the
  divisor-sum bridge:

  * Take `M = (4(N+1))!`.  `M` is practical (`factorial_practical`), so its full
    divisor set is a subset-sum coin chain (`divisor_chain_of_practical`).
  * Restrict to the *small* divisors `D = {d ∣ M : d ≤ M/(N+1)}`.  The chain
    condition for each `d ∈ D` mentions only divisors `< d`, all of which stay
    in `D` — a threshold restriction of a coin chain is again a coin chain
    (`small_divisor_chain`).
  * The cofactors `M/j` for `j` in the harmonic block `[N+2, 4(N+1)]` all lie in
    `D`, and their sum is at least `M · ∑ 1/j ≥ M` (`sum_Ico_inv_ge_one`), so
    `∑ D ≥ M` (`small_divisor_sum_ge`).
  * Hence `finset_chain_covers` produces distinct divisors `T ⊆ D` with
    `∑ T = M` exactly, and the divisor-sum bridge converts the cofactor family
    `{M/d : d ∈ T}` into a unit-fraction representation of `1` whose
    denominators all exceed `N` (`exists_isUnitFractionRepr_min_gt`).

  Consequently every finite set of naturals can be avoided by a representation
  of `1` (`exists_isUnitFractionRepr_disjoint`) — the collision-freeness
  obstruction recorded in the problem knowledge is gone.

  This does NOT touch the genuinely deep monochromatic statement
  (`ErdosProblem46`, Croot 2003), which needs density/covering machinery.  The
  construction here is the colour-free core previously identified as the
  missing crux for disjoint chaining.

  All results are axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/

import Mathlib
import Proofs.Erdos46Problem
import Proofs.Erdos18WIP01

open Finset

namespace Erdos46SmallDivisors

open Erdos18 (finset_chain_covers divisor_chain_of_practical factorial_practical)

/- ## The small-divisor pool

Throughout, `M = (4(N+1))!` and the pool is `D = {d ∣ M : d ≤ M/(N+1)}`. -/

/-- **Threshold restriction preserves the coin chain.**  For practical `M`, the
divisors of `M` that are `≤ B` still satisfy the subset-sum chain condition:
the chain inequality for `d` only involves divisors `< d ≤ B`, and all of those
survive the threshold filter. -/
theorem small_divisor_chain {M B : ℕ} (hM : Erdos18.IsPractical M) :
    ∀ d ∈ M.divisors.filter (· ≤ B),
      d ≤ 1 + ∑ t ∈ (M.divisors.filter (· ≤ B)).filter (· < d), t := by
  intro d hd
  rw [Finset.mem_filter] at hd
  have hfull := divisor_chain_of_practical hM d hd.1
  have hsetseq : (M.divisors.filter (· ≤ B)).filter (· < d)
      = M.divisors.filter (· < d) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro e _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [hsetseq]
  exact hfull

/-- **The small divisors of `(4(N+1))!` sum to at least `M`.**  The cofactors
`M/j` for `j` in the harmonic block `[N+2, 4(N+1)]` are distinct divisors of
`M`, each `≤ M/(N+1)`, and their reciprocal-weighted total is at least
`M · ∑_{j} 1/j ≥ M` by the block bound `sum_Ico_inv_ge_one`. -/
theorem small_divisor_sum_ge (N : ℕ) (hN : 1 ≤ N) :
    (4 * (N + 1)).factorial ≤
      ∑ d ∈ (4 * (N + 1)).factorial.divisors.filter
        (· ≤ (4 * (N + 1)).factorial / (N + 1)), d := by
  set M : ℕ := (4 * (N + 1)).factorial with hM
  have hMpos : 0 < M := Nat.factorial_pos _
  have hMne : M ≠ 0 := hMpos.ne'
  -- the harmonic index block, phrased exactly as in `sum_Ico_inv_ge_one (N+1)`
  set J : Finset ℕ := Finset.Ico ((N + 1) + 1) (4 * (N + 1) + 1) with hJ
  have hJdvd : ∀ j ∈ J, j ∣ M := by
    intro j hj
    rw [hJ, Finset.mem_Ico] at hj
    exact Nat.dvd_factorial (by omega) (by omega)
  have hJpos : ∀ j ∈ J, 0 < j := by
    intro j hj
    rw [hJ, Finset.mem_Ico] at hj
    omega
  -- the cofactor image lands inside the small-divisor pool
  have himsub : J.image (fun j => M / j) ⊆ M.divisors.filter (· ≤ M / (N + 1)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hjdvd := hJdvd j hj
    have hjlo : N + 1 ≤ j := by
      rw [hJ, Finset.mem_Ico] at hj
      omega
    rw [Finset.mem_filter]
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hjdvd, hMne⟩, ?_⟩
    apply (Nat.le_div_iff_mul_le (by omega : 0 < N + 1)).mpr
    calc M / j * (N + 1) ≤ M / j * j := Nat.mul_le_mul (le_refl _) hjlo
      _ = M := Nat.div_mul_cancel hjdvd
  -- the cofactor map is injective on the block
  have hinjJ : ∀ x ∈ J, ∀ y ∈ J, M / x = M / y → x = y := by
    intro x hx y hy h
    have i₁ : M / (M / x) = x := Nat.div_div_self (hJdvd x hx) hMne
    have i₂ : M / (M / y) = y := Nat.div_div_self (hJdvd y hy) hMne
    rw [← i₁, ← i₂, h]
  -- rational lower bound for the image sum
  have hharm := sum_Ico_inv_ge_one (N + 1) (by omega)
  have hcast : ∀ j ∈ J, ((M / j : ℕ) : ℚ) = (M : ℚ) * (1 / (j : ℚ)) := by
    intro j hj
    rw [Nat.cast_div (hJdvd j hj) (by exact_mod_cast (hJpos j hj).ne'), mul_one_div]
  have hQ : (M : ℚ) ≤ ∑ d ∈ J.image (fun j => M / j), (d : ℚ) := by
    rw [Finset.sum_image hinjJ, Finset.sum_congr rfl hcast, ← Finset.mul_sum]
    calc (M : ℚ) = (M : ℚ) * 1 := by ring
      _ ≤ (M : ℚ) * ∑ j ∈ J, 1 / (j : ℚ) :=
          mul_le_mul_of_nonneg_left hharm (by positivity)
  have hNat : M ≤ ∑ d ∈ J.image (fun j => M / j), d := by
    have := hQ
    rw [← Nat.cast_sum] at this
    exact_mod_cast this
  exact le_trans hNat (Finset.sum_le_sum_of_subset himsub)

/- ## The crux: exact representations of 1 with large minimum denominator -/

/-- **Unit-fraction representations of `1` with arbitrarily large minimum
denominator.**  For every `N ≥ 1` there is a finite set `S` of distinct
denominators, all `> N`, with `∑_{n ∈ S} 1/n = 1` exactly.

Construction: `M = (4(N+1))!` is practical, its divisors `≤ M/(N+1)` form a
subset-sum coin chain totalling `≥ M`, so some distinct family of them sums to
`M` exactly; the cofactors of that family are the denominators. -/
theorem exists_isUnitFractionRepr_min_gt (N : ℕ) (hN : 1 ≤ N) :
    ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ ∀ n ∈ S, N < n := by
  set M : ℕ := (4 * (N + 1)).factorial with hM
  have hMpos : 0 < M := Nat.factorial_pos _
  have hMne : M ≠ 0 := hMpos.ne'
  set D : Finset ℕ := M.divisors.filter (· ≤ M / (N + 1)) with hD
  -- coin chain + total ≥ M ⟹ an exact subset-sum hitting M
  have hchain := small_divisor_chain (B := M / (N + 1))
    (factorial_practical (4 * (N + 1)))
  have hDsum : M ≤ ∑ d ∈ D, d := small_divisor_sum_ge N hN
  obtain ⟨T, hTsub, hTsum⟩ := finset_chain_covers D hchain M hDsum
  -- unpack the pool membership facts for the chosen family
  have hTdvd : ∀ d ∈ T, d ∣ M := by
    intro d hd
    have := hTsub hd
    rw [hD, Finset.mem_filter] at this
    exact (Nat.mem_divisors.mp this.1).1
  have hTle : ∀ d ∈ T, d ≤ M / (N + 1) := by
    intro d hd
    have := hTsub hd
    rw [hD, Finset.mem_filter] at this
    exact this.2
  have hTpos : ∀ d ∈ T, 0 < d := by
    intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · exact absurd (Nat.eq_zero_of_zero_dvd (hTdvd 0 hd)) hMne
    · exact hpos
  have hmul : ∀ d ∈ T, (N + 1) * d ≤ M := by
    intro d hd
    have h2 := (Nat.le_div_iff_mul_le (by omega : 0 < N + 1)).mp (hTle d hd)
    rw [Nat.mul_comm]
    exact h2
  have h2d : ∀ d ∈ T, 2 * d ≤ M := by
    intro d hd
    calc 2 * d ≤ (N + 1) * d := Nat.mul_le_mul (by omega) (le_refl d)
      _ ≤ M := hmul d hd
  have hltN : ∀ d ∈ T, N * d < M := by
    intro d hd
    have h1 := hmul d hd
    have hd1 := hTpos d hd
    have hexp : (N + 1) * d = N * d + d := by ring
    rw [hexp] at h1
    omega
  exact ⟨T.image (fun d => M / d),
    isUnitFractionRepr_of_divisorSum (by omega) hTdvd h2d (by simpa using hTsum),
    divisorSum_min_gt hTdvd hltN⟩

/-- **Any finite set can be avoided**: for every finite `S₀ : Finset ℕ` there is
a unit-fraction representation of `1` disjoint from `S₀`.  This removes the
collision-freeness obstruction to disjoint chaining recorded in the problem
knowledge: iterating yields arbitrarily many pairwise-disjoint representations
of `1`. -/
theorem exists_isUnitFractionRepr_disjoint (S₀ : Finset ℕ) :
    ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ Disjoint S₀ S := by
  obtain ⟨S, hS, hmin⟩ := exists_isUnitFractionRepr_min_gt (S₀.sup id + 1) (by omega)
  refine ⟨S, hS, Finset.disjoint_left.mpr ?_⟩
  intro a ha hamem
  have h1 : a ≤ S₀.sup id := Finset.le_sup (f := id) ha
  have h2 := hmin a hamem
  omega

/- ## From `1` to every positive rational

With the crux `exists_isUnitFractionRepr_min_gt` in hand, the disjoint-union
and scaling primitives of the parent file (`isRatFractionRepr_union`,
`isRatFractionRepr_smul`) upgrade "exactly `1`, denominators `> N`" to
"exactly `q`, denominators `> N`" for EVERY positive rational `q`.  This is the
colour-free layer of the Erdős–Graham rational generalization
(`ErdosGraham_rational` with the colouring stripped): the remaining distance
from these results to `ErdosGraham_rational` / `ErdosProblem46` is purely the
monochromatic (Croot 2003) input. -/

/-- Combined avoidance: a representation of `1` whose denominators all exceed
`N` AND which avoids any prescribed finite set `S₀`.  Runs the crux at
threshold `max N (S₀.sup id)`. -/
theorem exists_isUnitFractionRepr_min_gt_disjoint (N : ℕ) (hN : 1 ≤ N)
    (S₀ : Finset ℕ) :
    ∃ S : Finset ℕ, IsUnitFractionRepr S ∧ (∀ n ∈ S, N < n) ∧ Disjoint S₀ S := by
  obtain ⟨S, hS, hmin⟩ :=
    exists_isUnitFractionRepr_min_gt (max N (S₀.sup id)) (hN.trans (le_max_left _ _))
  refine ⟨S, hS, fun n hn => lt_of_le_of_lt (le_max_left _ _) (hmin n hn), ?_⟩
  refine Finset.disjoint_left.mpr fun a ha hamem => ?_
  have h1 : a ≤ S₀.sup id := Finset.le_sup (f := id) ha
  have h2 := hmin a hamem
  have h3 := le_max_right N (S₀.sup id)
  omega

/-- Every positive natural `a` is a sum of distinct unit fractions with all
denominators `> N`: chain `a` pairwise-disjoint representations of `1` via
`isRatFractionRepr_union` and the avoidance lemma. -/
theorem exists_isRatFractionRepr_natCast_min_gt (a N : ℕ) (ha : 1 ≤ a)
    (hN : 1 ≤ N) :
    ∃ S : Finset ℕ, IsRatFractionRepr S (a : ℚ) ∧ ∀ n ∈ S, N < n := by
  induction a, ha using Nat.le_induction with
  | base =>
    obtain ⟨S, hS, hmin⟩ := exists_isUnitFractionRepr_min_gt N hN
    refine ⟨S, ?_, hmin⟩
    rw [Nat.cast_one]
    exact hS
  | succ a ha ih =>
    obtain ⟨S, hS, hSmin⟩ := ih
    obtain ⟨T, hT, hTmin, hdisj⟩ := exists_isUnitFractionRepr_min_gt_disjoint N hN S
    refine ⟨S ∪ T, ?_, fun n hn => ?_⟩
    · have hcast : ((a + 1 : ℕ) : ℚ) = (a : ℚ) + 1 := by push_cast; ring
      rw [hcast]
      exact isRatFractionRepr_union hdisj hS ((isRatFractionRepr_one_iff T).mpr hT)
    · rcases Finset.mem_union.mp hn with h | h
      · exact hSmin n h
      · exact hTmin n h

/-- **Colour-free Erdős–Graham layer.**  Every positive rational `q` has a
representation by distinct unit fractions with all denominators `> N`: write
`q = q.num / q.den`, represent the positive natural `q.num.toNat` with
denominators `> N`, and scale every denominator by `q.den`
(`isRatFractionRepr_smul`). -/
theorem exists_isRatFractionRepr_pos_min_gt (q : ℚ) (hq : 0 < q) (N : ℕ)
    (hN : 1 ≤ N) :
    ∃ S : Finset ℕ, IsRatFractionRepr S q ∧ ∀ n ∈ S, N < n := by
  have hnum : (0 : ℤ) < q.num := Rat.num_pos.mpr hq
  have hapos : 1 ≤ q.num.toNat := by omega
  have hbpos : 0 < q.den := Nat.pos_of_ne_zero q.den_nz
  obtain ⟨S, hS, hmin⟩ :=
    exists_isRatFractionRepr_natCast_min_gt q.num.toNat N hapos hN
  refine ⟨S.image (fun n => q.den * n), ?_, fun m hm => ?_⟩
  · have hsmul := isRatFractionRepr_smul hS hbpos
    have hcast : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
    rw [hcast, Rat.num_div_den q] at hsmul
    exact hsmul
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact lt_of_lt_of_le (hmin n hn) (Nat.le_mul_of_pos_left n hbpos)

/-- **Egyptian-fraction representability of every positive rational** — the
qualitative Fibonacci–Sylvester theorem, obtained here from the
practical-number engine rather than the greedy algorithm: every `q > 0` is a
finite sum of distinct unit fractions (denominators `≥ 2`). -/
theorem exists_isRatFractionRepr_of_pos (q : ℚ) (hq : 0 < q) :
    ∃ S : Finset ℕ, IsRatFractionRepr S q :=
  let ⟨S, hS, _⟩ := exists_isRatFractionRepr_pos_min_gt q hq 1 le_rfl
  ⟨S, hS⟩

/-- Arbitrarily many pairwise-disjoint representations of `1`: for every `k`
there is a `Fin k`-indexed family of pairwise-disjoint unit-fraction
representations of `1` — the colour-free skeleton of
`ErdosProblem46_infinitely_many`. -/
theorem exists_pairwise_disjoint_isUnitFractionRepr (k : ℕ) :
    ∃ F : Fin k → Finset ℕ, (∀ i, IsUnitFractionRepr (F i)) ∧
      ∀ i j, i ≠ j → Disjoint (F i) (F j) := by
  induction k with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨F, hF, hdisj⟩ := ih
    obtain ⟨T, hT, hTdisj⟩ :=
      exists_isUnitFractionRepr_disjoint (Finset.univ.biUnion F)
    have hsub : ∀ j : Fin k, F j ⊆ Finset.univ.biUnion F := fun j =>
      Finset.subset_biUnion_of_mem F (Finset.mem_univ j)
    refine ⟨Fin.cons T F, fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact hT
      | succ i => rw [Fin.cons_succ]; exact hF i
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          rw [Fin.cons_zero, Fin.cons_succ]
          exact (Finset.disjoint_of_subset_left (hsub j) hTdisj).symm
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          rw [Fin.cons_succ, Fin.cons_zero]
          exact Finset.disjoint_of_subset_left (hsub i) hTdisj
        | succ j =>
          rw [Fin.cons_succ, Fin.cons_succ]
          exact hdisj i j fun h => hij (congrArg Fin.succ h)

end Erdos46SmallDivisors
