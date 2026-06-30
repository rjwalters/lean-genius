/-
Proof: Irrationality of nth Roots — the full iff characterization
Source problem: sqrt2-irrational-oq-03
  "Can this generalize to √[n]{m}? Yes! √[n]{m} is irrational iff m is not a
   perfect n-th power."

This file answers the open question attached to the √2-irrationality entry by
upgrading the *one-directional* result already in the gallery
(`NthRootIrrational.irrational_nthRoot`, which only gives
"not a perfect power ⟹ irrational") to a complete **iff characterization**:

    Irrational (m ^ (1/n))  ↔  ¬ ∃ k : ℕ, k ^ n = m        (for n ≠ 0).

Mathlib packages the *square-root* case as an iff
(`irrational_sqrt_natCast_iff : Irrational (√n) ↔ ¬IsSquare n`) but provides only
a one-directional lemma for general nth roots (`irrational_nrt_of_notint_nrt`).
We close that gap here.

We additionally reduce the perfect-power test to a **bounded, decidable** search
(`exists_nthPow_iff_bounded`), which lets every concrete instance be discharged by
`decide`. This subsumes the case-by-case enumeration in `NthRootIrrational.lean`
(`two_not_perfect_cube`, `three_not_perfect_cube`, `two_not_perfect_fifth`, …):
each of those becomes a one-line `decide`.

No sorries, no axioms beyond Mathlib's foundations.
-/
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Sqrt2IrrationalOQ03

/- ## The nth root function -/

/-- The real nth root of a natural number `m`, namely `m ^ (1/n)`. -/
noncomputable def nthRoot (n m : ℕ) : ℝ := (m : ℝ) ^ ((n : ℝ)⁻¹)

theorem nthRoot_nonneg (n m : ℕ) : 0 ≤ nthRoot n m :=
  Real.rpow_nonneg (by positivity) _

/-- The defining identity: `(m ^ (1/n)) ^ n = m` for `n ≠ 0`. -/
theorem nthRoot_pow {n : ℕ} (m : ℕ) (hn : n ≠ 0) : nthRoot n m ^ n = m := by
  unfold nthRoot
  exact Real.rpow_inv_natCast_pow (by positivity) hn

/- ## The iff characterization -/

/-- **nth roots: the full characterization.**

For `n ≠ 0`, the real number `m ^ (1/n)` is irrational **iff** `m` is not a perfect
nth power. Both directions are proved:

* (⟸) If no natural `k` has `k ^ n = m`, then `m ^ (1/n)` is irrational
  (via Mathlib's `irrational_nrt_of_notint_nrt`).
* (⟹) If some `k` has `k ^ n = m`, then `m ^ (1/n) = k` is a natural number,
  hence not irrational. -/
theorem irrational_nthRoot_iff {n m : ℕ} (hn : n ≠ 0) :
    Irrational (nthRoot n m) ↔ ¬ ∃ k : ℕ, k ^ n = m := by
  constructor
  · -- irrational ⟹ not a perfect power
    rintro hirr ⟨k, hk⟩
    have hval : nthRoot n m = (k : ℝ) := by
      unfold nthRoot
      rw [← hk]
      push_cast
      exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg k) hn
    rw [hval] at hirr
    exact (Nat.not_irrational k) hirr
  · -- not a perfect power ⟹ irrational
    intro hm
    have hpow : nthRoot n m ^ n = ((m : ℤ) : ℝ) := by
      have := nthRoot_pow m hn; push_cast; push_cast at this; exact this
    apply irrational_nrt_of_notint_nrt n (m : ℤ) hpow _ (Nat.pos_of_ne_zero hn)
    rintro ⟨y, hy⟩
    apply hm
    -- `y` is the integer value of the root; it is nonnegative
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := hy ▸ nthRoot_nonneg n m
    have hyZ : (0 : ℤ) ≤ y := by exact_mod_cast hy0
    -- transport the power identity along `nthRoot n m = y`
    have hyn : (y : ℤ) ^ n = (m : ℤ) := by
      have : ((y : ℝ)) ^ n = ((m : ℤ) : ℝ) := by rw [← hy]; exact hpow
      exact_mod_cast this
    refine ⟨y.toNat, ?_⟩
    have : ((y.toNat : ℤ)) = y := Int.toNat_of_nonneg hyZ
    have : ((y.toNat : ℤ)) ^ n = (m : ℤ) := by rw [this]; exact hyn
    exact_mod_cast this

/- ## Bounded, decidable perfect-power test -/

/-- The unbounded perfect-power existential reduces to a **bounded** one: any witness
`k` with `k ^ n = m` satisfies `k ≤ m` (because `k ≤ k ^ n` for `n ≠ 0`). The
right-hand side is decidable, so concrete instances are settled by `decide`. -/
theorem exists_nthPow_iff_bounded {n : ℕ} (m : ℕ) (hn : n ≠ 0) :
    (∃ k : ℕ, k ^ n = m) ↔ ∃ k ∈ Finset.range (m + 1), k ^ n = m := by
  constructor
  · rintro ⟨k, hk⟩
    have hkm : k ≤ m := by
      calc k ≤ k ^ n := Nat.le_self_pow hn k
        _ = m := hk
    exact ⟨k, Finset.mem_range.mpr (by omega), hk⟩
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- Decidable repackaging: for `n ≠ 0`, irrationality of `m ^ (1/n)` is equivalent to
a decidable bounded search failing. -/
theorem irrational_nthRoot_iff_bounded {n m : ℕ} (hn : n ≠ 0) :
    Irrational (nthRoot n m) ↔ ¬ ∃ k ∈ Finset.range (m + 1), k ^ n = m := by
  rw [irrational_nthRoot_iff hn, exists_nthPow_iff_bounded m hn]

/- ## The converse direction, stated cleanly -/

/-- If `m` **is** a perfect nth power, then `m ^ (1/n)` is rational (a natural
number), hence not irrational. This is the contrapositive content of the forward
implication, isolated for reference. -/
theorem not_irrational_nthRoot_of_perfectPow {n m : ℕ} (hn : n ≠ 0)
    (h : ∃ k : ℕ, k ^ n = m) : ¬ Irrational (nthRoot n m) := by
  rw [irrational_nthRoot_iff hn]; exact fun hneg => hneg h

/- ## Concrete instances — each a one-line `decide`, replacing manual enumeration -/

/-- `∛2` is irrational (n = 3, m = 2). -/
theorem irrational_cbrt_two : Irrational (nthRoot 3 2) := by
  rw [irrational_nthRoot_iff_bounded (by norm_num)]; decide

/-- `∛3` is irrational. -/
theorem irrational_cbrt_three : Irrational (nthRoot 3 3) := by
  rw [irrational_nthRoot_iff_bounded (by norm_num)]; decide

/-- `⁴√3` is irrational (n = 4, m = 3). -/
theorem irrational_fourthRoot_three : Irrational (nthRoot 4 3) := by
  rw [irrational_nthRoot_iff_bounded (by norm_num)]; decide

/-- `⁵√2` is irrational (n = 5, m = 2). -/
theorem irrational_fifthRoot_two : Irrational (nthRoot 5 2) := by
  rw [irrational_nthRoot_iff_bounded (by norm_num)]; decide

/-- `√2` is irrational, recovered as the n = 2 case of the same characterization. -/
theorem irrational_sqrt_two : Irrational (nthRoot 2 2) := by
  rw [irrational_nthRoot_iff_bounded (by norm_num)]; decide

/-- The converse side in action: `∛8 = 2` is **not** irrational, since `8 = 2³`. -/
theorem not_irrational_cbrt_eight : ¬ Irrational (nthRoot 3 8) :=
  not_irrational_nthRoot_of_perfectPow (by norm_num) ⟨2, by norm_num⟩

end Sqrt2IrrationalOQ03
