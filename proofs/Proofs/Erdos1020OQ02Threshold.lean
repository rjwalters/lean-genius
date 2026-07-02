import Proofs.Erdos1020OQ02

/-
# Erdős #1020 OQ-02 — an EXPLICIT large-`n` threshold

`Erdos1020OQ02.lean` proves the regime transition is a *finite* threshold
(`exists_large_regime`: some `N` beyond which `construction2 ≥ construction1`) but
leaves `N` non-explicit. This file pins an explicit value.

**Key identity.** `construction1 r k = C(rk−1, r) = (k−1)·C(rk−1, r−1)` — because
`C(n, r)·r = C(n, r−1)·(n−r+1)` (`Nat.choose_succ_right_eq`) and at `n = rk−1` the
factor `n−r+1 = r(k−1)`. This rewrites `construction1` into the same `C(·, r−1)`
"currency" as the §8 window lower bound
`(k−1)·C(n−k+1, r−1) ≤ construction2 n r k` (`construction2_window_lb`).

**Explicit threshold.** For `r, k ≥ 2` and every `n ≥ (r+1)k − 2`,
```
construction1 r k = (k−1)·C(rk−1, r−1)
                  ≤ (k−1)·C(n−k+1, r−1)   (choose monotone: rk−1 ≤ n−k+1)
                  ≤ construction2 n r k.
```
The monotonicity step needs exactly `rk − 1 ≤ n − k + 1`, i.e. `n ≥ (r+1)k − 2`, so
`N = (r+1)k − 2` is an explicit threshold for the large-`n` regime — a concrete
upper bound on the least crossover point (whose *exact* location, inside the
genuinely open zone, this file still does not claim).
-/

namespace Erdos1020OQ02

/-- `construction1 r k = (k−1)·C(rk−1, r−1)`, rewriting the small-`n` maximiser into
the `C(·, r−1)` form used by the window bounds. From `Nat.choose_succ_right_eq`. -/
theorem construction1_eq (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    construction1 r k = (k - 1) * Nat.choose (r * k - 1) (r - 1) := by
  unfold construction1
  have hrr : r - 1 + 1 = r := by omega
  have key := Nat.choose_succ_right_eq (r * k - 1) (r - 1)
  rw [hrr] at key
  -- key : C(rk-1, r) * r = C(rk-1, r-1) * (rk-1 - (r-1))
  have hexp : r * k = r * (k - 1) + r := by
    conv_lhs => rw [show k = (k - 1) + 1 from by omega]
    rw [Nat.mul_add, Nat.mul_one]
  have hsub : r * k - 1 - (r - 1) = r * (k - 1) := by omega
  rw [hsub] at key
  -- key : C(rk-1, r) * r = C(rk-1, r-1) * (r * (k-1))
  have hmul : Nat.choose (r * k - 1) r * r
      = (k - 1) * Nat.choose (r * k - 1) (r - 1) * r := by
    rw [key]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) hmul

/-- **Explicit large-`n` threshold.** For `r, k ≥ 2` and every `n ≥ (r+1)k − 2`,
the large-`n` construction dominates: `construction1 r k ≤ construction2 n r k`.
Thus `N = (r+1)k − 2` is an explicit threshold for the regime transition. -/
theorem large_regime_threshold (r k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k)
    {n : ℕ} (hn : (r + 1) * k - 2 ≤ n) :
    construction1 r k ≤ construction2 n r k := by
  have hexp2 : (r + 1) * k = r * k + k := by ring
  have hrk4 : 4 ≤ r * k := Nat.mul_le_mul hr hk
  have hnk : k ≤ n := by omega
  have hidx : r * k - 1 ≤ n - k + 1 := by omega
  calc construction1 r k
      = (k - 1) * Nat.choose (r * k - 1) (r - 1) := construction1_eq r k (by omega) (by omega)
    _ ≤ (k - 1) * Nat.choose (n - k + 1) (r - 1) := by
        gcongr
    _ ≤ construction2 n r k := construction2_window_lb n r k (by omega) (by omega) hnk

/-- Sanity: for `r = 4, k = 2` the explicit threshold is `N = (4+1)·2 − 2 = 8`,
matching the crossover at `n = 8` established in the base file. -/
example : (4 + 1) * 2 - 2 = 8 := by decide

end Erdos1020OQ02
