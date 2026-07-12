/-
# Alternating-Series Boole Summation — OQ-01-OQ-01
## The order-`K` Boole summation limit

The parent entry `AlternatingSeriesBooleSummationOQ01.lean` passes the **first-order** finite
Boole identity `boole_first` to the limit `m → ∞`, for a convergent alternating series of a null
sequence.  Its follow-up question asks for the same at **every order `K` at once**: carry the
finite order-`K` identity `boole_general` (from the base file `AlternatingSeriesBooleSummation`)
to the limit `m → ∞`.

The base file proves, on every finite window `n ≤ m` with no convergence assumed,

  `altSum a n m`
  `  = ∑_{k=0}^{K-1} ((-1)^k / 2^{k+1}) · ((-1)^n (Δᵏa)_n − (-1)^m (Δᵏa)_m)`
  `    + ((-1)^K / 2^K) · altSum (Δᴷa) n m`   (`boole_general`),

where `Δᵏa = fdiff^[k] a` is the `k`-th forward difference and `altSum b n m = ∑_{j=n}^{m-1}
(-1)^j b_j`.  This file passes that identity to the limit.

**The only analytic input** is that for a null sequence every endpoint term `(-1)^m (Δᵏa)_m`
vanishes.  This uses one new structural fact — that *each* iterated forward difference of a null
sequence is again null (`iterate_fdiff_tendsto_zero`) — after which the whole order-`K` boundary
sum converges termwise and the remainder `((-1)^K/2^K)·altSum(Δᴷa) n m` converges to
`T_K := lim_m altSum (Δᴷa) n m`.  The result is

  `S = ∑_{k=0}^{K-1} ((-1)^k / 2^{k+1}) · (-1)^n (Δᵏa)_n + ((-1)^K / 2^K) · T_K`
      (`boole_general_tendsto`).

Because `((-1)^K/2^K) = −((-1)^{K-1}/2^K)`, this is exactly the closed form
`S = ∑ ((-1)^k/2^{k+1})(-1)^n(Δᵏa)_n − ((-1)^{K-1}/2^K) T_K` of the open question, now valid
uniformly in `K` (the case `K = 0` reads `S = S`, and `K = 1` recovers the parent's
`boole_tendsto`).

We also settle the two supporting open items:

* **Convergence of every intermediate series** (`iterate_altSum_tendsto`): if `a → 0` and the
  base alternating series converges, then `altSum (Δᵏa) n ·` converges for *every* `k`, so each
  `T_k` — and in particular `T_K` — is well defined.  (The hypothesis `hT` of the main theorem is
  therefore automatic, not an extra assumption.)

* **Unconditional antitone version** (`boole_general_tendsto_of_antitone`): for an antitone null
  sequence Mathlib's alternating-series test supplies convergence outright, so the order-`K`
  identity holds with no convergence hypothesis at all.

All results are over `ℝ` and axiom-free.
-/

import Mathlib
import Proofs.AlternatingSeriesBooleSummation

namespace AlternatingSeriesBooleSummationOQ01OQ01

open AlternatingSeriesBooleSummation Finset Filter Topology

/-! ## Endpoint terms of a null sequence vanish -/

/-- The absolute value of the signed term is just `|a m|` (the sign has modulus `1`). -/
theorem abs_sign_mul (a : ℕ → ℝ) (m : ℕ) : |(-1 : ℝ) ^ m * a m| = |a m| := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- For a null sequence, the alternating endpoint term `(-1)^m a_m` tends to `0`. -/
theorem sign_mul_tendsto_zero {a : ℕ → ℝ} (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun m => (-1 : ℝ) ^ m * a m) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m => |a m|) atTop (𝓝 0) := by simpa using ha0.abs
  have hlower : Tendsto (fun m => -|a m|) atTop (𝓝 0) := by simpa using hupper.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun m => ?_) (fun m => ?_)
  · have := neg_abs_le ((-1 : ℝ) ^ m * a m); rwa [abs_sign_mul a m] at this
  · have := le_abs_self ((-1 : ℝ) ^ m * a m); rwa [abs_sign_mul a m] at this

/-- **Every iterated forward difference of a null sequence is again null.**  If `a → 0` then
`Δᵏa = fdiff^[k] a → 0` for every `k`, by induction: `Δ^{k+1}a_j = (Δᵏa)_{j+1} − (Δᵏa)_j` is a
difference of two shifted copies of `Δᵏa`, each of which tends to `0`.  This is the structural
input that makes *every* endpoint term in `boole_general` vanish in the limit. -/
theorem iterate_fdiff_tendsto_zero {a : ℕ → ℝ} (ha0 : Tendsto a atTop (𝓝 0)) :
    ∀ k, Tendsto (fdiff^[k] a) atTop (𝓝 0) := by
  intro k
  induction k with
  | zero => simpa using ha0
  | succ k ih =>
    have hshift : Tendsto (fun j => (fdiff^[k] a) (j + 1)) atTop (𝓝 0) :=
      ih.comp (tendsto_add_atTop_nat 1)
    have hsub : Tendsto (fun j => (fdiff^[k] a) (j + 1) - (fdiff^[k] a) j) atTop (𝓝 (0 - 0)) :=
      hshift.sub ih
    have hstep : fdiff^[k + 1] a = fdiff (fdiff^[k] a) :=
      congrFun (Function.iterate_succ' fdiff k) a
    rw [hstep]
    show Tendsto (fun j => (fdiff^[k] a) (j + 1) - (fdiff^[k] a) j) atTop (𝓝 0)
    simpa using hsub

/-! ## The first-order limit engine (restated for the base definitions) -/

/-- **Limit of the forward-difference alternating series.**  If `a → 0` and `altSum a n · → S`,
then `altSum (Δa) n · → (-1)^n a_n − 2S`.  This is `boole_first` after `m → ∞`; we restate it for
the base-file definitions of `altSum`/`fdiff` so it composes with `boole_general`. -/
theorem fdiff_altSum_tendsto {a : ℕ → ℝ} {n : ℕ} {S : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S)) :
    Tendsto (fun m => altSum (fdiff a) n m) atTop (𝓝 ((-1 : ℝ) ^ n * a n - 2 * S)) := by
  have heq : (fun m => altSum (fdiff a) n m)
      =ᶠ[atTop] (fun m => ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m) - 2 * altSum a n m) := by
    filter_upwards [eventually_ge_atTop n] with m hm
    have := boole_first a n m hm
    linarith [this]
  rw [tendsto_congr' heq]
  have hend : Tendsto (fun m => (-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m) atTop
      (𝓝 ((-1 : ℝ) ^ n * a n - 0)) :=
    tendsto_const_nhds.sub (sign_mul_tendsto_zero ha0)
  have := hend.sub (hS.const_mul 2)
  simpa using this

/-- **Convergence of every intermediate higher-difference series.**  If `a → 0` and the base
alternating series converges (`altSum a n · → S`), then for *every* order `k` the alternating
series of the `k`-th forward difference converges: `altSum (Δᵏa) n ·` has a limit `T_k`.  Proof by
induction on `k` using `fdiff_altSum_tendsto` (and `iterate_fdiff_tendsto_zero` to feed it the
nullity of `Δᵏa`).  In particular the limit `T_K` in `boole_general_tendsto` always exists. -/
theorem iterate_altSum_tendsto {a : ℕ → ℝ} {n : ℕ} {S : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S)) :
    ∀ k, ∃ T, Tendsto (fun m => altSum (fdiff^[k] a) n m) atTop (𝓝 T) := by
  intro k
  induction k with
  | zero => exact ⟨S, by simpa using hS⟩
  | succ k ih =>
    obtain ⟨Tk, hTk⟩ := ih
    refine ⟨(-1 : ℝ) ^ n * (fdiff^[k] a) n - 2 * Tk, ?_⟩
    have hbk : Tendsto (fdiff^[k] a) atTop (𝓝 0) := iterate_fdiff_tendsto_zero ha0 k
    have hstep : fdiff^[k + 1] a = fdiff (fdiff^[k] a) :=
      congrFun (Function.iterate_succ' fdiff k) a
    rw [hstep]
    exact fdiff_altSum_tendsto hbk hTk

/-! ## The order-`K` Boole summation limit -/

/-- **The order-`K` Boole summation limit.**  Let `a → 0`, let the base alternating series
converge (`altSum a n · → S`), and let the `K`-th forward-difference series converge
(`altSum (Δᴷa) n · → T`).  Then passing `boole_general` (order `K`) to `m → ∞`:

  `S = ∑_{k=0}^{K-1} ((-1)^k / 2^{k+1}) · (-1)^n (Δᵏa)_n + ((-1)^K / 2^K) · T`.

Every endpoint term `(-1)^m (Δᵏa)_m` vanishes by `iterate_fdiff_tendsto_zero`, so the finite
order-`K` boundary sum converges termwise to its `m`-free part and the remainder converges to `T`.
Since `((-1)^K/2^K) = −((-1)^{K-1}/2^K)`, this is the closed identity of the open question, valid
uniformly in `K`; `K = 1` is the parent's `boole_tendsto`. -/
theorem boole_general_tendsto {a : ℕ → ℝ} {n K : ℕ} {S T : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S))
    (hT : Tendsto (fun m => altSum (fdiff^[K] a) n m) atTop (𝓝 T)) :
    S = (∑ k ∈ Finset.range K,
            ((-1 : ℝ) ^ k / 2 ^ (k + 1)) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
        + ((-1 : ℝ) ^ K / 2 ^ K) * T := by
  -- `altSum a n m` equals the finite order-`K` Boole model for all `m ≥ n`.
  have hcongr : (fun m => altSum a n m) =ᶠ[atTop]
      (fun m => (∑ k ∈ Finset.range K,
            ((-1 : ℝ) ^ k / 2 ^ (k + 1))
              * ((-1 : ℝ) ^ n * (fdiff^[k] a) n - (-1 : ℝ) ^ m * (fdiff^[k] a) m))
          + ((-1 : ℝ) ^ K / 2 ^ K) * altSum (fdiff^[K] a) n m) := by
    filter_upwards [eventually_ge_atTop n] with m hm
    exact boole_general a n m hm K
  -- The model function converges to the claimed right-hand side.
  have key : Tendsto (fun m => altSum a n m) atTop (𝓝
      ((∑ k ∈ Finset.range K,
            ((-1 : ℝ) ^ k / 2 ^ (k + 1)) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
        + ((-1 : ℝ) ^ K / 2 ^ K) * T)) := by
    rw [tendsto_congr' hcongr]
    refine Tendsto.add ?_ (hT.const_mul ((-1 : ℝ) ^ K / 2 ^ K))
    refine tendsto_finset_sum _ (fun k _ => ?_)
    have hz : Tendsto (fun m => (-1 : ℝ) ^ m * (fdiff^[k] a) m) atTop (𝓝 0) :=
      sign_mul_tendsto_zero (iterate_fdiff_tendsto_zero ha0 k)
    have hd : Tendsto (fun m => (-1 : ℝ) ^ n * (fdiff^[k] a) n - (-1 : ℝ) ^ m * (fdiff^[k] a) m)
        atTop (𝓝 ((-1 : ℝ) ^ n * (fdiff^[k] a) n - 0)) := tendsto_const_nhds.sub hz
    have := hd.const_mul ((-1 : ℝ) ^ k / 2 ^ (k + 1))
    simpa using this
  exact tendsto_nhds_unique hS key

/-! ## Unconditional version for antitone null sequences -/

/-- Consecutive-window additivity `altSum a 0 n + altSum a n m = altSum a 0 m` for `n ≤ m`. -/
theorem altSum_zero_add (a : ℕ → ℝ) {n m : ℕ} (h : n ≤ m) :
    altSum a 0 n + altSum a n m = altSum a 0 m := by
  simp only [altSum]
  rw [Finset.sum_Ico_consecutive _ (Nat.zero_le n) h]

/-- Every tail of an antitone null sequence's alternating series converges (Mathlib's
alternating-series test on the full series, then the consecutive-window identity). -/
theorem altSum_tendsto_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    (ha0 : Tendsto a atTop (𝓝 0)) (n : ℕ) :
    ∃ S, Tendsto (fun m => altSum a n m) atTop (𝓝 S) := by
  obtain ⟨L, hL⟩ := ha.tendsto_alternating_series_of_tendsto_zero ha0
  have hL' : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L) := by
    refine hL.congr (fun m => ?_)
    rw [altSum, Finset.range_eq_Ico]
  refine ⟨L - altSum a 0 n, ?_⟩
  have heq : (fun m => altSum a n m) =ᶠ[atTop] (fun m => altSum a 0 m - altSum a 0 n) := by
    filter_upwards [eventually_ge_atTop n] with m hm
    have := altSum_zero_add a hm
    linarith [this]
  rw [tendsto_congr' heq]
  exact hL'.sub_const _

/-- **The order-`K` Boole summation limit, unconditionally, for antitone null sequences.**  For an
antitone `a → 0` no convergence hypothesis is needed: the base series and every higher-difference
series converge by the alternating-series test (`altSum_tendsto_of_antitone`,
`iterate_altSum_tendsto`), so the order-`K` closed identity holds outright. -/
theorem boole_general_tendsto_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    (ha0 : Tendsto a atTop (𝓝 0)) (n K : ℕ) :
    ∃ S T, Tendsto (fun m => altSum a n m) atTop (𝓝 S)
      ∧ Tendsto (fun m => altSum (fdiff^[K] a) n m) atTop (𝓝 T)
      ∧ S = (∑ k ∈ Finset.range K,
              ((-1 : ℝ) ^ k / 2 ^ (k + 1)) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
            + ((-1 : ℝ) ^ K / 2 ^ K) * T := by
  obtain ⟨S, hS⟩ := altSum_tendsto_of_antitone ha ha0 n
  obtain ⟨T, hT⟩ := iterate_altSum_tendsto ha0 hS K
  exact ⟨S, T, hS, hT, boole_general_tendsto ha0 hS hT⟩

/-- **Sanity check: `K = 1` recovers the parent's first-order limit `boole_tendsto`.**  With
`K = 1` the boundary sum has the single `k = 0` term `½·(-1)^n a_n` and the remainder is
`-½·T`, i.e. `S = ½·(-1)^n a_n − ½·T`. -/
theorem boole_general_tendsto_one {a : ℕ → ℝ} {n : ℕ} {S T : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S))
    (hT : Tendsto (fun m => altSum (fdiff a) n m) atTop (𝓝 T)) :
    S = (1 / 2) * ((-1 : ℝ) ^ n * a n) - (1 / 2) * T := by
  have hT' : Tendsto (fun m => altSum (fdiff^[1] a) n m) atTop (𝓝 T) := by
    simpa using hT
  have h := boole_general_tendsto (K := 1) ha0 hS hT'
  rw [Finset.sum_range_one] at h
  simp only [Function.iterate_zero, id_eq, pow_zero, pow_one] at h
  linarith [h]

#check @boole_general_tendsto
#check @iterate_altSum_tendsto
#check @boole_general_tendsto_of_antitone

end AlternatingSeriesBooleSummationOQ01OQ01
