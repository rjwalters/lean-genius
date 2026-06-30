import Mathlib
import Proofs.AlternatingSeriesTestOQ01OQ01

/-
# Two-Sided Error Trapping for *Eventually* Antitone Alternating Series

The parent result (`AlternatingSeriesTestOQ01OQ01`) traps the truncation error of an
alternating series `S_N = ∑_{i<N} (-1)^i f i` between two consecutive omitted terms,

`f N - f (N+1) ≤ |S_N - l| ≤ f N`,

under the *global* hypothesis that `f` is antitone and `f → 0`. The parent's own open
question (index 1) asks whether the same two-sided bound survives when the monotonicity is
only **eventual** — `f` antitone on `[M, ∞)` rather than on all of `ℕ`. This file answers
it: **yes, verbatim, for every `N ≥ M`.**

The mechanism is a *shift reduction*. Write the tail of the series starting at index `M` as
its own alternating series with coefficients `g j = f (j + M)`. Then `g` is globally
antitone and `g → 0`, so the parent theorem applies to `g`. The two series are linked by the
exact splitting

`S_{n+M} = S_M + (-1)^M · T_n`,   where `T_n = ∑_{j<n} (-1)^j g j`,

so the truncation errors coincide up to a sign of modulus one: `|S_N - l| = |T_{N-M} - t|`.
Feeding the parent's trap for `g` back through `g (N-M) = f N` and `g (N-M+1) = f (N+1)`
reproduces the original two-term trap, now valid from the antitonicity threshold `M` onward.

Two further points are established along the way and are genuinely new content:

* **Convergence is derived, not assumed.** Eventual antitonicity plus `f → 0` already forces
  `S_N` to converge (the shifted series does, by Leibniz). So the limit `l` need not be
  hypothesised.
* **The hypothesis is strictly weaker.** An explicit `f` (a single upward "bump" at the
  start, antitone only from `M = 1` on) satisfies the eventual hypothesis but not the global
  one, so the parent theorem does not apply to it while this one does.

All results are over `ℝ` and the proof is axiom-free.
-/

namespace AlternatingSeriesTestOQ01OQ01OQ02

open Finset Filter Topology

variable {f : ℕ → ℝ} {M : ℕ}

/-- The shifted tail coefficients `g j = f (j + M)`. When `f` is antitone on `[M, ∞)` these
are globally antitone, which is the whole point of the reduction. -/
theorem antitone_shift (hfa : AntitoneOn f (Set.Ici M)) :
    Antitone (fun j : ℕ => f (j + M)) := by
  intro j k hjk
  exact hfa (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr (by omega)) (by omega)

/-- The shifted coefficients still tend to `0`. -/
theorem tendsto_shift_zero (hf0 : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun j : ℕ => f (j + M)) atTop (𝓝 0) :=
  hf0.comp (tendsto_add_atTop_nat M)

/-- **Shift splitting of partial sums.** The partial sum of the full series at index `n + M`
splits as the fixed head `S_M` plus a `±` copy of the shifted series' partial sum:

`∑_{i<n+M} (-1)^i f i = ∑_{i<M} (-1)^i f i + (-1)^M ∑_{j<n} (-1)^j f (j+M)`.

Proved by induction on `n`: each new term `(-1)^{n+M} f (n+M)` on the left matches
`(-1)^M · (-1)^n f (n+M)` on the right via `(-1)^{n+M} = (-1)^M (-1)^n`. -/
theorem partialSum_shift (n : ℕ) :
    (∑ i ∈ range (n + M), (-1 : ℝ) ^ i * f i)
      = (∑ i ∈ range M, (-1 : ℝ) ^ i * f i)
        + (-1 : ℝ) ^ M * ∑ j ∈ range n, (-1 : ℝ) ^ j * f (j + M) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + M = (n + M) + 1 by ring, Finset.sum_range_succ (n := n + M), ih,
      Finset.sum_range_succ (n := n), pow_add]
    ring

/-- **Convergence from eventual antitonicity.** If `f` is antitone on `[M, ∞)` and `f → 0`,
the alternating partial sums converge. The limit is exhibited explicitly as
`l = S_M + (-1)^M t`, where `t` is the Leibniz limit of the shifted series. -/
theorem tendsto_partialSum_of_eventually_antitone
    (hfa : AntitoneOn f (Set.Ici M)) (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 l) := by
  obtain ⟨t, ht⟩ :=
    (antitone_shift hfa).tendsto_alternating_series_of_tendsto_zero (tendsto_shift_zero hf0)
  refine ⟨(∑ i ∈ range M, (-1 : ℝ) ^ i * f i) + (-1 : ℝ) ^ M * t, ?_⟩
  rw [← tendsto_add_atTop_iff_nat M]
  refine (ht.const_mul ((-1 : ℝ) ^ M)).const_add _ |>.congr (fun n => ?_)
  rw [partialSum_shift n]

/-- **Two-sided two-term error trap, eventually-antitone form.** Suppose `f` is antitone on
`[M, ∞)`, `f → 0`, and the alternating series converges to `l`. Then for **every** index
`N ≥ M` the truncation error is trapped exactly as in the globally-antitone case:

`f N - f (N+1) ≤ |S_N - l| ≤ f N`.

The proof reduces to the parent theorem applied to the shifted series `g j = f (j+M)`:
the error `|S_N - l|` equals `|T_{N-M} - t|` (the limits differ by the same `(-1)^M` factor),
and `g (N-M) = f N`, `g (N-M+1) = f (N+1)`. -/
theorem abs_partialSum_sub_limit_trapped_eventually
    (hfa : AntitoneOn f (Set.Ici M)) (hf0 : Tendsto f atTop (𝓝 0))
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 l)) {N : ℕ}
    (hN : M ≤ N) :
    f N - f (N + 1) ≤ |(∑ i ∈ range N, (-1 : ℝ) ^ i * f i) - l|
      ∧ |(∑ i ∈ range N, (-1 : ℝ) ^ i * f i) - l| ≤ f N := by
  -- shifted coefficients and their (global) Leibniz limit `t`
  set g : ℕ → ℝ := fun j => f (j + M) with hg
  have hga : Antitone g := antitone_shift hfa
  have hg0 : Tendsto g atTop (𝓝 0) := tendsto_shift_zero hf0
  obtain ⟨t, ht⟩ := hga.tendsto_alternating_series_of_tendsto_zero hg0
  -- the full limit `l` is forced to be `S_M + (-1)^M t`
  have hl' : l = (∑ i ∈ range M, (-1 : ℝ) ^ i * f i) + (-1 : ℝ) ^ M * t := by
    have hconv : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop
        (𝓝 ((∑ i ∈ range M, (-1 : ℝ) ^ i * f i) + (-1 : ℝ) ^ M * t)) := by
      rw [← tendsto_add_atTop_iff_nat M]
      refine (ht.const_mul ((-1 : ℝ) ^ M)).const_add _ |>.congr (fun n => ?_)
      rw [partialSum_shift n]
    exact tendsto_nhds_unique hl hconv
  -- write `N = (N - M) + M` so the shift splitting applies at `n = N - M`
  obtain ⟨m, rfl⟩ : ∃ m, N = m + M := ⟨N - M, by omega⟩
  -- key identity: `S_N - l = (-1)^M (T_m - t)`, hence `|S_N - l| = |T_m - t|`
  have hsplit : (∑ i ∈ range (m + M), (-1 : ℝ) ^ i * f i) - l
      = (-1 : ℝ) ^ M * ((∑ j ∈ range m, (-1 : ℝ) ^ j * g j) - t) := by
    rw [partialSum_shift m, hl']; ring
  have habs : |(∑ i ∈ range (m + M), (-1 : ℝ) ^ i * f i) - l|
      = |(∑ j ∈ range m, (-1 : ℝ) ^ j * g j) - t| := by
    rw [hsplit, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  -- parent trap for the shifted (globally antitone) series at index `m`
  have hpar := AlternatingSeriesTestOQ01OQ01.abs_partialSum_sub_limit_trapped hga hg0 ht m
  -- translate `g m = f N`, `g (m+1) = f (N+1)`
  have hgm : g m = f (m + M) := rfl
  have hgm1 : g (m + 1) = f (m + M + 1) := by simp only [hg]; congr 1; omega
  rw [habs, ← hgm, ← hgm1]
  exact hpar

/-- The upper (Leibniz) half, extracted: `|S_N - l| ≤ f N` for `N ≥ M`. -/
theorem abs_partialSum_sub_limit_le_eventually
    (hfa : AntitoneOn f (Set.Ici M)) (hf0 : Tendsto f atTop (𝓝 0))
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 l)) {N : ℕ}
    (hN : M ≤ N) :
    |(∑ i ∈ range N, (-1 : ℝ) ^ i * f i) - l| ≤ f N :=
  (abs_partialSum_sub_limit_trapped_eventually hfa hf0 hl hN).2

/-- The lower (sharpness) half, extracted: `f N - f (N+1) ≤ |S_N - l|` for `N ≥ M`. -/
theorem sub_le_abs_partialSum_sub_limit_eventually
    (hfa : AntitoneOn f (Set.Ici M)) (hf0 : Tendsto f atTop (𝓝 0))
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 l)) {N : ℕ}
    (hN : M ≤ N) :
    f N - f (N + 1) ≤ |(∑ i ∈ range N, (-1 : ℝ) ^ i * f i) - l| :=
  (abs_partialSum_sub_limit_trapped_eventually hfa hf0 hl hN).1

/-!
## The hypothesis is strictly weaker

We exhibit a concrete coefficient sequence that is antitone on `[1, ∞)` but **not** antitone
on all of `ℕ`, witnessing that the eventually-antitone trap covers cases the parent's global
hypothesis cannot. The sequence is the alternating-harmonic profile with an upward bump
planted at the start: `b 0 = 0`, `b i = 1/(i+1)` for `i ≥ 1`. Since `b 0 = 0 < 1/2 = b 1`,
it fails global antitonicity, yet from index `1` on it is the usual antitone `1/(i+1)`.
-/

/-- The bumped coefficient sequence: `0` at the origin, then `1/(i+1)`. -/
noncomputable def bumped (i : ℕ) : ℝ := if i = 0 then 0 else 1 / ((i : ℝ) + 1)

/-- `bumped` is antitone on `[1, ∞)`: there the `if` is uniformly in its `i ≠ 0` branch and
the coefficients are the standard decreasing `1/(i+1)`. -/
theorem antitoneOn_bumped : AntitoneOn bumped (Set.Ici 1) := by
  intro i hi j hj hij
  simp only [Set.mem_Ici] at hi hj
  have hi0 : i ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  simp only [bumped, hi0, hj0, if_false]
  have hipos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  apply one_div_le_one_div_of_le hipos
  exact_mod_cast by simpa using hij

/-- `bumped → 0`. -/
theorem tendsto_bumped_zero : Tendsto bumped atTop (𝓝 0) := by
  have h : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with i hi
  simp only [bumped, if_neg (by omega : i ≠ 0)]

/-- `bumped` is **not** globally antitone: it rises from `b 0 = 0` to `b 1 = 1/2`. Hence the
parent theorem's global hypothesis genuinely fails on it, while the eventually-antitone trap
of this file applies with `M = 1`. -/
theorem not_antitone_bumped : ¬ Antitone bumped := by
  intro h
  have := h (show (0 : ℕ) ≤ 1 by norm_num)
  simp only [bumped, if_neg (by norm_num : (1 : ℕ) ≠ 0)] at this
  norm_num at this

/-- **Capstone: the eventually-antitone trap applies to the bumped series.** The series
`∑ (-1)^i bumped i` converges to some `l`, and for every `N ≥ 1` its error is trapped between
the consecutive-term gap and the first omitted term — even though `bumped` is not globally
antitone, so the parent result does not cover it. -/
theorem bumped_error_trapped :
    ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * bumped i) atTop (𝓝 l) ∧
      ∀ N : ℕ, 1 ≤ N →
        bumped N - bumped (N + 1) ≤ |(∑ i ∈ range N, (-1 : ℝ) ^ i * bumped i) - l|
          ∧ |(∑ i ∈ range N, (-1 : ℝ) ^ i * bumped i) - l| ≤ bumped N := by
  obtain ⟨l, hl⟩ :=
    tendsto_partialSum_of_eventually_antitone antitoneOn_bumped tendsto_bumped_zero
  exact ⟨l, hl, fun N hN =>
    abs_partialSum_sub_limit_trapped_eventually antitoneOn_bumped tendsto_bumped_zero hl hN⟩

end AlternatingSeriesTestOQ01OQ01OQ02
