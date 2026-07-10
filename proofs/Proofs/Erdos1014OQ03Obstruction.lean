/-
Erdős Problem #1014 OQ-03: why the increment asymptotic is **not** derivable from the
asymptotic (`~`) equivalence class of `R(k, ·)`.

The companion files `Erdos1014OQ03.lean`, `Erdos1014OQ03LogIncrement.lean` and
`Erdos1014OQ03Concrete.lean` prove the honest **increment–ratio bridge**: for a
positive sequence `R`, the normalized increment `(R(l+1) − R(l))/R(l)` tends to `0`
iff the consecutive ratio `R(l+1)/R(l)` tends to `1`, and instantiate it on the
`k = 3` Ramsey number to get `Δ_l(3) = o(R(3,l))` unconditionally.

Their module docstrings warn against the tempting but **invalid** "Approach A", which
would read off a full increment asymptotic `Δ_l(k) ~ g_k(l)` from a power law
`R(k,l) ~ c_k · l^{k-1}/(log l)^{k-2}`. The warning is justified there only in prose,
with the informal witness `u_l = l²` versus `v_l = l² + l·sin l` (`u ~ v`, different
increments). This file turns that caution into a **theorem**.

## What is proved here

The consecutive increment of a sequence is **not** a function of its asymptotic
equivalence class: there exist eventually-positive sequences `u, v` with
`v(l)/u(l) → 1` (i.e. `u ~ v`) whose increment *ratio*
`(v(l+1) − v(l)) / (u(l+1) − u(l))` does **not** tend to `1` — indeed it does not
converge at all.

The witness is elementary and fully explicit:

    u l = l ,      v l = l + (−1)^l .

Then `v/u = 1 + (−1)^l/l → 1`, so `u ~ v`, while the increments are

    u(l+1) − u(l) = 1 ,      v(l+1) − v(l) = 1 − 2·(−1)^l ∈ {−1, 3},

so the increment ratio is `1 − 2·(−1)^l`, taking the value `−1` on every even index
and `3` on every odd index — it cannot converge, let alone to `1`. This is the
rigorous form of the sin-based caution, and it shows that *any* correct increment
statement for `R(k, ·)` must hypothesize the consecutive ratio (or a regularity
condition) directly, exactly as the increment–ratio bridge does.

Verified, 0 axioms, 0 sorries, no `native_decide`. Depends only on the abstract
bridge file, not on any Ramsey-specific input.

References:
- Erdős [Er71], Problem 1014
-/

import Mathlib
import Proofs.Erdos1014OQ03

namespace Erdos1014OQ03Obstruction

open Filter Topology

/-- The base sequence `u l = l`. -/
noncomputable def u : ℕ → ℝ := fun l => (l : ℝ)

/-- The perturbed sequence `v l = l + (−1)^l`, asymptotically equivalent to `u` but
with an oscillating consecutive increment. -/
noncomputable def v : ℕ → ℝ := fun l => (l : ℝ) + (-1 : ℝ) ^ l

/-- The base increment is constantly `1`: `u(l+1) − u(l) = 1`. -/
theorem u_increment (l : ℕ) : u (l + 1) - u l = 1 := by
  simp only [u]; push_cast; ring

/-- The perturbed increment is `1 − 2·(−1)^l`, oscillating between `−1` and `3`. -/
theorem v_increment (l : ℕ) : v (l + 1) - v l = 1 - 2 * (-1 : ℝ) ^ l := by
  simp only [v]; rw [pow_succ]; push_cast; ring

/-- `u` is eventually positive. -/
theorem u_pos : ∀ᶠ l in atTop, 0 < u l := by
  filter_upwards [eventually_gt_atTop 0] with l hl
  simpa [u] using (by exact_mod_cast hl : (0 : ℝ) < (l : ℝ))

/-- `v` is eventually positive (`v l ≥ l − 1 > 0` for `l ≥ 2`). -/
theorem v_pos : ∀ᶠ l in atTop, 0 < v l := by
  filter_upwards [eventually_ge_atTop 2] with l hl
  have habs : |(-1 : ℝ) ^ l| = 1 := by rw [abs_pow]; simp
  have hb : (-1 : ℝ) ≤ (-1 : ℝ) ^ l := by
    have := neg_abs_le ((-1 : ℝ) ^ l)
    rwa [habs] at this
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  simp only [v]; linarith

/-- **`u ~ v`.** The consecutive-value ratio `v(l)/u(l) = 1 + (−1)^l/l` tends to `1`,
so the two sequences are asymptotically equivalent. -/
theorem asymptotic_equiv : Tendsto (fun l => v l / u l) atTop (𝓝 1) := by
  -- On `l ≥ 1`, `v l / u l = 1 + (−1)^l / l`.
  have hEq : (fun l => v l / u l) =ᶠ[atTop] (fun l => 1 + (-1 : ℝ) ^ l / (l : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with l hl
    have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hl
    simp only [u, v, add_div, div_self hl0]
  rw [tendsto_congr' hEq]
  -- `(−1)^l / l → 0` by the sandwich `‖(−1)^l/l‖ ≤ 1/l → 0`.
  have h0 : Tendsto (fun l : ℕ => (-1 : ℝ) ^ l / (l : ℝ)) atTop (𝓝 0) := by
    have hbound : ∀ l : ℕ, ‖(-1 : ℝ) ^ l / (l : ℝ)‖ ≤ 1 / (l : ℝ) := by
      intro l
      simp [norm_div, norm_pow, Real.norm_natCast]
    exact squeeze_zero_norm hbound tendsto_one_div_atTop_nhds_zero_nat
  simpa using (tendsto_const_nhds.add h0)

/-- **The increment ratio does not converge to `1`.** For the witness pair `u, v`,
the consecutive-increment ratio `(v(l+1) − v(l))/(u(l+1) − u(l))` equals
`1 − 2·(−1)^l`, which is `−1` on every even index; hence it cannot tend to `1`.

This is the crux: `u ~ v` (`asymptotic_equiv`) yet the increment ratio fails to
converge, so no increment asymptotic can be extracted from the `~`-class alone. -/
theorem increment_ratio_not_tendsto_one :
    ¬ Tendsto (fun l => (v (l + 1) - v l) / (u (l + 1) - u l)) atTop (𝓝 1) := by
  intro h
  -- Rewrite the increment ratio in closed form `1 − 2·(−1)^l`.
  have hf : (fun l => (v (l + 1) - v l) / (u (l + 1) - u l))
      = (fun l => 1 - 2 * (-1 : ℝ) ^ l) := by
    funext l; rw [u_increment, v_increment, div_one]
  rw [hf] at h
  -- Restrict to even indices `l = 2n`, on which the value is constantly `−1`.
  have hmul : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have heven : Tendsto (fun n : ℕ => 1 - 2 * (-1 : ℝ) ^ (2 * n)) atTop (𝓝 1) := h.comp hmul
  have hconst : (fun n : ℕ => 1 - 2 * (-1 : ℝ) ^ (2 * n)) = (fun _ => (-1 : ℝ)) := by
    funext n; rw [pow_mul, neg_one_sq, one_pow]; norm_num
  rw [hconst] at heven
  -- A constant `−1` sequence tending to `1` forces `−1 = 1`.
  have : (-1 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds heven
  norm_num at this

/-- **The base sequence's normalized increment vanishes.**  For the witness `u l = l`
the normalized consecutive increment is `(u(l+1) − u(l))/u(l) = 1/l`, which tends to
`0`.  Read alongside `increment_ratio_not_tendsto_one`, this sharpens the obstruction:
`u` individually has a vanishing *normalized* increment (its jumps are `o(u)`), yet the
increment *ratio* against the `~`-equivalent `v` still fails to converge.  So even
`o(R)`-scale agreement of the sequences does not pin down the increment asymptotic —
the honest increment–ratio bridge, which hypothesizes the consecutive ratio directly,
is unavoidable.  (The companion statement for `v`, whose oscillating increment is
`1 − 2(−1)^l` over the diverging `v l = l + (−1)^l`, likewise tends to `0` but requires
a bounded-numerator-over-divergent-denominator estimate; recorded here as the base
case.) -/
theorem u_normalizedIncrement_tendsto_zero :
    Tendsto (fun l => (u (l + 1) - u l) / u l) atTop (𝓝 0) := by
  have hEq : (fun l => (u (l + 1) - u l) / u l) = (fun l : ℕ => 1 / (l : ℝ)) := by
    funext l; rw [u_increment]; simp [u]
  rw [hEq]
  exact tendsto_one_div_atTop_nhds_zero_nat

/-- **Increment not determined by the asymptotic class (packaged existential).**

There exist eventually-positive sequences `u, v` that are asymptotically equivalent
(`v(l)/u(l) → 1`) whose consecutive-increment ratio
`(v(l+1) − v(l))/(u(l+1) − u(l))` does **not** tend to `1`. Thus a full increment
asymptotic `Δ_l(k) ~ g_k(l)` cannot be derived from a power law `R(k,l) ~ g(l)`
alone — the honest route is the increment–ratio bridge, which hypothesizes the
consecutive ratio directly. -/
theorem increment_asymptotic_not_determined_by_asymptotic_class :
    ∃ u v : ℕ → ℝ,
      (∀ᶠ l in atTop, 0 < u l) ∧
      (∀ᶠ l in atTop, 0 < v l) ∧
      Tendsto (fun l => v l / u l) atTop (𝓝 1) ∧
      ¬ Tendsto (fun l => (v (l + 1) - v l) / (u (l + 1) - u l)) atTop (𝓝 1) :=
  ⟨u, v, u_pos, v_pos, asymptotic_equiv, increment_ratio_not_tendsto_one⟩

/-- **Increment undetermined even under normalized-increment regularity (sharpened
existential).**

A strengthening of `increment_asymptotic_not_determined_by_asymptotic_class`: the two
witnesses can additionally be required to have `u` *normalized-increment regular*, i.e.
`(u(l+1) − u(l))/u(l) → 0`.  So even when the sequences are asymptotically equivalent
**and** the base sequence's own jumps are `o(u)` — the natural first-order smoothness
hypothesis one might hope to leverage — the consecutive-increment ratio still fails to
tend to `1`.  Hence a normalized-increment (`o(R)`-scale) regularity assumption on the
sequence does **not** substitute for the honest increment–ratio bridge, which
hypothesizes the consecutive ratio directly. -/
theorem increment_asymptotic_not_determined_under_normalized_regularity :
    ∃ u v : ℕ → ℝ,
      (∀ᶠ l in atTop, 0 < u l) ∧
      (∀ᶠ l in atTop, 0 < v l) ∧
      Tendsto (fun l => v l / u l) atTop (𝓝 1) ∧
      Tendsto (fun l => (u (l + 1) - u l) / u l) atTop (𝓝 0) ∧
      ¬ Tendsto (fun l => (v (l + 1) - v l) / (u (l + 1) - u l)) atTop (𝓝 1) :=
  ⟨u, v, u_pos, v_pos, asymptotic_equiv, u_normalizedIncrement_tendsto_zero,
    increment_ratio_not_tendsto_one⟩

end Erdos1014OQ03Obstruction
