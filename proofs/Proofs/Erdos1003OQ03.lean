/-
  Erdős Problem #1003 — Open Question OQ-03:
  "What is the true asymptotic density of the solution set
   `{ n | φ n = φ (n+1) }`?"

This file does NOT resolve the open question.  The conjectured answer is that
the natural density is `0` (solutions are extremely sparse — Erdős–Pomerance–Sárközy
give the sparsity bound `#{n ≤ x : φ n = φ(n+1)} ≤ x / exp((log x)^{1/3})`
eventually), while the set is *conjectured to be infinite* (this is #1003 itself,
still open even in the base case).  Neither the infinitude nor the exact density
is known.

Instead we formalize the *honest structural layer* of the density question: we
introduce the counting function and the natural-density predicate, and prove the
exact logical relationships that pin down what an eventual answer must supply.

  1. The counting function `countConsecutiveEqual N = #{n ≤ N : φ n = φ(n+1)}`
     is monotone and bounded by `N + 1`.

  2. **The density object is the right one**: the solution set is infinite *iff*
     the counting function is unbounded (`infinite_iff_count_unbounded`).  This is
     the bridge between the density/counting view of OQ-03 and the infinitude view
     of the main #1003 conjecture (and of OQ-02).

  3. **A positive density would settle #1003**: if the natural density exists and
     is positive, the set is infinite (`infinite_of_pos_density`).  Hence one
     cannot exhibit a positive density without first resolving the open infinitude
     conjecture.

  4. **Density 0 is strictly weaker information**: whenever the set is *finite* its
     natural density is `0` (`hasNaturalDensity_zero_of_finite`).  So the conjectured
     answer (density 0) is exactly the value forced by finiteness — it does not by
     itself decide infinitude.  Together with (3) this isolates the genuine content
     of OQ-03: the density is `0` in both the finite and the (conjectured) sparse-but-
     infinite worlds, and any *positive* density is equivalent to a strong form of
     the open #1003 conjecture.

  5. **The upper density is the unconditional carrier**: the natural-density
     *limit* may fail to exist (existence is itself open), but the upper density
     `upperDensity = limsup_N count(N)/(N+1)` always exists for our bounded
     sequence.  We show it lies in `[0,1]`, agrees with the natural density when
     the latter exists, vanishes on finite solution sets, and — most usefully —
     that a *positive upper density* already forces infinitude
     (`infinite_of_pos_upperDensity`).  This strengthens (3): one no longer needs
     the limit to exist, only its limsup to be positive.

These are fully machine-checked (0 sorry, 0 axiom) consequences of the
definitions.  The definitions agree verbatim with the parent #1003 entry
(`Proofs.Erdos1003Problem`) and the sibling OQ-02 file.

Reference: https://erdosproblems.com/1003
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Nat Set Filter Topology

namespace Erdos1003.OQ03

/-! ## Definitions (mirroring `Proofs.Erdos1003Problem`) -/

/-- The set of `n` with `φ n = φ (n+1)` — the main Erdős #1003 set. -/
def ConsecutiveEqualTotients : Set ℕ :=
  { n : ℕ | φ n = φ (n + 1) }

/-- Count of `n ≤ N` with `φ n = φ (n+1)` (i.e. over `Finset.range (N+1)`).
Agrees verbatim with `Proofs.Erdos1003Problem.countConsecutiveEqual`. -/
def countConsecutiveEqual (N : ℕ) : ℕ :=
  (Finset.filter (fun n => φ n = φ (n + 1)) (Finset.range (N + 1))).card

/-- Membership in the counted finset is exactly "is a solution and is `≤ N`". -/
theorem mem_filter_iff {N n : ℕ} :
    n ∈ Finset.filter (fun n => φ n = φ (n + 1)) (Finset.range (N + 1)) ↔
      n ∈ ConsecutiveEqualTotients ∧ n ≤ N := by
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ## Elementary properties of the counting function -/

/-- The counting function is monotone: a wider window contains at least as many
solutions. -/
theorem countConsecutiveEqual_monotone : Monotone countConsecutiveEqual := by
  intro a b hab
  apply Finset.card_le_card
  intro x hx
  rw [mem_filter_iff] at hx ⊢
  exact ⟨hx.1, hx.2.trans hab⟩

/-- At most `N + 1` integers lie in the window `0, …, N`, so the count is bounded
by `N + 1`. -/
theorem countConsecutiveEqual_le (N : ℕ) : countConsecutiveEqual N ≤ N + 1 := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_range]

/-! ## The bridge: density-counting view ⇔ infinitude view

This connects OQ-03 (asymptotic density) to the main #1003 conjecture / OQ-02
(infinitude): the solution set is infinite exactly when the counting function is
unbounded. -/

theorem infinite_iff_count_unbounded :
    ConsecutiveEqualTotients.Infinite ↔
      ∀ M, ∃ N, M ≤ countConsecutiveEqual N := by
  constructor
  · -- infinite ⇒ unbounded count: take a finite subset of size `M` and bound the
    -- window by its largest element.
    intro hinf M
    obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq M
    refine ⟨t.sup id, ?_⟩
    have hsub : t ⊆ Finset.filter (fun n => φ n = φ (n + 1))
        (Finset.range (t.sup id + 1)) := by
      intro x hx
      rw [mem_filter_iff]
      refine ⟨hts (Finset.mem_coe.mpr hx), ?_⟩
      exact Finset.le_sup (f := id) hx
    calc M = t.card := htc.symm
      _ ≤ _ := Finset.card_le_card hsub
  · -- unbounded count ⇒ infinite: otherwise the count is bounded by the (finite)
    -- total number of solutions.
    intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N, hN⟩ := h (hfin.toFinset.card + 1)
    have hle : countConsecutiveEqual N ≤ hfin.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      rw [mem_filter_iff] at hx
      rw [Set.Finite.mem_toFinset]
      exact hx.1
    omega

/-! ## Natural density -/

/-- The solution set "has natural density `d`" if the proportion of solutions in
`{0, …, N}` converges to `d` as `N → ∞`. -/
def HasNaturalDensity (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (countConsecutiveEqual N : ℝ) / (N + 1)) atTop (𝓝 d)

/-- The density ratio is always nonnegative. -/
theorem density_ratio_nonneg (N : ℕ) :
    0 ≤ (countConsecutiveEqual N : ℝ) / (N + 1) := by
  positivity

/-- The density ratio never exceeds `1`. -/
theorem density_ratio_le_one (N : ℕ) :
    (countConsecutiveEqual N : ℝ) / (N + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact_mod_cast countConsecutiveEqual_le N

/-- If the solution set is finite, its natural density is `0`: the count is
bounded by a constant while the window grows. -/
theorem hasNaturalDensity_zero_of_finite
    (hfin : ConsecutiveEqualTotients.Finite) : HasNaturalDensity 0 := by
  unfold HasNaturalDensity
  set C : ℕ := hfin.toFinset.card with hC
  -- count is uniformly bounded by `C`
  have hbound : ∀ N, countConsecutiveEqual N ≤ C := by
    intro N
    apply Finset.card_le_card
    intro x hx
    rw [mem_filter_iff] at hx
    rw [Set.Finite.mem_toFinset]
    exact hx.1
  -- squeeze `0 ≤ count/(N+1) ≤ C/(N+1) → 0`
  have hupper : Tendsto (fun N : ℕ => (C : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  refine squeeze_zero density_ratio_nonneg (fun N => ?_) hupper
  gcongr
  exact_mod_cast hbound N

/-- A positive natural density would resolve Erdős #1003 affirmatively: the
solution set would be infinite.  (Proof: a finite set has density `0`, so by
uniqueness of limits a positive density forces the set to be infinite.) -/
theorem infinite_of_pos_density {d : ℝ} (hd : 0 < d)
    (h : HasNaturalDensity d) : ConsecutiveEqualTotients.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have h0 : HasNaturalDensity 0 := hasNaturalDensity_zero_of_finite hfin
  have : d = 0 := tendsto_nhds_unique h h0
  exact absurd this (ne_of_gt hd)

/-! ## What an answer to OQ-03 must supply: uniqueness and range

The previous section shows the density object is the right one (it sees infinitude)
and that a *positive* value is as hard as #1003. This section pins down the shape of
any admissible answer: it is a **unique** real number lying in **`[0, 1]`**, and a
positive value is equivalent (via the bridge) to the counting function being
unbounded. -/

/-- **Natural density, when it exists, is unique.** Two density values for the
solution set coincide, since limits in `ℝ` are unique (`atTop` is `NeBot`). So OQ-03
asks for a well-defined real number — not merely *some* limit point of the ratios. -/
theorem hasNaturalDensity_unique {d₁ d₂ : ℝ}
    (h₁ : HasNaturalDensity d₁) (h₂ : HasNaturalDensity d₂) : d₁ = d₂ :=
  tendsto_nhds_unique h₁ h₂

/-- **Any natural density is `≥ 0`.** The density ratio is nonnegative, so its limit
is nonnegative. -/
theorem hasNaturalDensity_nonneg {d : ℝ} (h : HasNaturalDensity d) : 0 ≤ d :=
  ge_of_tendsto' h density_ratio_nonneg

/-- **Any natural density is `≤ 1`.** The density ratio never exceeds `1`, so neither
does its limit. -/
theorem hasNaturalDensity_le_one {d : ℝ} (h : HasNaturalDensity d) : d ≤ 1 :=
  le_of_tendsto' h density_ratio_le_one

/-- **Any natural density lies in `[0, 1]`.** Combining the two bounds: an answer to
OQ-03, if it exists, must be a real number in the unit interval. -/
theorem hasNaturalDensity_mem_Icc {d : ℝ} (h : HasNaturalDensity d) :
    d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hasNaturalDensity_nonneg h, hasNaturalDensity_le_one h⟩

/-- **A positive density makes the counting function unbounded.** Threading the
density view of OQ-03 back to the counting/infinitude view: if the density exists and
is positive, the count `#{n ≤ N : φ n = φ(n+1)}` is unbounded (equivalently, the set
is infinite). Contrapositively, while #1003's infinitude is open, no positive density
can be exhibited — sharpening `infinite_of_pos_density` to the counting function. -/
theorem pos_density_count_unbounded {d : ℝ} (hd : 0 < d)
    (h : HasNaturalDensity d) : ∀ M, ∃ N, M ≤ countConsecutiveEqual N :=
  infinite_iff_count_unbounded.mp (infinite_of_pos_density hd h)

/-- **Summary of the admissibility constraints (0 axioms, 0 sorries).** Any answer
`d` to OQ-03 is unique, lies in `[0, 1]`, and is positive only if the counting
function is unbounded (i.e. the solution set is infinite — the open #1003). -/
theorem oq03_answer_constraints :
    (∀ d₁ d₂ : ℝ, HasNaturalDensity d₁ → HasNaturalDensity d₂ → d₁ = d₂) ∧
    (∀ d : ℝ, HasNaturalDensity d → d ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ d : ℝ, 0 < d → HasNaturalDensity d →
      ∀ M, ∃ N, M ≤ countConsecutiveEqual N) :=
  ⟨fun _ _ => hasNaturalDensity_unique,
   fun _ => hasNaturalDensity_mem_Icc,
   fun _ => pos_density_count_unbounded⟩

/-! ## Upper density (the unconditional object)

The natural-density *limit* may fail to exist (its existence is itself open).
The *upper density* — the `limsup` of the same ratios — always exists for our
bounded sequence and is the right unconditional carrier of OQ-03.
Recovered from PR #31611. -/

/-- The upper density of the solution set: the `limsup` of the counting ratios
`count(N)/(N+1)`.  Unlike the natural density, this always exists (the sequence
is bounded in `[0,1]`). -/
noncomputable def upperDensity : ℝ :=
  limsup (fun N : ℕ => (countConsecutiveEqual N : ℝ) / (N + 1)) atTop

/-- The ratio sequence is bounded above (by `1`); used to feed the `limsup`
order lemmas. -/
theorem isBoundedUnder_ratio :
    IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ => (countConsecutiveEqual N : ℝ) / (N + 1)) :=
  ⟨1, Filter.eventually_map.mpr (by filter_upwards with N using density_ratio_le_one N)⟩

/-- The ratio sequence is cobounded above (witness `0`, since it is `≥ 0`); used
to feed the `limsup` order lemmas. -/
theorem isCoboundedUnder_ratio :
    IsCoboundedUnder (· ≤ ·) atTop
      (fun N : ℕ => (countConsecutiveEqual N : ℝ) / (N + 1)) :=
  isCoboundedUnder_le_of_le atTop density_ratio_nonneg

/-- The upper density is nonnegative. -/
theorem upperDensity_nonneg : 0 ≤ upperDensity :=
  Filter.le_limsup_of_frequently_le
    (Filter.Frequently.of_forall density_ratio_nonneg) isBoundedUnder_ratio

/-- The upper density never exceeds `1`. -/
theorem upperDensity_le_one : upperDensity ≤ 1 :=
  Filter.limsup_le_of_le isCoboundedUnder_ratio
    (by filter_upwards with N using density_ratio_le_one N)

/-- When the natural density exists it coincides with the upper density (the
`limsup` of a convergent sequence is its limit). -/
theorem upperDensity_eq_of_hasNaturalDensity {d : ℝ} (h : HasNaturalDensity d) :
    upperDensity = d :=
  h.limsup_eq

/-- If the solution set is finite, its upper density is `0`. -/
theorem upperDensity_zero_of_finite
    (hfin : ConsecutiveEqualTotients.Finite) : upperDensity = 0 :=
  (hasNaturalDensity_zero_of_finite hfin).limsup_eq

/-- A *positive upper density* already forces the solution set to be infinite —
strengthening `infinite_of_pos_density`, since the upper density always exists
whereas the natural-density limit may not.  (Proof: a finite set has upper
density `0`.) -/
theorem infinite_of_pos_upperDensity (h : 0 < upperDensity) :
    ConsecutiveEqualTotients.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  rw [upperDensity_zero_of_finite hfin] at h
  exact lt_irrefl 0 h

-- Axiom audits (expected: propext, Classical.choice, Quot.sound only)
#print axioms infinite_of_pos_upperDensity
#print axioms upperDensity_eq_of_hasNaturalDensity
#print axioms upperDensity_nonneg
#print axioms upperDensity_le_one

end Erdos1003.OQ03
