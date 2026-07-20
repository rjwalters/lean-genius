import Mathlib
import Proofs.Erdos98Problem

/-
# Erdős #98 — foundational counting bounds for distinct distances in general position
# (erdos-98-wip-01)

## The Problem

**Erdős Problem #98** (OPEN). Let `h(n)` be the minimum number of distinct
distances determined by `n` points in `ℝ²` in *general position* — no three
collinear and no four concyclic. Erdős asked whether `h(n)/n → ∞`; he could not
even prove `h(n) ≥ n`.

The scaffold `Erdos98Problem.lean` sets up the objects — `PointConfig`,
`NoThreeCollinear`, `NoFourConcyclic`, `InGeneralPosition`,
`numDistinctDistances`, and `h` — but proves **no theorems**. This file supplies
the first structural theorems: the elementary counting envelope that pins the
distinct-distance count between the trivial bounds, and the link between a
concrete configuration and the extremal quantity `h`.

## Results

1. `InGeneralPosition.injective` — a general-position configuration is injective
   (the first conjunct), so its `n` points are genuinely distinct.

2. `numDistinctDistances_le_offDiag` — the count of distinct (positive) distances
   is at most `n·(n−1)`: every positive distance is realized by an *off-diagonal*
   pair `(i, j)` with `i ≠ j`, and there are `n·(n−1)` such ordered pairs.

3. `numDistinctDistances_eq_zero_of_le_one` — fewer than two points determine no
   positive distance (`n ≤ 1 ⟹ 0`), the degenerate floor of the envelope.

4. `one_le_numDistinctDistances_of_injective` — conversely, two or more *distinct*
   points always determine at least one positive distance (`2 ≤ n ⟹ ≥ 1`).

5. `h_le_of_inGeneralPosition` — every general-position configuration is a witness
   bounding the minimum from above: `h n ≤ numDistinctDistances P`. This is the
   `Nat.sInf`-membership fact that any upper-bound construction (Pach's
   `n^{log₂ 3}`, Erdős–Füredi–Pach's `n·exp(c√log n)`) ultimately feeds.

6. `numDistinctDistances_le_choose_two` — the sharp (unordered-pair) ceiling of
   the envelope: distances are symmetric, so the count is at most `n.choose 2`,
   not merely `n·(n−1)`. Proved by factoring the symmetric distance function
   through `Sym2 (Fin n)` and invoking `Sym2.card_image_offDiag`.

## From source comments to typed statements

The scaffold left Pach's bound, the Erdős–Füredi–Pach bound, the Guth–Katz
baseline, and both forms of the conjecture as *prose comments only*. This file
turns each into an explicit Lean `Prop` over the gallery definitions
(`PachUpperBound`, `EFPUpperBound`, `GuthKatzBaseline`, `Erdos98WeakConjecture`,
`Erdos98StrongConjecture`), and proves the two relations that hold unconditionally
between them:

7. `strong_imp_weak` — `h(n)/n → ∞` implies `h(n) ≥ n` eventually (the strong
   conjecture entails the weak one). Machine-checked.

8. `weak_imp_tendsto` — even the weak conjecture already forces `h(n) → ∞`
   (a non-vacuity sanity check on the statements). Machine-checked.

The `Prop` definitions are faithful transcriptions only — Pach/EFP/Guth–Katz are
imported as *assumptions* (deep results, not reproved here) and the two
conjectures are *open* in mathematics; nothing below claims to resolve them.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Built over the gallery defs.
-/

open Finset

namespace Erdos98WIP01

variable {n : ℕ}

/-- A general-position configuration is injective (its `n` points are distinct). -/
theorem InGeneralPosition.injective {P : PointConfig n}
    (h : InGeneralPosition P) : Function.Injective P :=
  h.1

/-- **Upper envelope.** The number of distinct positive distances is at most
`n·(n−1)`: a positive distance can only come from an off-diagonal pair. -/
theorem numDistinctDistances_le_offDiag (P : PointConfig n) :
    numDistinctDistances P ≤ n * (n - 1) := by
  -- Unfold the definition to a filtered image over all ordered pairs.
  unfold numDistinctDistances
  set f : Fin n × Fin n → ℝ := fun p => dist (P p.1) (P p.2) with hf
  -- The filtered image is contained in the image of the off-diagonal.
  have hsub :
      ((univ.product univ).image f).filter (· > 0) ⊆
        (univ.offDiag).image f := by
    intro d hd
    rw [mem_filter, mem_image] at hd
    obtain ⟨⟨p, _, hpd⟩, hpos⟩ := hd
    -- `d > 0` forces `f p > 0`, hence the two points differ, hence `p.1 ≠ p.2`.
    rw [mem_image]
    refine ⟨p, ?_, hpd⟩
    rw [mem_offDiag]
    have hposp : (0 : ℝ) < f p := by rw [hpd]; exact hpos
    have hne : P p.1 ≠ P p.2 := by
      have := dist_pos.mp hposp
      simpa [hf] using this
    refine ⟨mem_univ _, mem_univ _, ?_⟩
    intro hpp
    exact hne (by rw [hpp])
  -- Card monotonicity through the subset and the image, then count the off-diagonal.
  calc (((univ.product univ).image f).filter (· > 0)).card
      ≤ ((univ.offDiag).image f).card := card_le_card hsub
    _ ≤ (univ.offDiag).card := card_image_le
    _ = n * (n - 1) := by
        rw [Finset.offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub_one]

/-- Fewer than two points determine no positive distance. -/
theorem numDistinctDistances_eq_zero_of_le_one (P : PointConfig n) (hn : n ≤ 1) :
    numDistinctDistances P = 0 := by
  have hb := numDistinctDistances_le_offDiag P
  have hz : n * (n - 1) = 0 := by interval_cases n <;> rfl
  omega

/-- Two or more distinct points determine at least one positive distance. -/
theorem one_le_numDistinctDistances_of_injective (P : PointConfig n)
    (hinj : Function.Injective P) (hn : 2 ≤ n) :
    1 ≤ numDistinctDistances P := by
  unfold numDistinctDistances
  set f : Fin n × Fin n → ℝ := fun p => dist (P p.1) (P p.2) with hf
  -- Two distinct indices `i ≠ j` exist since `2 ≤ n`.
  have hi : (0 : ℕ) < n := by omega
  have hj : (1 : ℕ) < n := by omega
  let i : Fin n := ⟨0, hi⟩
  let j : Fin n := ⟨1, hj⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  -- Their distance is positive (points distinct because `P` is injective).
  have hpts : P i ≠ P j := fun h => hij (hinj h)
  have hpos : (0 : ℝ) < f (i, j) := by
    have := dist_pos.mpr hpts
    simpa [hf] using this
  -- Hence the filtered image is nonempty.
  have hmem : f (i, j) ∈ ((univ.product univ).image f).filter (· > 0) := by
    rw [mem_filter, mem_image]
    exact ⟨⟨(i, j), by simp, rfl⟩, hpos⟩
  exact card_pos.mpr ⟨_, hmem⟩

/-- **The extremal witness fact.** Every general-position configuration bounds the
minimum distinct-distance count `h n` from above. -/
theorem h_le_of_inGeneralPosition {P : PointConfig n}
    (hgp : InGeneralPosition P) : h n ≤ numDistinctDistances P :=
  Nat.sInf_le ⟨P, hgp, rfl⟩

/-- **Sharp upper envelope.** Because `dist` is symmetric, a distinct distance is
determined by an *unordered* pair, so the count is at most `n.choose 2` — the
correct ceiling, halving the crude `n·(n−1)` bound. Proved by factoring the
symmetric distance map through `Sym2 (Fin n)`. -/
theorem numDistinctDistances_le_choose_two (P : PointConfig n) :
    numDistinctDistances P ≤ n.choose 2 := by
  unfold numDistinctDistances
  set f : Fin n × Fin n → ℝ := fun p => dist (P p.1) (P p.2) with hf
  -- The symmetric distance function factors through `Sym2 (Fin n)`.
  set g : Sym2 (Fin n) → ℝ :=
    Sym2.lift ⟨fun a b => dist (P a) (P b), fun a b => dist_comm _ _⟩ with hg
  have hfac : f = g ∘ Sym2.mk.uncurry := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [hf, hg, Function.comp_apply, Function.uncurry_apply_pair, Sym2.lift_mk]
  -- A positive distance still comes from an off-diagonal pair.
  have hsub :
      ((univ.product univ).image f).filter (· > 0) ⊆ (univ.offDiag).image f := by
    intro d hd
    rw [mem_filter, mem_image] at hd
    obtain ⟨⟨p, _, hpd⟩, hpos⟩ := hd
    rw [mem_image]
    refine ⟨p, ?_, hpd⟩
    rw [mem_offDiag]
    have hposp : (0 : ℝ) < f p := by rw [hpd]; exact hpos
    have hne : P p.1 ≠ P p.2 := by
      have := dist_pos.mp hposp; simpa [hf] using this
    exact ⟨mem_univ _, mem_univ _, fun hpp => hne (by rw [hpp])⟩
  -- Reroute the off-diagonal image through `Sym2` and count unordered pairs.
  calc (((univ.product univ).image f).filter (· > 0)).card
      ≤ ((univ.offDiag).image f).card := card_le_card hsub
    _ = (((univ.offDiag).image Sym2.mk.uncurry).image g).card := by
          rw [hfac, ← Finset.image_image]
    _ ≤ ((univ.offDiag).image Sym2.mk.uncurry).card := card_image_le
    _ = n.choose 2 := by
          rw [Sym2.card_image_offDiag]; simp

/-! ## The bounds and conjectures as typed Lean propositions

Everything below converts the source comments of `Erdos98Problem.lean` into
explicit `Prop`s over the gallery definitions. Each is annotated as an imported
assumption (a documented deep result we do not reprove) or as open. -/

open scoped Filter Topology in
/-- **Pach's upper bound** (documented result — imported as an assumption).
General-position sets exist with fewer than `n^{log₂ 3} ≈ n^{1.585}` distinct
distances, so for large `n`, `h(n) < n^{log₂ 3}`. -/
def PachUpperBound : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, (h n : ℝ) < (n : ℝ) ^ Real.logb 2 3

open scoped Filter Topology in
/-- **Erdős–Füredi–Pach upper bound** (documented result — imported as an
assumption). `h(n) < n · exp(c·√(log n))` for some `c > 0`, near-linear since the
exponential factor is `n^{o(1)}`. -/
def EFPUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop, (h n : ℝ) < n * Real.exp (c * Real.sqrt (Real.log n))

open scoped Filter Topology in
/-- **Guth–Katz baseline** (documented result — imported as an assumption). Any
`n` planar points (in particular any general-position configuration) determine
`Ω(n / log n)` distinct distances, giving the unconditional lower bound
`c·n/log n ≤ h(n)` for some `c > 0`. -/
def GuthKatzBaseline : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop, c * n / Real.log n ≤ (h n : ℝ)

open scoped Filter Topology in
/-- **Weak Erdős conjecture** (OPEN). Even `h(n) ≥ n` for all large `n` is
unknown; Erdős could not prove it. -/
def Erdos98WeakConjecture : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, n ≤ h n

open scoped Filter Topology in
/-- **Strong Erdős conjecture** (OPEN). `h(n)/n → ∞`: general position forces
superlinearly many distinct distances. This is Erdős Problem #98 itself. -/
def Erdos98StrongConjecture : Prop :=
  Filter.Tendsto (fun n : ℕ => (h n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop

/-! ## Provable relations among the typed statements -/

/-- The strong conjecture entails the weak one: if `h(n)/n → ∞` then eventually
`h(n)/n ≥ 1`, i.e. `h(n) ≥ n`. -/
theorem strong_imp_weak (H : Erdos98StrongConjecture) : Erdos98WeakConjecture := by
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ (h n : ℝ) / (n : ℝ) :=
    H.eventually_ge_atTop 1
  filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn1 hn2
  have hnp : 0 < n := hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnp
  rw [one_le_div hnpos] at hn1
  exact_mod_cast hn1

/-- Non-vacuity check: the weak conjecture already forces `h(n) → ∞`. -/
theorem weak_imp_tendsto (H : Erdos98WeakConjecture) :
    Filter.Tendsto h Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono' Filter.atTop H Filter.tendsto_id

end Erdos98WIP01
