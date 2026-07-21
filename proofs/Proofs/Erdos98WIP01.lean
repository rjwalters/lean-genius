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

open scoped Filter Topology in
/-- The scale `n ↦ c·n / log n` diverges for any `c > 0`: `log n = o(n)`
(`Real.isLittleO_log_id_atTop`) makes `log n / n → 0⁺`, so its reciprocal
`n / log n → ∞`, and multiplying by the constant `c` preserves divergence. This is
the growth rate of the Guth–Katz lower bound. -/
theorem tendsto_const_mul_div_log_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => c * (n : ℝ) / Real.log n) Filter.atTop Filter.atTop := by
  have hlo : (fun n : ℕ => Real.log n) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) Filter.atTop (𝓝 0) :=
    hlo.tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < Real.log n / (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact div_pos (Real.log_pos hn1) (by positivity)
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) Filter.atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 hpos
  have h3 : Filter.Tendsto (fun n : ℕ => (Real.log n / (n : ℝ))⁻¹) Filter.atTop Filter.atTop :=
    h2.inv_tendsto_nhdsGT_zero
  have h4 : Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) Filter.atTop Filter.atTop :=
    h3.congr (fun n => by rw [inv_div])
  exact (h4.const_mul_atTop hc).congr (fun n => by rw [mul_div_assoc])

open scoped Filter Topology in
/-- **The unconditional Guth–Katz baseline already forces `h(n) → ∞`.**  Assuming
the (proven, imported) `Ω(n / log n)` lower bound `GuthKatzBaseline`, the minimum
distinct-distance count diverges — *without* invoking either open conjecture.  This
sharpens `weak_imp_tendsto` (which derives the same conclusion from the *open* weak
conjecture): the divergence of `h` is in fact a theorem, since `c·n/log n ≤ h(n)`
and `c·n/log n → ∞` (`tendsto_const_mul_div_log_atTop`).  What remains open is the
*rate* (`h(n)/n → ∞`), not the divergence itself. -/
theorem guthKatz_imp_tendsto (H : GuthKatzBaseline) :
    Filter.Tendsto h Filter.atTop Filter.atTop := by
  obtain ⟨c, hc, hbound⟩ := H
  have hreal : Filter.Tendsto (fun n : ℕ => (h n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono' Filter.atTop hbound (tendsto_const_mul_div_log_atTop hc)
  refine Filter.tendsto_atTop.mpr (fun M => ?_)
  filter_upwards [hreal.eventually_ge_atTop (M : ℝ)] with n hn
  exact_mod_cast hn


/-- **Unconditional upper bound on the minimum.** `h n ≤ n.choose 2` for every `n`,
holding *without* a general-position existence hypothesis: either some general-position
configuration exists — then `h n ≤ numDistinctDistances P ≤ n.choose 2` by the extremal
witness fact and the sharp envelope — or the defining set is empty, in which case
`h n = sInf ∅ = 0 ≤ n.choose 2`. Combined with the unconditional divergence
`guthKatz_imp_tendsto`, this pins the minimum distinct-distance count into the envelope
`h n → ∞` yet `h n ≤ n.choose 2`.  (In the degenerate empty regime the bound is vacuous;
the interesting content is the nonempty branch, where general-position configurations do
exist for points in `ℝ²`.) -/
theorem h_le_choose_two (n : ℕ) : h n ≤ n.choose 2 := by
  rcases Set.eq_empty_or_nonempty
      {numDistinctDistances P | (P : PointConfig n) (_ : InGeneralPosition P)} with he | hne
  · rw [h, he, Nat.sInf_empty]
    exact Nat.zero_le _
  · obtain ⟨x, P, hgp, hx⟩ := hne
    calc h n ≤ numDistinctDistances P := h_le_of_inGeneralPosition hgp
      _ ≤ n.choose 2 := numDistinctDistances_le_choose_two P



/-- **Degenerate values.** `h n = 0` for `n ≤ 1`: with fewer than two points there is
no positive distance to count, and `n.choose 2 = 0` caps the minimum at `0`. A concrete
consequence of `h_le_choose_two`. -/
theorem h_eq_zero_of_le_one (hn : n ≤ 1) : h n = 0 := by
  have hle := h_le_choose_two n
  have hc : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  omega

/-! ## General-position existence in the small-cardinality regime

The interesting content of `h_le_choose_two` lives in the branch where a
general-position configuration exists (otherwise `h n = sInf ∅ = 0` vacuously).
Existence of general-position sets for **all** `n` is the deep constructive piece
(the natural parabola construction `(t, t²)` already fails *no four concyclic* —
any four parabola points whose `x`-coordinates sum to `0` are concyclic). But for
small `n` the two nondegeneracy conditions become **vacuous** — `card {i,j,k} = 3`
is impossible when `n ≤ 2`, and `card {a,b,c,d} = 4` is impossible when `n ≤ 3` —
so an injective configuration already lies in general position. -/

/-- **Vacuity of no-three-collinear for `n ≤ 2`.** Three *distinct* indices cannot
exist among `n ≤ 2` points, so the condition holds for every configuration. -/
theorem noThreeCollinear_of_le_two (P : PointConfig n) (hn : n ≤ 2) :
    NoThreeCollinear P := by
  intro i j k hcard
  exfalso
  have hle : ({i, j, k} : Finset (Fin n)).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ ({i, j, k} : Finset (Fin n)))
    simpa [Finset.card_univ, Fintype.card_fin] using this
  omega

/-- **Vacuity of no-four-concyclic for `n ≤ 3`.** Four *distinct* indices cannot
exist among `n ≤ 3` points, so the condition holds for every configuration. -/
theorem noFourConcyclic_of_le_three (P : PointConfig n) (hn : n ≤ 3) :
    NoFourConcyclic P := by
  intro a b c d hcard
  exfalso
  have hle : ({a, b, c, d} : Finset (Fin n)).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ ({a, b, c, d} : Finset (Fin n)))
    simpa [Finset.card_univ, Fintype.card_fin] using this
  omega

/-- **General-position configurations exist for `n ≤ 2`.** Both nondegeneracy
conditions are vacuous there, so the injective embedding `i ↦ (i, 0)` (distinct
first coordinates) is in general position. Consequently the defining set of `h n`
is nonempty and `h n` is a genuine attained minimum (not the `sInf ∅` junk value)
in this regime. -/
theorem exists_inGeneralPosition_of_le_two (hn : n ≤ 2) :
    ∃ P : PointConfig n, InGeneralPosition P := by
  refine ⟨fun i => EuclideanSpace.single (0 : Fin 2) (i : ℝ), ?_, ?_, ?_⟩
  · -- injective: distinct indices give distinct first coordinates
    intro i j hij
    have h0 : (i : ℝ) = (j : ℝ) := by
      have := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) hij
      simpa [PiLp.single_apply] using this
    exact Fin.ext (by exact_mod_cast h0)
  · exact noThreeCollinear_of_le_two _ hn
  · exact noFourConcyclic_of_le_three _ (by omega)

/-! ## General-position existence for `n = 3` (the first non-vacuous case)

For `n = 3` the no-four-concyclic condition is still vacuous, but no-three-collinear
becomes a genuine constraint. An explicit right triangle `(0,0), (1,0), (0,1)` witnesses
it: any line `a·x + b·y + c = 0` through all three forces `c = 0` (from `(0,0)`), then
`a = 0` (from `(1,0)`) and `b = 0` (from `(0,1)`), i.e. `(a,b,c) = 0`.  This upgrades the
attained-minimum guarantee from `n ≤ 2` to `n ≤ 3`. -/

/-- An explicit right triangle `(0,0), (1,0), (0,1)` as a configuration of three points
in `ℝ²` (each point built with `EuclideanSpace.single` for uniform coordinate access). -/
noncomputable def triangleConfig : PointConfig 3 :=
  ![EuclideanSpace.single 0 0, EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]

/-- The three triangle vertices are distinct. -/
theorem triangleConfig_injective : Function.Injective triangleConfig := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       have h0 := congrArg (fun p => p 0) hij
       have h1 := congrArg (fun p => p 1) hij
       simp only [triangleConfig, EuclideanSpace.single_apply, Matrix.cons_val_zero,
         Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1
       norm_num at h0 h1)

/-- **No three of the triangle's vertices are collinear.** The single non-vacuous case:
a line through all three vertices forces `(a,b,c) = 0`. -/
theorem noThreeCollinear_triangleConfig : NoThreeCollinear triangleConfig := by
  intro i j k hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | (simp only [triangleConfig, EuclideanSpace.single_apply, Matrix.cons_val_zero,
         Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
         mul_zero, mul_one, add_zero, zero_add] at hi hj hk
       simp only [Prod.mk.injEq]
       refine ⟨?_, ?_, ?_⟩ <;> linarith)

/-- No four of the triangle's vertices are concyclic (vacuous: only three points). -/
theorem noFourConcyclic_triangleConfig : NoFourConcyclic triangleConfig :=
  noFourConcyclic_of_le_three _ (by norm_num)

/-- **General-position configurations exist for `n = 3`.** The right triangle
`(0,0), (1,0), (0,1)` is injective, has no three collinear, and (vacuously) no four
concyclic. Hence the defining set of `h 3` is nonempty and `h 3` is a genuine attained
minimum. -/
theorem exists_inGeneralPosition_three :
    ∃ P : PointConfig 3, InGeneralPosition P :=
  ⟨triangleConfig, triangleConfig_injective, noThreeCollinear_triangleConfig,
    noFourConcyclic_triangleConfig⟩

/-- **General-position configurations exist for every `n ≤ 3`.** Combines the vacuous
small regime (`n ≤ 2`) with the explicit triangle (`n = 3`), so `h n` is an attained
minimum — not the `sInf ∅` junk value — throughout `n ≤ 3`. -/
theorem exists_inGeneralPosition_of_le_three (hn : n ≤ 3) :
    ∃ P : PointConfig n, InGeneralPosition P := by
  interval_cases n
  · exact exists_inGeneralPosition_of_le_two (by norm_num)
  · exact exists_inGeneralPosition_of_le_two (by norm_num)
  · exact exists_inGeneralPosition_of_le_two (by norm_num)
  · exact exists_inGeneralPosition_three

end Erdos98WIP01
