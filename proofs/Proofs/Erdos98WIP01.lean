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

9. `exists_inGeneralPosition` — **general-position configurations exist for *every* `n`**,
   via the uniform parabola witness `i ↦ (i+1, (i+1)²)` (strictly positive, distinct
   abscissae). This settles the constructive existence question the `n = 4` section flagged
   as "the deep constructive piece": four parabola points are concyclic iff their abscissae
   sum to `0`, so positivity of the abscissae rules concyclicity out, and strict convexity
   rules out collinearity. Consequently `h_attained` upgrades the attained-minimum guarantee
   from `n ≤ 4` to all `n` — `h n` is never the `sInf ∅` junk value.

10. `numDistinctDistances_lower` — **an elementary linear lower bound**
    `n − 1 ≤ 3·numDistinctDistances P` for every general-position `P`: a circle centred at
    any fixed point of the configuration holds at most three others (a fourth is four
    concyclic points), so the `n−1` distances from a fixed point take `≥ (n−1)/3` distinct
    values. This is the first lower bound that uses the *no-four-concyclic* hypothesis.

11. `three_mul_h_ge` — the same bound for the extremal quantity: `n − 1 ≤ 3·h n` for all `n`,
    obtained by applying (10) to the attained minimiser `h_attained`. Equivalently
    `h n ≥ (n−1)/3`.

12. `tendsto_h_atTop` — **`h n → ∞`, unconditionally.** A direct consequence of (11), needing
    *no* imported deep theorem. This sharpens `guthKatz_imp_tendsto` (which assumed the
    Guth–Katz baseline) and `weak_imp_tendsto` (which assumed the open weak conjecture): the
    divergence of `h` is elementary. Only the conjectured *rate* `h n / n → ∞` (Erdős #98)
    remains open.

13. `inGeneralPosition_comp` / `numDistinctDistances_comp_le` / `h_mono` — **`h` is monotone
    non-decreasing.** A sub-configuration `P ∘ e` selected by an injective index map inherits
    general position and has no more distinct distances; applied along `Fin.castSucc` this gives
    `h n ≤ h (n+1)`, hence `Monotone h`. The first structural comparison *across cardinalities*
    (all earlier bounds are pointwise in `n`).

14. `h_two` — **`h 2 = 1`, pinned exactly.** Squeezing the linear lower bound
    (`1 ≤ 3·h 2`) against the sharp envelope (`h 2 ≤ (2 choose 2) = 1`) determines the first
    nontrivial value with no explicit distance computation.

15. `equilateralConfig` / `numDistinctDistances_equilateralConfig` / `h_three` — **`h 3 = 1`,
    pinned exactly.** The unit equilateral triangle `(0,0), (1,0), (½, √3⁄2)` is in general
    position and has *exactly one* distinct distance (all three sides length `1`), the first
    explicit configuration whose `numDistinctDistances` is computed exactly. This gives
    `h 3 ≤ 1`; with `h_mono` and `h_two` (`1 = h 2 ≤ h 3`) it pins `h 2 = h 3 = 1`. The
    elementary envelope alone leaves only `1 ≤ h 3 ≤ 3`.

16. `centeredTriangleConfig` / `numDistinctDistances_centeredTriangleConfig_le` /
    `h_four_le_two` — **`h 4 ≤ 2`.** The classical minimum-distance witness for four points,
    the square, is *disqualified* (its vertices are concyclic). The equilateral triangle
    `(1,0), (−½,√3⁄2), (−½,−√3⁄2)` together with its centroid `(0,0)` is the smallest
    2-distance set that is general position — circumradius `1`, side `√3`, and the centroid
    is not on the vertices' circumcircle — giving `numDistinctDistances ≤ 2`, hence `h 4 ≤ 2`.

17. `not_four_equidistant` / `two_le_numDistinctDistances_four` / `h_four_ge_two` / `h_four`
    — **`h 4 = 2`, pinned exactly.** The matching lower bound rules out a 1-distance
    4-configuration: four pairwise-equidistant points would make the three difference vectors
    `pₖ₊₁−p₀` linearly independent (their Gram matrix `r²·½(I+J)` is nonsingular), impossible
    in the 2-dimensional plane (`LinearIndependent.fintype_card_le_finrank`: `3 ≤ 2`). With
    `h_four_le_two` this pins `h 4 = 2` — the first value of `h` exceeding `1`, and the first
    result to use the *dimension* of the ambient plane rather than only metric/combinatorial
    facts.

18. `h5Config` / `numDistinctDistances_h5Config_le` / `h_five_le_three` / `h_five_bounds`
    — **`h 5 ≤ 3`**, hence `2 ≤ h 5 ≤ 3`. The explicit five points `(0,0), (1,0),
    (−√3⁄2,−½), (½,√3⁄2), (½,−(2+√3)⁄2)` are in general position (no three collinear, no
    four concyclic — the five circumscribed-circle determinants are all nonzero) and realize
    *exactly three* distinct distances `1, √(2+√3), 1+√3`, giving `numDistinctDistances ≤ 3`.
    The regular pentagon (the only planar 2-distance 5-set) is concyclic, so `h 5 = 3` is
    expected; the matching lower bound `h 5 ≥ 3` needs that classification and is left open.

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
       simp [triangleConfig, EuclideanSpace.single_apply] at h0 h1)

/-- **No three of the triangle's vertices are collinear.** The single non-vacuous case:
a line through all three vertices forces `(a,b,c) = 0`. -/
theorem noThreeCollinear_triangleConfig : NoThreeCollinear triangleConfig := by
  intro i j k hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | (simp only [triangleConfig, Matrix.cons_val_zero, Matrix.cons_val_one,
         Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
         EuclideanSpace.single_apply] at hi hj hk
       norm_num at hi hj hk
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

/-! ## General-position existence for `n = 4` (the first non-vacuous no-four-concyclic case)

For `n = 4` both constraints are genuine: no three of the four points may be collinear, and
the four points may not be concyclic. The configuration `(0,0), (1,0), (0,1), (1,-1)` witnesses
both. No-three-collinear is the triangle argument applied to each of the four triples. For
no-four-concyclic, a common circle would put its centre equidistant from all four points; the
three squared-distance equalities `‖c-P₀‖² = ‖c-Pᵢ‖²` (`i = 1,2,3`) are linear in the centre's
coordinates and force `c₀ = ½`, `c₁ = ½`, and `c₀ - c₁ = 1` simultaneously — impossible. This
upgrades the attained-minimum guarantee for `h n` from `n ≤ 3` to `n ≤ 4`. -/

/-- An explicit four-point configuration `(0,0), (1,0), (0,1), (1,-1)` in `ℝ²`. Unlike the
triangle, the last vertex is not an axis point, so it is written with the `!₂[·,·]` Euclidean
vector notation. -/
noncomputable def fourConfig : PointConfig 4 :=
  ![!₂[0, 0], !₂[1, 0], !₂[0, 1], !₂[1, -1]]

/-- The four vertices are distinct. -/
theorem fourConfig_injective : Function.Injective fourConfig := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       have h0 := congrArg (fun p => p 0) hij
       have h1 := congrArg (fun p => p 1) hij
       simp [fourConfig] at h0 h1)

/-- **No three of the four vertices are collinear.** Each of the four triples is affinely
independent, so a line through any three forces `(a,b,c) = 0`. -/
theorem noThreeCollinear_fourConfig : NoThreeCollinear fourConfig := by
  intro i j k hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | (simp only [fourConfig] at hi hj hk
       norm_num at hi hj hk
       simp only [Prod.mk.injEq]
       refine ⟨?_, ?_, ?_⟩ <;> linarith)

/-- No centre is equidistant from all four vertices. The three squared-distance equalities
`‖c-P₀‖² = ‖c-Pᵢ‖²` reduce (the `c₀²`, `c₁²` terms cancelling) to linear constraints forcing
`c₀ = ½`, `c₁ = ½`, and `c₀ - c₁ = 1` at once — a contradiction. -/
theorem fourConfig_not_equidistant (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (fourConfig 0) = r) (h1 : dist center (fourConfig 1) = r)
    (h2 : dist center (fourConfig 2) = r) (h3 : dist center (fourConfig 3) = r) : False := by
  have e01 : dist center (fourConfig 0) ^ 2 = dist center (fourConfig 1) ^ 2 := by rw [h0, h1]
  have e02 : dist center (fourConfig 0) ^ 2 = dist center (fourConfig 2) ^ 2 := by rw [h0, h2]
  have e03 : dist center (fourConfig 0) ^ 2 = dist center (fourConfig 3) ^ 2 := by rw [h0, h3]
  simp only [fourConfig, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at e01 e02 e03
  nlinarith [e01, e02, e03]

/-- **No four of the four vertices are concyclic.** The only 4-subset (in every ordering) is
all four points; by `fourConfig_not_equidistant` no centre is equidistant from them, so no
common circle exists. -/
theorem noFourConcyclic_fourConfig : NoFourConcyclic fourConfig := by
  intro a b c d hcard
  rintro ⟨center, r, ha, hb, hc, hd⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact fourConfig_not_equidistant center r (by assumption) (by assumption)
        (by assumption) (by assumption)

/-- **General-position configurations exist for `n = 4`.** The configuration
`(0,0), (1,0), (0,1), (1,-1)` is injective, has no three collinear, and no four concyclic —
the first case where the concyclicity constraint is non-vacuous. Hence the defining set of
`h 4` is nonempty and `h 4` is a genuine attained minimum. -/
theorem exists_inGeneralPosition_four :
    ∃ P : PointConfig 4, InGeneralPosition P :=
  ⟨fourConfig, fourConfig_injective, noThreeCollinear_fourConfig, noFourConcyclic_fourConfig⟩

/-- **General-position configurations exist for every `n ≤ 4`.** Combines the `n ≤ 3` regime
with the explicit four-point witness, so `h n` is an attained minimum — not the `sInf ∅` junk
value — throughout `n ≤ 4`. -/
theorem exists_inGeneralPosition_of_le_four (hn : n ≤ 4) :
    ∃ P : PointConfig n, InGeneralPosition P := by
  rcases Nat.lt_or_ge n 4 with h | h
  · exact exists_inGeneralPosition_of_le_three (by omega)
  · have : n = 4 := by omega
    subst this
    exact exists_inGeneralPosition_four

/-! ## General-position existence for **every** `n` — the parabola with positive abscissae

The concrete `n ≤ 4` witnesses above are subsumed by a single uniform construction that
settles general-position existence for **all** `n`, the "deep constructive piece" the
`n = 4` header flagged as open.  The obstruction it named — "the natural parabola
construction `(t, t²)` already fails *no four concyclic*: any four parabola points whose
`x`-coordinates sum to `0` are concyclic" — is real but avoidable: four points
`(xₐ, xₐ²), …, (x_d, x_d²)` on `y = x²` are concyclic **iff** `xₐ + x_b + x_c + x_d = 0`
(the four abscissae are the roots of the monic quartic `x⁴ + (1-2c₁)x² - 2c₀x + s` cut out by
a circle `(x-c₀)² + (y-c₁)² = r²`, whose `x³`-coefficient vanishes).  Choosing the abscissae
**strictly positive** — here `xᵢ = i + 1 ∈ {1, …, n}` — makes every 4-subset sum `≥ 4 > 0`, so
no four are concyclic.  And on a parabola no three points are *ever* collinear: three points
`(xᵢ, xᵢ²)` collinear forces `a + b(xᵢ+xⱼ) = 0` for each pair, hence `b = 0` then `a = 0` then
`c = 0`.  Both nondegeneracy conditions thus hold for `parabolaConfig n`, giving
`exists_inGeneralPosition n` for all `n` and, via `Nat.sInf_mem`, that `h n` is a genuinely
attained minimum for every `n` (never the `sInf ∅` junk value). -/

/-- Distinct indices have distinct abscissae `(·) + 1` (the cast `Fin n ↪ ℕ ↪ ℝ` is injective). -/
private theorem parabola_x_ne {p q : Fin n} (hpq : p ≠ q) :
    ((p : ℕ) : ℝ) + 1 ≠ ((q : ℕ) : ℝ) + 1 := by
  intro h
  apply hpq
  have : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- A three-element `{i, j, k}` has pairwise-distinct entries. -/
private theorem card_triple_pairwise_ne {α : Type*} [DecidableEq α] {i j k : α}
    (h : ({i, j, k} : Finset α).card = 3) : i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  have card_le2 : ∀ p q : α, ({p, q} : Finset α).card ≤ 2 :=
    fun p q => (Finset.card_insert_le _ _).trans (by simp)
  have hine : i ∉ ({j, k} : Finset α) := by
    intro hmem
    rw [Finset.insert_eq_self.mpr hmem] at h
    have := card_le2 j k; omega
  have hjk2 : ({j, k} : Finset α).card = 2 := by
    have := Finset.card_insert_of_notMem hine; omega
  have hjne : j ≠ k := by
    intro hjk'; rw [hjk'] at hjk2; simp at hjk2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hine
  exact ⟨hine.1, hine.2, hjne⟩

/-- A four-element `{a, b, c, d}` has pairwise-distinct entries. -/
private theorem card_quad_pairwise_ne {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ({a, b, c, d} : Finset α).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have card_le3 : ∀ p q r : α, ({p, q, r} : Finset α).card ≤ 3 := by
    intro p q r
    calc ({p, q, r} : Finset α).card
        ≤ ({q, r} : Finset α).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({r} : Finset α).card + 1) + 1 := by
            have := Finset.card_insert_le q ({r} : Finset α); omega
      _ = 3 := by simp
  have hane : a ∉ ({b, c, d} : Finset α) := by
    intro hmem
    rw [Finset.insert_eq_self.mpr hmem] at h
    have := card_le3 b c d; omega
  have hbcd : ({b, c, d} : Finset α).card = 3 := by
    have := Finset.card_insert_of_notMem hane; omega
  have hbne : b ∉ ({c, d} : Finset α) := by
    intro hmem
    rw [Finset.insert_eq_self.mpr hmem] at hbcd
    have : ({c, d} : Finset α).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hcd2 : ({c, d} : Finset α).card = 2 := by
    have := Finset.card_insert_of_notMem hbne; omega
  have hcne : c ≠ d := by
    intro hcd'; rw [hcd'] at hcd2; simp at hcd2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hane hbne
  exact ⟨hane.1, hane.2.1, hane.2.2, hbne.1, hbne.2, hcne⟩

/-- **Parabola no-three-collinear, abstractly.** If a line `a·x + b·y + c = 0` passes through
three distinct-abscissa parabola points `(xₜ, xₜ²)`, then `(a, b, c) = 0`. Cancelling the
distinct differences turns the three incidences into `a + b(xᵢ+xⱼ) = 0`, forcing `b = 0`,
then `a = 0`, then `c = 0`. -/
private theorem parabola_collinear_trivial (xi xj xk a b c : ℝ)
    (hxij : xi ≠ xj) (hxik : xi ≠ xk) (hxjk : xj ≠ xk)
    (hi : a * xi + b * xi ^ 2 + c = 0)
    (hj : a * xj + b * xj ^ 2 + c = 0)
    (hk : a * xk + b * xk ^ 2 + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have P1 : a + b * (xi + xj) = 0 := by
    have hp : (xi - xj) * (a + b * (xi + xj)) = 0 := by linear_combination hi - hj
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hxij
    · exact hz
  have P2 : a + b * (xi + xk) = 0 := by
    have hp : (xi - xk) * (a + b * (xi + xk)) = 0 := by linear_combination hi - hk
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hxik
    · exact hz
  have hb : b = 0 := by
    have hp : (xj - xk) * b = 0 := by linear_combination P1 - P2
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hxjk
    · exact hz
  have ha : a = 0 := by linear_combination P1 - (xi + xj) * hb
  have hc : c = 0 := by linear_combination hi - xi * ha - xi ^ 2 * hb
  exact ⟨ha, hb, hc⟩

/-- **Parabola concyclicity forces zero abscissa-sum.** Four distinct-abscissa parabola points
equidistant (squared) from a common centre `(c₀, c₁)` satisfy `w + x + y + z = 0`. This is the
`x³`-coefficient-`0` Vieta relation, obtained here by three rounds of difference-and-cancel:
`(c₀-t)²+(c₁-t²)²` equal across pairs ⟹ a linear-in-centre relation `M(t,u)=0` ⟹ a
quadratic-symmetric relation `N(·,·)=0` ⟹ the abscissa sum. -/
private theorem parabola_concyclic_sum_zero (w x y z c0 c1 R : ℝ)
    (hwx : w ≠ x) (hxy : x ≠ y) (hyz : y ≠ z)
    (hwy : w ≠ y) (hwz : w ≠ z) (hxz : x ≠ z)
    (Hw : (c0 - w) ^ 2 + (c1 - w ^ 2) ^ 2 = R)
    (Hx : (c0 - x) ^ 2 + (c1 - x ^ 2) ^ 2 = R)
    (Hy : (c0 - y) ^ 2 + (c1 - y ^ 2) ^ 2 = R)
    (Hz : (c0 - z) ^ 2 + (c1 - z ^ 2) ^ 2 = R) :
    w + x + y + z = 0 := by
  -- `M(t,u) := -2c₀ + (t+u)(1 - 2c₁ + t² + u²)`: from equal squared distances, `M = 0`.
  have Mwx : -2 * c0 + (w + x) * (1 - 2 * c1 + w ^ 2 + x ^ 2) = 0 := by
    have hp : (w - x) * (-2 * c0 + (w + x) * (1 - 2 * c1 + w ^ 2 + x ^ 2)) = 0 := by
      linear_combination Hw - Hx
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hwx
    · exact hz
  have Mwy : -2 * c0 + (w + y) * (1 - 2 * c1 + w ^ 2 + y ^ 2) = 0 := by
    have hp : (w - y) * (-2 * c0 + (w + y) * (1 - 2 * c1 + w ^ 2 + y ^ 2)) = 0 := by
      linear_combination Hw - Hy
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hwy
    · exact hz
  have Mwz : -2 * c0 + (w + z) * (1 - 2 * c1 + w ^ 2 + z ^ 2) = 0 := by
    have hp : (w - z) * (-2 * c0 + (w + z) * (1 - 2 * c1 + w ^ 2 + z ^ 2)) = 0 := by
      linear_combination Hw - Hz
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hwz
    · exact hz
  -- `N(u,v) := 1 - 2c₁ + w² + wu + wv + u² + uv + v²`: cancelling `(u-v)` from `M`-differences.
  have Nxy : 1 - 2 * c1 + w ^ 2 + w * x + w * y + x ^ 2 + x * y + y ^ 2 = 0 := by
    have hp : (x - y) * (1 - 2 * c1 + w ^ 2 + w * x + w * y + x ^ 2 + x * y + y ^ 2) = 0 := by
      linear_combination Mwx - Mwy
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hxy
    · exact hz
  have Nxz : 1 - 2 * c1 + w ^ 2 + w * x + w * z + x ^ 2 + x * z + z ^ 2 = 0 := by
    have hp : (x - z) * (1 - 2 * c1 + w ^ 2 + w * x + w * z + x ^ 2 + x * z + z ^ 2) = 0 := by
      linear_combination Mwx - Mwz
    rcases mul_eq_zero.mp hp with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hxz
    · exact hz
  -- Final cancel of `(y-z)` yields the abscissa sum.
  have hp : (y - z) * (w + x + y + z) = 0 := by linear_combination Nxy - Nxz
  rcases mul_eq_zero.mp hp with hz | hz
  · exact absurd (sub_eq_zero.mp hz) hyz
  · exact hz

/-- **The uniform witness.** `parabolaConfig n i = (i+1, (i+1)²)`: `n` points on the parabola
`y = x²` with strictly positive, pairwise-distinct abscissae `1, 2, …, n`. -/
noncomputable def parabolaConfig (n : ℕ) : PointConfig n :=
  fun i => !₂[((i : ℕ) : ℝ) + 1, (((i : ℕ) : ℝ) + 1) ^ 2]

@[simp] theorem parabolaConfig_zero (i : Fin n) :
    parabolaConfig n i 0 = ((i : ℕ) : ℝ) + 1 := by simp [parabolaConfig]

@[simp] theorem parabolaConfig_one (i : Fin n) :
    parabolaConfig n i 1 = (((i : ℕ) : ℝ) + 1) ^ 2 := by simp [parabolaConfig]

/-- The `parabolaConfig` points are distinct (distinct abscissae). -/
theorem parabolaConfig_injective : Function.Injective (parabolaConfig n) := by
  intro i j hij
  have h0 : parabolaConfig n i 0 = parabolaConfig n j 0 := by rw [hij]
  simp only [parabolaConfig_zero] at h0
  have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- **No three parabola points are collinear** — for any distinct-abscissa parabola configuration
the only line through three of the points is the degenerate `(a,b,c) = 0`. -/
theorem noThreeCollinear_parabolaConfig : NoThreeCollinear (parabolaConfig n) := by
  intro i j k hcard
  obtain ⟨hij, hik, hjk⟩ := card_triple_pairwise_ne hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  simp only [parabolaConfig_zero, parabolaConfig_one] at hi hj hk
  obtain ⟨ha, hb, hc⟩ :=
    parabola_collinear_trivial _ _ _ a b c
      (parabola_x_ne hij) (parabola_x_ne hik) (parabola_x_ne hjk) hi hj hk
  rw [ha, hb, hc]

/-- **No four parabola points are concyclic** — the four positive abscissae would have to sum to
`0` (`parabola_concyclic_sum_zero`), impossible since each is `≥ 1`. -/
theorem noFourConcyclic_parabolaConfig : NoFourConcyclic (parabolaConfig n) := by
  intro a b c d hcard
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := card_quad_pairwise_ne hcard
  rintro ⟨center, r, ha, hb, hc, hd⟩
  -- Turn each `dist = r` into the squared-coordinate identity `(c₀-xₜ)² + (c₁-xₜ²)² = r²`.
  have sq : ∀ t : Fin n, dist center (parabolaConfig n t) = r →
      (center 0 - (((t : ℕ) : ℝ) + 1)) ^ 2 + (center 1 - ((((t : ℕ) : ℝ) + 1) ^ 2)) ^ 2 = r ^ 2 := by
    intro t ht
    have h2 : dist center (parabolaConfig n t) ^ 2 = r ^ 2 := by rw [ht]
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, parabolaConfig_zero,
      parabolaConfig_one, Real.dist_eq, sq_abs] at h2
    linear_combination h2
  have hsum := parabola_concyclic_sum_zero
    (((a : ℕ) : ℝ) + 1) (((b : ℕ) : ℝ) + 1) (((c : ℕ) : ℝ) + 1) (((d : ℕ) : ℝ) + 1)
    (center 0) (center 1) (r ^ 2)
    (parabola_x_ne hab) (parabola_x_ne hbc) (parabola_x_ne hcd)
    (parabola_x_ne hac) (parabola_x_ne had) (parabola_x_ne hbd)
    (sq a ha) (sq b hb) (sq c hc) (sq d hd)
  have hpos : (0 : ℝ) <
      (((a : ℕ) : ℝ) + 1) + (((b : ℕ) : ℝ) + 1) + (((c : ℕ) : ℝ) + 1) + (((d : ℕ) : ℝ) + 1) := by
    positivity
  linarith

/-- **General-position configurations exist for every `n`.** The parabola configuration
`i ↦ (i+1, (i+1)²)` is injective, has no three collinear (strict convexity), and no four
concyclic (positive abscissae cannot sum to `0`). This resolves the constructive existence
question for all `n`, superseding the concrete `n ≤ 4` witnesses above. -/
theorem exists_inGeneralPosition (n : ℕ) : ∃ P : PointConfig n, InGeneralPosition P :=
  ⟨parabolaConfig n, parabolaConfig_injective, noThreeCollinear_parabolaConfig,
    noFourConcyclic_parabolaConfig⟩

/-- **`h n` is a genuinely attained minimum for every `n`.** Because a general-position
configuration exists (`exists_inGeneralPosition`), the defining set of `h n` is nonempty, so
`Nat.sInf_mem` gives a witness `P` in general position with `numDistinctDistances P = h n` — the
minimum is realized, never the `sInf ∅ = 0` junk value. -/
theorem h_attained (n : ℕ) :
    ∃ P : PointConfig n, InGeneralPosition P ∧ numDistinctDistances P = h n := by
  have hne : {numDistinctDistances P | (P : PointConfig n) (_ : InGeneralPosition P)}.Nonempty :=
    ⟨numDistinctDistances (parabolaConfig n), parabolaConfig n,
      ⟨parabolaConfig_injective, noThreeCollinear_parabolaConfig, noFourConcyclic_parabolaConfig⟩,
      rfl⟩
  obtain ⟨P, hgp, hval⟩ := Nat.sInf_mem hne
  exact ⟨P, hgp, hval⟩

/-! ## An elementary linear lower bound `n - 1 ≤ 3 · h n`, and unconditional `h n → ∞`

The upper bounds (Pach, EFP) and `guthKatz_imp_tendsto` all rest on imported deep
theorems.  The **no-four-concyclic** hypothesis, by contrast, already forces a
*linear* lower bound by a one-line pigeonhole, straight from the gallery
definitions.  Fix a base point `P b`.  Any circle centred at `P b` meets the other
`n - 1` points in **at most three** of them — a fourth would put four points at a
common distance from `P b`, i.e. four concyclic points (centre `P b`), forbidden.
So the `n - 1` distances `dist (P b) (P i)` (`i ≠ b`) take at least `(n-1)/3`
distinct values, and each is a genuine distinct distance of the configuration.
Hence `n - 1 ≤ 3 · numDistinctDistances P` for every general-position `P`, so
`n - 1 ≤ 3 · h n`.

In particular `h n → ∞` **unconditionally** (`tendsto_h_atTop`) — no Guth–Katz
input, sharpening `guthKatz_imp_tendsto` which needed the imported `Ω(n/log n)`
baseline.  Only the *divergence* is elementary; the conjectured *rate*
`h n / n → ∞` (Erdős #98 itself) remains open, and even the linear order here is
`/3` of the conjectured `n`. -/

/-- Converse of `card_quad_pairwise_ne`: four pairwise-distinct elements form a
four-element finset. -/
private theorem card_quad_of_pairwise_ne {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 :=
  Finset.card_eq_four.mpr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩

/-- **At most three points share a distance to a fixed point.** For general-position
`P` and base index `b`, the fibre of `i ↦ dist (P b) (P i)` over any value `v`,
restricted to `i ≠ b`, has at most three elements: a fourth would give four points
equidistant from `P b` — four concyclic points (centre `P b`, radius `v`) —
contradicting `NoFourConcyclic`. -/
theorem card_fiber_dist_le_three {P : PointConfig n} (hgp : InGeneralPosition P)
    (b : Fin n) (v : ℝ) :
    ((univ.erase b).filter (fun i => dist (P b) (P i) = v)).card ≤ 3 := by
  by_contra hlt
  -- `3 < card` extracts four distinct fibre elements `i, j, k, l`.
  obtain ⟨i, hi, j, hj, k, hk, l, hl, hij, hik, hil, hjk, hjl, hkl⟩ :=
    Finset.three_lt_card.mp (not_le.mp hlt)
  rw [mem_filter] at hi hj hk hl
  -- Their common distance to `P b` makes them concyclic (centre `P b`, radius `v`).
  exact hgp.2.2 i j k l (card_quad_of_pairwise_ne hij hik hil hjk hjl hkl)
    ⟨P b, v, hi.2, hj.2, hk.2, hl.2⟩

/-- **Linear lower bound (per configuration).** Any general-position configuration of
`n ≥ 1` points has `n - 1 ≤ 3 · numDistinctDistances P`: the `n - 1` distances from a
fixed point take at least `(n-1)/3` distinct values (each circle holds `≤ 3` points),
all of which are genuine positive distinct distances. -/
theorem numDistinctDistances_lower {P : PointConfig n} (hgp : InGeneralPosition P)
    (hn : 0 < n) :
    n - 1 ≤ 3 * numDistinctDistances P := by
  let b : Fin n := ⟨0, hn⟩
  -- Pigeonhole over distances from `P b`: each fibre `≤ 3`.
  have hpig := Finset.card_le_mul_card_image (f := fun i => dist (P b) (P i))
    (univ.erase b) 3 (fun v _ => card_fiber_dist_le_three hgp b v)
  have hscard : (univ.erase b).card = n - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- The distances from `P b` are genuine positive distinct distances of `P`.
  have hsub : (univ.erase b).image (fun i => dist (P b) (P i)) ⊆
      ((univ.product univ).image
        (fun p : Fin n × Fin n => dist (P p.1) (P p.2))).filter (· > 0) := by
    intro v hv
    rw [mem_image] at hv
    obtain ⟨i, hi, hiv⟩ := hv
    rw [mem_erase] at hi
    obtain ⟨hib, _⟩ := hi
    have hpos : (0 : ℝ) < v := by
      rw [← hiv]; exact dist_pos.mpr (fun heq => hib (hgp.1 heq.symm))
    rw [mem_filter]
    exact ⟨mem_image.mpr ⟨(b, i), by simp, hiv⟩, hpos⟩
  have hle : ((univ.erase b).image (fun i => dist (P b) (P i))).card ≤
      numDistinctDistances P := by
    unfold numDistinctDistances
    exact card_le_card hsub
  calc n - 1 = (univ.erase b).card := hscard.symm
    _ ≤ 3 * ((univ.erase b).image (fun i => dist (P b) (P i))).card := hpig
    _ ≤ 3 * numDistinctDistances P := by omega

/-- **Unconditional linear lower bound on the minimum.** `n - 1 ≤ 3 · h n` for every `n`:
apply the per-configuration bound `numDistinctDistances_lower` to the attained minimiser
`h_attained`. Equivalently `h n ≥ (n-1)/3` — the first lower bound that grows with `n`,
using only the no-four-concyclic hypothesis. -/
theorem three_mul_h_ge (n : ℕ) : n - 1 ≤ 3 * h n := by
  obtain ⟨P, hgp, hval⟩ := h_attained n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [← hval]; exact numDistinctDistances_lower hgp hn

open scoped Filter Topology in
/-- **`h n → ∞`, unconditionally.** The elementary bound `n - 1 ≤ 3 · h n`
(`three_mul_h_ge`) already forces divergence — with **no** imported deep theorem, in
contrast to `guthKatz_imp_tendsto` (which assumes the Guth–Katz `Ω(n/log n)` baseline)
and `weak_imp_tendsto` (which assumes the *open* weak conjecture). Only the divergence is
elementary; the conjectured rate `h n / n → ∞` (Erdős #98) stays open. -/
theorem tendsto_h_atTop : Filter.Tendsto h Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr (fun M => ?_)
  filter_upwards [Filter.eventually_ge_atTop (3 * M + 1)] with n hn
  have hb := three_mul_h_ge n
  omega

/-! ## Monotonicity of `h`, and the pinned value `h 2 = 1`

Deleting a point from a general-position `(n+1)`-configuration leaves a
general-position `n`-configuration with **no more** distinct distances (its
distances are a sub-multiset of the larger configuration's), so the minimum `h`
cannot increase as `n` shrinks: `h` is monotone non-decreasing. This is a
*structural comparison across cardinalities* — none of the pointwise bounds above
(`three_mul_h_ge`, `h_le_choose_two`) relates `h n` to `h (n+1)`.

The engine is a single reusable fact: any sub-configuration `P ∘ e` selected by an
**injective** index map `e : Fin m ↪ Fin n` inherits general position from `P`
(`inGeneralPosition_comp`) and has at most as many distinct distances
(`numDistinctDistances_comp_le`). Monotonicity is the `e = Fin.castSucc` instance.

Squeezing the linear lower bound against the sharp envelope at `n = 2` pins the
first nontrivial value exactly: `1 ≤ 3·h 2` and `h 2 ≤ (2 choose 2) = 1` force
`h 2 = 1` (`h_two`). -/

/-- The image of a triple under an injective map has the same cardinality. -/
private theorem card_triple_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α → β} (he : Function.Injective e) (i j k : α) :
    ({e i, e j, e k} : Finset β).card = ({i, j, k} : Finset α).card := by
  have himg : ({e i, e j, e k} : Finset β) = ({i, j, k} : Finset α).image e := by
    simp only [Finset.image_insert, Finset.image_singleton]
  rw [himg, Finset.card_image_of_injective _ he]

/-- The image of a quadruple under an injective map has the same cardinality. -/
private theorem card_quad_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α → β} (he : Function.Injective e) (a b c d : α) :
    ({e a, e b, e c, e d} : Finset β).card = ({a, b, c, d} : Finset α).card := by
  have himg : ({e a, e b, e c, e d} : Finset β) = ({a, b, c, d} : Finset α).image e := by
    simp only [Finset.image_insert, Finset.image_singleton]
  rw [himg, Finset.card_image_of_injective _ he]

/-- **Sub-configurations inherit general position.** If `P : PointConfig n` is in
general position and `e : Fin m → Fin n` is injective, then the selected
sub-configuration `P ∘ e` is in general position: injectivity composes, and any
collinear/concyclic degeneracy among `P ∘ e` transports (via the injective `e`,
which preserves the `card = 3` / `card = 4` distinctness conditions) to the same
degeneracy among `P`, contradicting its general position. -/
theorem inGeneralPosition_comp {m n : ℕ} {e : Fin m → Fin n} (he : Function.Injective e)
    {P : PointConfig n} (hP : InGeneralPosition P) : InGeneralPosition (P ∘ e) := by
  obtain ⟨hinj, hcol, hcyc⟩ := hP
  refine ⟨hinj.comp he, ?_, ?_⟩
  · intro i j k hcard
    rintro ⟨a, b, c, hne, hi, hj, hk⟩
    refine hcol (e i) (e j) (e k) ?_ ⟨a, b, c, hne, hi, hj, hk⟩
    rw [card_triple_image he]; exact hcard
  · intro a b c d hcard
    rintro ⟨center, r, ha, hb, hc, hd⟩
    refine hcyc (e a) (e b) (e c) (e d) ?_ ⟨center, r, ha, hb, hc, hd⟩
    rw [card_quad_image he]; exact hcard

/-- **Sub-configurations have no more distinct distances.** Every positive distance
of `P ∘ e` is a positive distance of `P` (realized by the image pair `(e p.1, e p.2)`),
so `numDistinctDistances (P ∘ e) ≤ numDistinctDistances P`. -/
theorem numDistinctDistances_comp_le {m n : ℕ} (e : Fin m → Fin n) (P : PointConfig n) :
    numDistinctDistances (P ∘ e) ≤ numDistinctDistances P := by
  unfold numDistinctDistances
  apply Finset.card_le_card
  intro d hd
  rw [Finset.mem_filter] at hd ⊢
  obtain ⟨hd1, hpos⟩ := hd
  refine ⟨?_, hpos⟩
  rw [Finset.mem_image] at hd1 ⊢
  obtain ⟨p, -, hpd⟩ := hd1
  exact ⟨(e p.1, e p.2), by simp, hpd⟩

/-- **`h` is monotone non-decreasing.** Deleting the last point from a minimizing
general-position `(n+1)`-configuration (`h_attained`) gives, via
`inGeneralPosition_comp` and `numDistinctDistances_comp_le` along `Fin.castSucc`, a
general-position `n`-configuration with `h n ≤ numDistinctDistances ≤ h (n+1)`. -/
theorem h_mono : Monotone h := by
  apply monotone_nat_of_le_succ
  intro n
  obtain ⟨P, hgp, hval⟩ := h_attained (n + 1)
  have hgpQ : InGeneralPosition (P ∘ Fin.castSucc) :=
    inGeneralPosition_comp (Fin.castSucc_injective n) hgp
  calc h n ≤ numDistinctDistances (P ∘ Fin.castSucc) := h_le_of_inGeneralPosition hgpQ
    _ ≤ numDistinctDistances P := numDistinctDistances_comp_le _ _
    _ = h (n + 1) := hval

/-- **`h 2 = 1`, pinned exactly.** Two general-position points determine exactly one
positive distance. The linear lower bound gives `1 ≤ 3·h 2` (so `h 2 ≥ 1`) and the
sharp unordered-pair envelope gives `h 2 ≤ (2 choose 2) = 1`; the two squeeze `h 2`
to `1`. This is the first exactly-determined value of `h`, obtained with no explicit
distance computation — purely from the two bounds. -/
theorem h_two : h 2 = 1 := by
  have hlo := three_mul_h_ge 2
  have hhi := h_le_choose_two 2
  have hchoose : Nat.choose 2 2 = 1 := by decide
  omega

/-! ## The pinned value `h 3 = 1` via an explicit equilateral triangle

`h 2 = 1` and `h_mono` give `1 = h 2 ≤ h 3`, so `h 3 ≥ 1`.  For the matching
upper bound we exhibit a *single* general-position 3-configuration with exactly
**one** distinct distance — the equilateral triangle `(0,0), (1,0), (½, √3⁄2)`,
all three pairwise distances equal to `1`.  This is the first time an explicit
configuration's `numDistinctDistances` is computed *exactly* (earlier witnesses
only bounded it), and it forces `h 3 ≤ 1`.  Squeezing, `h 2 = h 3 = 1`.

The linear lower bound is far from tight here — `three_mul_h_ge 3` gives only
`h 3 ≥ 1` and `h_le_choose_two 3` only `h 3 ≤ 3`; the exact value needs the
equilateral witness, not the elementary envelope. -/

/-- An explicit unit **equilateral triangle** `(0,0), (1,0), (½, √3⁄2)` in `ℝ²`.
All three pairwise distances equal `1`, so it realizes the minimum possible
distinct-distance count for three non-collinear points. -/
noncomputable def equilateralConfig : PointConfig 3 :=
  ![!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]]

/-- The three equilateral vertices are distinct (their abscissae `0, 1, ½` already
differ, so the `x`-coordinate alone separates every pair). -/
theorem equilateralConfig_injective : Function.Injective equilateralConfig := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       have h0 := congrArg (fun p => p 0) hij
       norm_num [equilateralConfig] at h0)

/-- **No three equilateral vertices are collinear.** A line `a·x + b·y + c = 0`
through all three forces `c = 0` (from `(0,0)`), then `a = 0` (from `(1,0)`), then
`b·(√3⁄2) = 0`; since `√3 > 0` this gives `b = 0`, i.e. `(a,b,c) = 0`. -/
theorem noThreeCollinear_equilateralConfig : NoThreeCollinear equilateralConfig := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro i j k hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | (simp only [equilateralConfig] at hi hj hk
       norm_num at hi hj hk
       simp only [Prod.mk.injEq]
       refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hs, hi, hj, hk])

/-- No four equilateral vertices are concyclic (vacuous: only three points). -/
theorem noFourConcyclic_equilateralConfig : NoFourConcyclic equilateralConfig :=
  noFourConcyclic_of_le_three _ (by norm_num)

/-- **The equilateral triangle is in general position.** -/
theorem inGeneralPosition_equilateralConfig : InGeneralPosition equilateralConfig :=
  ⟨equilateralConfig_injective, noThreeCollinear_equilateralConfig,
    noFourConcyclic_equilateralConfig⟩

/-- **Every side of the equilateral triangle has length `1`.** For distinct indices
`i ≠ j`, `dist (equilateralConfig i) (equilateralConfig j) = 1`: each squared side is
`(Δx)² + (Δy)² = 1` (using `(√3)² = 3`), and the distance is the nonnegative square
root of `1`. -/
theorem equilateral_dist_off {i j : Fin 3} (hij : i ≠ j) :
    dist (equilateralConfig i) (equilateralConfig j) = 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsum : (∑ k : Fin 2,
      dist (equilateralConfig i k) (equilateralConfig j k) ^ 2) = 1 := by
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (simp only [equilateralConfig, Fin.sum_univ_two, Real.dist_eq, sq_abs]
         norm_num [hs]
         all_goals nlinarith [hs])
  rw [EuclideanSpace.dist_eq, hsum, Real.sqrt_one]

/-- **The equilateral triangle has exactly one distinct distance.** Every off-diagonal
pair realizes the common side length `1`, and the diagonal pairs contribute `0` (filtered
out); so the set of positive distances is `{1}`, of cardinality `1`. -/
theorem numDistinctDistances_equilateralConfig :
    numDistinctDistances equilateralConfig = 1 := by
  -- Any positive distance of the configuration equals `1`.
  have hoff : ∀ p : Fin 3 × Fin 3,
      (0 : ℝ) < dist (equilateralConfig p.1) (equilateralConfig p.2) →
      dist (equilateralConfig p.1) (equilateralConfig p.2) = 1 := by
    rintro ⟨x, y⟩ hpos
    by_cases hxy : x = y
    · subst hxy; simp only [dist_self, lt_self_iff_false] at hpos
    · exact equilateral_dist_off hxy
  unfold numDistinctDistances
  have hset : ((univ.product univ).image
      (fun p : Fin 3 × Fin 3 => dist (equilateralConfig p.1) (equilateralConfig p.2))).filter
      (· > 0) = {1} := by
    apply Finset.ext
    intro d
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton, gt_iff_lt]
    constructor
    · rintro ⟨⟨p, -, hp⟩, hpos⟩
      rw [← hp]; exact hoff p (by rw [hp]; exact hpos)
    · rintro rfl
      refine ⟨⟨(0, 1), ?_, equilateral_dist_off (by decide)⟩, by norm_num⟩
      simp
  rw [hset, Finset.card_singleton]

/-- **`h 3 = 1`, pinned exactly.** The upper bound `h 3 ≤ 1` comes from the equilateral
witness (`numDistinctDistances_equilateralConfig`); the lower bound `1 = h 2 ≤ h 3` from
monotonicity (`h_mono`) and the pinned `h_two`. Together with `h_two` this shows
`h 2 = h 3 = 1` — the elementary envelope alone leaves `1 ≤ h 3 ≤ 3`. -/
theorem h_three : h 3 = 1 := by
  have hle : h 3 ≤ 1 := by
    have hwit := h_le_of_inGeneralPosition inGeneralPosition_equilateralConfig
    rwa [numDistinctDistances_equilateralConfig] at hwit
  have hge : 1 ≤ h 3 :=
    calc 1 = h 2 := h_two.symm
      _ ≤ h 3 := h_mono (by norm_num)
  omega

/-! ## The upper bound `h 4 ≤ 2` via an equilateral triangle plus its centroid

For four points both nondegeneracy constraints are genuine, and the classical
minimal-distance witness — the **square** — is *disqualified*: its four vertices are
concyclic, so the square is not a general-position configuration.  The smallest
2-distance set that survives is the equilateral triangle `(1,0), (−½,√3⁄2), (−½,−√3⁄2)`
together with its **centroid** `(0,0)`.  The centroid lies at distance `1` (the
circumradius) from each vertex, and the three sides have the common length `√3`, so only
the two distances `1` and `√3` occur: `numDistinctDistances ≤ 2`, hence `h 4 ≤ 2`.

The configuration is in general position: no three of the four points are collinear
(the centroid is interior to the triangle), and the four are **not** concyclic — the
only point equidistant from the three vertices is their circumcenter, the centroid
itself, which is at distance `0 ≠ 1` from itself, so no circle passes through all four.
Combined with `three_mul_h_ge 4` (which gives only `h 4 ≥ 1`) this traps `1 ≤ h 4 ≤ 2`;
the exact value `h 4 = 2` additionally requires the lower bound `h 4 ≥ 2` — four
pairwise-equidistant points are impossible in the plane — recorded as the next step. -/

/-- The equilateral triangle `(1,0), (−½,√3⁄2), (−½,−√3⁄2)` together with its centroid
`(0,0)`, as a four-point configuration in `ℝ²`.  A 2-distance set (circumradius `1`,
side length `√3`) which — unlike the square — is not concyclic. -/
noncomputable def centeredTriangleConfig : PointConfig 4 :=
  ![!₂[0, 0], !₂[1, 0], !₂[-1/2, Real.sqrt 3 / 2], !₂[-1/2, -(Real.sqrt 3 / 2)]]

/-- **Every pairwise distance of the centred triangle is `1` or `√3`.** For distinct
indices the distance is either the circumradius `1` (centroid to a vertex) or the common
side length `√3` (between two vertices): its square is `1` or `3`, and the nonnegative
square root is `1` or `√3`. -/
theorem centeredTriangleConfig_dist_mem {i j : Fin 4} (hij : i ≠ j) :
    dist (centeredTriangleConfig i) (centeredTriangleConfig j) ∈
      ({1, Real.sqrt 3} : Finset ℝ) := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd0 : 0 ≤ dist (centeredTriangleConfig i) (centeredTriangleConfig j) := dist_nonneg
  have hsq : dist (centeredTriangleConfig i) (centeredTriangleConfig j) ^ 2 = 1 ∨
      dist (centeredTriangleConfig i) (centeredTriangleConfig j) ^ 2 = 3 := by
    rw [EuclideanSpace.dist_sq_eq]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (left
         simp only [centeredTriangleConfig, Fin.sum_univ_two, Real.dist_eq, sq_abs]
         norm_num [hs2] <;> nlinarith [hs2])
      | (right
         simp only [centeredTriangleConfig, Fin.sum_univ_two, Real.dist_eq, sq_abs]
         norm_num [hs2] <;> nlinarith [hs2])
  rcases hsq with h | h
  · have hone : dist (centeredTriangleConfig i) (centeredTriangleConfig j) = 1 := by
      rw [← Real.sqrt_sq hd0, h, Real.sqrt_one]
    simp [hone]
  · have hrt : dist (centeredTriangleConfig i) (centeredTriangleConfig j) = Real.sqrt 3 := by
      rw [← Real.sqrt_sq hd0, h]
    simp [hrt]

/-- The four points are distinct: every pairwise distance is positive (it is `1` or `√3`),
so equal indices are forced. -/
theorem centeredTriangleConfig_injective : Function.Injective centeredTriangleConfig := by
  intro i j hij
  by_contra hne
  have hmem := centeredTriangleConfig_dist_mem hne
  rw [hij, dist_self] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · norm_num at h
  · have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    rw [← h] at hpos
    exact lt_irrefl 0 hpos

set_option maxHeartbeats 1000000 in
/-- **No three of the four points are collinear.** A line through any three forces
`(a,b,c) = 0`; the two vertices sharing the abscissa `−½` need `√3 > 0` to conclude. -/
theorem noThreeCollinear_centeredTriangleConfig : NoThreeCollinear centeredTriangleConfig := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro i j k hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | (simp only [centeredTriangleConfig] at hi hj hk
       norm_num at hi hj hk
       simp only [Prod.mk.injEq]
       refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hs, hi, hj, hk])

/-- **No centre is equidistant from all four points.** The squared-distance equality with
`P₁` forces `c₀ = ½`, while those with `P₂, P₃` give `c₀ + 1 ∓ c₁√3 = 0`; adding the latter
two yields `c₀ = −1`, contradicting `c₀ = ½`. -/
theorem centeredTriangle_not_equidistant (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (centeredTriangleConfig 0) = r)
    (h1 : dist center (centeredTriangleConfig 1) = r)
    (h2 : dist center (centeredTriangleConfig 2) = r)
    (h3 : dist center (centeredTriangleConfig 3) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (centeredTriangleConfig 0) ^ 2 = dist center (centeredTriangleConfig 1) ^ 2 := by
    rw [h0, h1]
  have e02 : dist center (centeredTriangleConfig 0) ^ 2 = dist center (centeredTriangleConfig 2) ^ 2 := by
    rw [h0, h2]
  have e03 : dist center (centeredTriangleConfig 0) ^ 2 = dist center (centeredTriangleConfig 3) ^ 2 := by
    rw [h0, h3]
  simp only [centeredTriangleConfig, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at e01 e02 e03
  nlinarith [e01, e02, e03, hs2]

set_option maxHeartbeats 1000000 in
/-- **No four of the four points are concyclic.** The only 4-subset (in every ordering) is
all four points; by `centeredTriangle_not_equidistant` no centre is equidistant from them,
so no common circle exists. -/
theorem noFourConcyclic_centeredTriangleConfig : NoFourConcyclic centeredTriangleConfig := by
  intro a b c d hcard
  rintro ⟨center, r, ha, hb, hc, hd⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact centeredTriangle_not_equidistant center r (by assumption) (by assumption)
        (by assumption) (by assumption)

/-- **The centred triangle is in general position.** -/
theorem inGeneralPosition_centeredTriangleConfig : InGeneralPosition centeredTriangleConfig :=
  ⟨centeredTriangleConfig_injective, noThreeCollinear_centeredTriangleConfig,
    noFourConcyclic_centeredTriangleConfig⟩

/-- **The centred triangle realizes at most two distinct distances.** Every positive
pairwise distance lies in the two-element set `{1, √3}` (`centeredTriangleConfig_dist_mem`),
so the distinct-distance count is at most `2`. -/
theorem numDistinctDistances_centeredTriangleConfig_le :
    numDistinctDistances centeredTriangleConfig ≤ 2 := by
  unfold numDistinctDistances
  have hsub :
      ((univ.product univ).image
          (fun p : Fin 4 × Fin 4 =>
            dist (centeredTriangleConfig p.1) (centeredTriangleConfig p.2))).filter (· > 0)
        ⊆ ({1, Real.sqrt 3} : Finset ℝ) := by
    intro d hd
    rw [mem_filter, mem_image] at hd
    obtain ⟨⟨p, -, hpd⟩, hpos⟩ := hd
    have hne : p.1 ≠ p.2 := by
      intro he
      rw [he, dist_self] at hpd
      rw [← hpd] at hpos
      exact lt_irrefl 0 hpos
    rw [← hpd]
    exact centeredTriangleConfig_dist_mem hne
  calc (((univ.product univ).image
          (fun p : Fin 4 × Fin 4 =>
            dist (centeredTriangleConfig p.1) (centeredTriangleConfig p.2))).filter (· > 0)).card
      ≤ ({1, Real.sqrt 3} : Finset ℝ).card := card_le_card hsub
    _ ≤ 2 := by
        have hc := Finset.card_insert_le (1 : ℝ) ({Real.sqrt 3} : Finset ℝ)
        simpa using hc

/-- **`h 4 ≤ 2`, an exact upper bound.** The centred-triangle witness is in general
position and realizes at most two distinct distances, so it bounds the minimum:
`h 4 ≤ numDistinctDistances ≤ 2`.  With the linear lower bound `three_mul_h_ge 4`
(`h 4 ≥ 1`) this traps `1 ≤ h 4 ≤ 2`; only the matching lower bound `h 4 ≥ 2` (no four
equidistant points in the plane) is missing to pin `h 4 = 2`. -/
theorem h_four_le_two : h 4 ≤ 2 :=
  le_trans (h_le_of_inGeneralPosition inGeneralPosition_centeredTriangleConfig)
    numDistinctDistances_centeredTriangleConfig_le

/-! ## The matching lower bound `h 4 ≥ 2`: four equidistant points are impossible in ℝ²

The upper bound leaves `1 ≤ h 4 ≤ 2`.  To pin `h 4 = 2` we rule out a general-position
4-configuration with a *single* distinct distance — i.e. four points all at a common
pairwise distance `r`.  Such a **regular simplex** cannot embed in the plane: the three
difference vectors `vₖ = pₖ₊₁ − p₀` would be pairwise at inner product `r²/2` and each of
squared norm `r²`, so their Gram matrix `r²·(½·(I + J))` is nonsingular — the three
vectors are linearly independent.  But `EuclideanSpace ℝ (Fin 2)` has dimension `2`, and
three independent vectors cannot fit (`LinearIndependent.fintype_card_le_finrank`:
`3 ≤ 2`), a contradiction.  This is the first result in the file to use the *dimension*
of the ambient plane (all earlier bounds are metric/combinatorial). -/

open scoped InnerProductSpace in
/-- **No four points in the plane are pairwise equidistant.** For an injective
`p : Fin 4 → ℝ²` with all pairwise distances equal to `r`, the three difference vectors
`p₁−p₀, p₂−p₀, p₃−p₀` are linearly independent (their Gram matrix `r²·½(I+J)` has full
rank), so three independent vectors would live in the 2-dimensional plane — impossible. -/
theorem not_four_equidistant {p : Fin 4 → EuclideanSpace ℝ (Fin 2)}
    (hinj : Function.Injective p) (r : ℝ)
    (hd : ∀ i j : Fin 4, i ≠ j → dist (p i) (p j) = r) : False := by
  have hr : 0 < r := by
    rw [← hd 0 1 (by decide)]
    exact dist_pos.mpr (hinj.ne (by decide))
  -- difference vectors from the base point `p 0`
  set v : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun k => p k.succ - p 0 with hv
  have hnorm : ∀ k : Fin 3, ‖v k‖ = r := by
    intro k
    simp only [hv]
    rw [← dist_eq_norm]
    exact hd _ _ (Fin.succ_ne_zero k)
  have hself : ∀ k : Fin 3, inner ℝ (v k) (v k) = r ^ 2 := by
    intro k
    rw [real_inner_self_eq_norm_sq, hnorm k]
  have hcross : ∀ i j : Fin 3, i ≠ j → inner ℝ (v i) (v j) = r ^ 2 / 2 := by
    intro i j hij
    have hnij : ‖v i - v j‖ = r := by
      simp only [hv]
      rw [show p i.succ - p 0 - (p j.succ - p 0) = p i.succ - p j.succ from by abel,
        ← dist_eq_norm]
      exact hd _ _ ((Fin.succ_injective _).ne hij)
    have hns := norm_sub_sq_real (v i) (v j)
    rw [hnij, hnorm i, hnorm j] at hns
    linarith
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hip : ∀ j : Fin 3, ∑ k : Fin 3, g k * inner ℝ (v k) (v j) = 0 := by
      intro j
      have h0 : inner ℝ (∑ k : Fin 3, g k • v k) (v j) = 0 := by
        rw [hg]; exact inner_zero_left _
      rw [sum_inner] at h0
      simp_rw [real_inner_smul_left] at h0
      exact h0
    have e0 := hip 0; have e1 := hip 1; have e2 := hip 2
    simp only [Fin.sum_univ_three] at e0 e1 e2
    rw [hself 0, hcross 1 0 (by decide), hcross 2 0 (by decide)] at e0
    rw [hcross 0 1 (by decide), hself 1, hcross 2 1 (by decide)] at e1
    rw [hcross 0 2 (by decide), hcross 1 2 (by decide), hself 2] at e2
    have hr2 : r ^ 2 ≠ 0 := (pow_pos hr 2).ne'
    have f0 : g 0 + g 1 / 2 + g 2 / 2 = 0 := by
      have h : r ^ 2 * (g 0 + g 1 / 2 + g 2 / 2) = 0 := by linear_combination e0
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr2
      · exact h'
    have f1 : g 0 / 2 + g 1 + g 2 / 2 = 0 := by
      have h : r ^ 2 * (g 0 / 2 + g 1 + g 2 / 2) = 0 := by linear_combination e1
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr2
      · exact h'
    have f2 : g 0 / 2 + g 1 / 2 + g 2 = 0 := by
      have h : r ^ 2 * (g 0 / 2 + g 1 / 2 + g 2) = 0 := by linear_combination e2
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr2
      · exact h'
    have hg0 : g 0 = 0 := by linarith [f0, f1, f2]
    have hg1 : g 1 = 0 := by linarith [f0, f1, f2]
    have hg2 : g 2 = 0 := by linarith [f0, f1, f2]
    intro i
    fin_cases i <;> assumption
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin, finrank_euclideanSpace_fin] at hcard
  omega

/-- **Two or more distinct distances for four distinct points.** A four-point injective
configuration has `numDistinctDistances ≥ 2`: it has `≥ 1` (two points determine a
positive distance), and a count of exactly `1` would force all six pairwise distances
equal — four equidistant points, ruled out by `not_four_equidistant`. -/
theorem two_le_numDistinctDistances_four {P : PointConfig 4}
    (hinj : Function.Injective P) : 2 ≤ numDistinctDistances P := by
  by_contra hlt
  push_neg at hlt
  have h1 : 1 ≤ numDistinctDistances P :=
    one_le_numDistinctDistances_of_injective P hinj (by norm_num)
  have heq : numDistinctDistances P = 1 := by omega
  unfold numDistinctDistances at heq
  obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp heq
  have hall : ∀ i j : Fin 4, i ≠ j → dist (P i) (P j) = r := by
    intro i j hij
    have hpos : (0 : ℝ) < dist (P i) (P j) := dist_pos.mpr (hinj.ne hij)
    have hmem : dist (P i) (P j) ∈
        ((univ.product univ).image
          (fun q : Fin 4 × Fin 4 => dist (P q.1) (P q.2))).filter (· > 0) := by
      rw [mem_filter]
      exact ⟨mem_image.mpr ⟨(i, j), by simp, rfl⟩, hpos⟩
    rw [hr_eq, mem_singleton] at hmem
    exact hmem
  exact not_four_equidistant hinj r hall

/-- **`h 4 ≥ 2`.** The attained minimiser (`h_attained 4`) is injective, so it has at
least two distinct distances; hence the minimum is `≥ 2`. -/
theorem h_four_ge_two : 2 ≤ h 4 := by
  obtain ⟨P, hgp, hval⟩ := h_attained 4
  rw [← hval]
  exact two_le_numDistinctDistances_four hgp.1

/-- **`h 4 = 2`, pinned exactly.** The centred-triangle witness gives `h 4 ≤ 2`
(`h_four_le_two`) and the impossibility of four equidistant points gives `h 4 ≥ 2`
(`h_four_ge_two`).  This is the first value of `h` strictly greater than `1`, and the
first to use both nondegeneracy hypotheses non-vacuously together with the planar
dimension bound. -/
theorem h_four : h 4 = 2 :=
  le_antisymm h_four_le_two h_four_ge_two

/-! ## The upper bound `h 5 ≤ 3` via an explicit three-distance five-point witness

For five points the pinning of `h` runs into genuine difficulty: the linear lower bound
`three_mul_h_ge 5` gives only `h 5 ≥ 2`, and monotonicity (`h_four`, `h_mono`) gives the
same `h 5 ≥ 2`, while the natural 2-distance candidate — the **regular pentagon** — is
*disqualified* (its five vertices are concyclic).  Indeed the only planar 2-distance set
of five points is the regular pentagon, so no general-position 5-set has two distances and
in fact `h 5 = 3`; the matching lower bound `h 5 ≥ 3` requires that classification and is
left open here.

What *is* elementary is the **upper bound** `h 5 ≤ 3`.  The five points

  `A = (0,0)`, `B = (1,0)`, `C = (−√3⁄2, −½)`, `D = (½, √3⁄2)`, `E = (½, −(2+√3)⁄2)`

realize **exactly three** distinct distances — `1`, `√(2+√3)`, and `1+√3` — with the
multiplicities

  `1`         : `AB, AC, AD, BD`            (four pairs, squared distance `1`),
  `√(2+√3)`   : `AE, BC, BE, CD, CE`        (five pairs, squared distance `2+√3`),
  `1+√3`      : `DE`                        (one pair, squared distance `(1+√3)² = 4+2√3`).

The configuration is in general position: no three of the five are collinear (all ten
triangle areas are nonzero), and no four are concyclic (each of the five quadruples has a
nonzero circumscribed-circle determinant — `1+√3⁄2`, `2+√3`, `5⁄2+3√3⁄2`).  Hence it
witnesses `h 5 ≤ numDistinctDistances ≤ 3`, trapping `2 ≤ h 5 ≤ 3`. -/

/-- The explicit five-point configuration `A=(0,0)`, `B=(1,0)`, `C=(−√3⁄2,−½)`,
`D=(½,√3⁄2)`, `E=(½,−(2+√3)⁄2)` in `ℝ²`.  A three-distance set (`1`, `√(2+√3)`, `1+√3`)
in general position — the first configuration in the file whose distinct-distance count is
exactly three. -/
noncomputable def h5Config : PointConfig 5 :=
  ![!₂[0, 0], !₂[1, 0], !₂[-(Real.sqrt 3 / 2), -(1 / 2)],
    !₂[1 / 2, Real.sqrt 3 / 2], !₂[1 / 2, -((2 + Real.sqrt 3) / 2)]]

set_option maxHeartbeats 1600000 in
/-- **Every pairwise squared distance of `h5Config` is `1`, `2+√3`, or `(1+√3)²`.** A direct
coordinate computation over all off-diagonal pairs, using `√3² = 3`. -/
theorem h5Config_dist_sq {i j : Fin 5} (hij : i ≠ j) :
    dist (h5Config i) (h5Config j) ^ 2 = 1 ∨
    dist (h5Config i) (h5Config j) ^ 2 = 2 + Real.sqrt 3 ∨
    dist (h5Config i) (h5Config j) ^ 2 = (1 + Real.sqrt 3) ^ 2 := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.dist_sq_eq]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp only [h5Config, Fin.sum_univ_two, Real.dist_eq, sq_abs]
       first
       | (left; norm_num [hs2] <;> nlinarith [hs2])
       | (right; left; norm_num [hs2] <;> nlinarith [hs2])
       | (right; right; norm_num [hs2] <;> nlinarith [hs2]))

/-- **Every pairwise distance of `h5Config` lies in `{1, √(2+√3), 1+√3}`.** The nonnegative
square root of `h5Config_dist_sq`; `(1+√3)² ↦ 1+√3` since `1+√3 ≥ 0`. -/
theorem h5Config_dist_mem {i j : Fin 5} (hij : i ≠ j) :
    dist (h5Config i) (h5Config j) ∈
      ({1, Real.sqrt (2 + Real.sqrt 3), 1 + Real.sqrt 3} : Finset ℝ) := by
  have hd0 : 0 ≤ dist (h5Config i) (h5Config j) := dist_nonneg
  have h3nn : (0 : ℝ) ≤ 1 + Real.sqrt 3 := by positivity
  rcases h5Config_dist_sq hij with h | h | h
  · have he : dist (h5Config i) (h5Config j) = 1 := by
      rw [← Real.sqrt_sq hd0, h, Real.sqrt_one]
    simp [he]
  · have he : dist (h5Config i) (h5Config j) = Real.sqrt (2 + Real.sqrt 3) := by
      rw [← Real.sqrt_sq hd0, h]
    simp [he]
  · have he : dist (h5Config i) (h5Config j) = 1 + Real.sqrt 3 := by
      rw [← Real.sqrt_sq hd0, h, Real.sqrt_sq h3nn]
    simp [he]

/-- The five points are distinct: every pairwise distance lies in `{1, √(2+√3), 1+√3}`, all
of whose elements are positive, so equal indices are forced. -/
theorem h5Config_injective : Function.Injective h5Config := by
  intro i j hij
  by_contra hne
  have hmem := h5Config_dist_mem hne
  rw [hij, dist_self] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (0 : ℝ) < Real.sqrt (2 + Real.sqrt 3) := Real.sqrt_pos.mpr (by positivity)
  rcases hmem with h | h | h
  · norm_num at h
  · linarith [hs2]
  · linarith [hs]

set_option maxHeartbeats 1600000 in
/-- **No three of the five points are collinear.** A line through any three forces
`(a,b,c) = 0`; the cases involving the `√3`-abscissa points need `√3 > 0`. -/
theorem noThreeCollinear_h5Config : NoThreeCollinear h5Config := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  intro i j k hcard
  rintro ⟨a, b, c, hne, hi, hj, hk⟩
  apply hne
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd hcard (by decide)
    | (simp only [h5Config] at hi hj hk
       norm_num at hi hj hk
       simp only [Prod.mk.injEq]
       refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hs, hs2, hi, hj, hk])

/-- No centre is equidistant from `A, B, C, D` (`h5Config 0,1,2,3`). The three
squared-distance equalities relative to `A` are linear in the centre and inconsistent. -/
theorem h5_not_equidistant_0123 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h5Config 0) = r) (h1 : dist center (h5Config 1) = r)
    (h2 : dist center (h5Config 2) = r) (h3 : dist center (h5Config 3) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h5Config 0) ^ 2 = dist center (h5Config 1) ^ 2 := by rw [h0, h1]
  have e02 : dist center (h5Config 0) ^ 2 = dist center (h5Config 2) ^ 2 := by rw [h0, h2]
  have e03 : dist center (h5Config 0) ^ 2 = dist center (h5Config 3) ^ 2 := by rw [h0, h3]
  simp only [h5Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at e01 e02 e03
  nlinarith [e01, e02, e03, hs2]

/-- No centre is equidistant from `A, B, C, E` (`h5Config 0,1,2,4`). -/
theorem h5_not_equidistant_0124 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h5Config 0) = r) (h1 : dist center (h5Config 1) = r)
    (h2 : dist center (h5Config 2) = r) (h4 : dist center (h5Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h5Config 0) ^ 2 = dist center (h5Config 1) ^ 2 := by rw [h0, h1]
  have e02 : dist center (h5Config 0) ^ 2 = dist center (h5Config 2) ^ 2 := by rw [h0, h2]
  have e04 : dist center (h5Config 0) ^ 2 = dist center (h5Config 4) ^ 2 := by rw [h0, h4]
  simp only [h5Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at e01 e02 e04
  nlinarith [e01, e02, e04, hs2]

/-- No centre is equidistant from `A, B, D, E` (`h5Config 0,1,3,4`). -/
theorem h5_not_equidistant_0134 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h5Config 0) = r) (h1 : dist center (h5Config 1) = r)
    (h3 : dist center (h5Config 3) = r) (h4 : dist center (h5Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e01 : dist center (h5Config 0) ^ 2 = dist center (h5Config 1) ^ 2 := by rw [h0, h1]
  have e03 : dist center (h5Config 0) ^ 2 = dist center (h5Config 3) ^ 2 := by rw [h0, h3]
  have e04 : dist center (h5Config 0) ^ 2 = dist center (h5Config 4) ^ 2 := by rw [h0, h4]
  simp only [h5Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at e01 e03 e04
  nlinarith [e01, e03, e04, hs2]

/-- No centre is equidistant from `A, C, D, E` (`h5Config 0,2,3,4`). -/
theorem h5_not_equidistant_0234 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h0 : dist center (h5Config 0) = r) (h2 : dist center (h5Config 2) = r)
    (h3 : dist center (h5Config 3) = r) (h4 : dist center (h5Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e02 : dist center (h5Config 0) ^ 2 = dist center (h5Config 2) ^ 2 := by rw [h0, h2]
  have e03 : dist center (h5Config 0) ^ 2 = dist center (h5Config 3) ^ 2 := by rw [h0, h3]
  have e04 : dist center (h5Config 0) ^ 2 = dist center (h5Config 4) ^ 2 := by rw [h0, h4]
  simp only [h5Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at e02 e03 e04
  nlinarith [e02, e03, e04, hs2]

/-- No centre is equidistant from `B, C, D, E` (`h5Config 1,2,3,4`). -/
theorem h5_not_equidistant_1234 (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (h1 : dist center (h5Config 1) = r) (h2 : dist center (h5Config 2) = r)
    (h3 : dist center (h5Config 3) = r) (h4 : dist center (h5Config 4) = r) : False := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e12 : dist center (h5Config 1) ^ 2 = dist center (h5Config 2) ^ 2 := by rw [h1, h2]
  have e13 : dist center (h5Config 1) ^ 2 = dist center (h5Config 3) ^ 2 := by rw [h1, h3]
  have e14 : dist center (h5Config 1) ^ 2 = dist center (h5Config 4) ^ 2 := by rw [h1, h4]
  simp only [h5Config, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at e12 e13 e14
  nlinarith [e12, e13, e14, hs2]

set_option maxHeartbeats 1600000 in
/-- **No four of the five points are concyclic.** Every 4-subset is one of the five
quadruples, and for each no centre is equidistant from its members
(`h5_not_equidistant_*`), so no common circle exists. -/
theorem noFourConcyclic_h5Config : NoFourConcyclic h5Config := by
  intro a b c d hcard
  rintro ⟨center, r, ha, hb, hc, hd⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd hcard (by decide)
    | exact h5_not_equidistant_0123 center r (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact h5_not_equidistant_0124 center r (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact h5_not_equidistant_0134 center r (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact h5_not_equidistant_0234 center r (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact h5_not_equidistant_1234 center r (by assumption) (by assumption) (by assumption)
        (by assumption)

/-- **`h5Config` is in general position.** -/
theorem inGeneralPosition_h5Config : InGeneralPosition h5Config :=
  ⟨h5Config_injective, noThreeCollinear_h5Config, noFourConcyclic_h5Config⟩

/-- **`h5Config` realizes at most three distinct distances.** Every positive pairwise
distance lies in the three-element set `{1, √(2+√3), 1+√3}` (`h5Config_dist_mem`), so the
distinct-distance count is at most `3`. -/
theorem numDistinctDistances_h5Config_le :
    numDistinctDistances h5Config ≤ 3 := by
  unfold numDistinctDistances
  have hsub :
      ((univ.product univ).image
          (fun p : Fin 5 × Fin 5 =>
            dist (h5Config p.1) (h5Config p.2))).filter (· > 0)
        ⊆ ({1, Real.sqrt (2 + Real.sqrt 3), 1 + Real.sqrt 3} : Finset ℝ) := by
    intro d hd
    rw [mem_filter, mem_image] at hd
    obtain ⟨⟨p, -, hpd⟩, hpos⟩ := hd
    have hne : p.1 ≠ p.2 := by
      intro he
      rw [he, dist_self] at hpd
      rw [← hpd] at hpos
      exact lt_irrefl 0 hpos
    rw [← hpd]
    exact h5Config_dist_mem hne
  calc (((univ.product univ).image
          (fun p : Fin 5 × Fin 5 =>
            dist (h5Config p.1) (h5Config p.2))).filter (· > 0)).card
      ≤ ({1, Real.sqrt (2 + Real.sqrt 3), 1 + Real.sqrt 3} : Finset ℝ).card := card_le_card hsub
    _ ≤ 3 := by
        refine (Finset.card_insert_le _ _).trans ?_
        have h2 : ({Real.sqrt (2 + Real.sqrt 3), 1 + Real.sqrt 3} : Finset ℝ).card ≤ 2 := by
          refine (Finset.card_insert_le _ _).trans ?_
          simp
        omega

/-- **`h 5 ≤ 3`, an exact upper bound.** The three-distance witness `h5Config` is in general
position and realizes at most three distinct distances, so it bounds the minimum:
`h 5 ≤ numDistinctDistances ≤ 3`. -/
theorem h_five_le_three : h 5 ≤ 3 :=
  le_trans (h_le_of_inGeneralPosition inGeneralPosition_h5Config)
    numDistinctDistances_h5Config_le

/-- **`h 5 ≥ 2`.** From `h 4 = 2` (`h_four_ge_two`) and monotonicity (`h_mono`, `4 ≤ 5`). -/
theorem h_five_ge_two : 2 ≤ h 5 :=
  le_trans h_four_ge_two (h_mono (by norm_num))

/-- **`2 ≤ h 5 ≤ 3`.** The three-distance witness gives the upper bound; monotonicity from
`h 4 = 2` gives the lower bound.  Pinning `h 5 = 3` additionally requires `h 5 ≥ 3` — no
general-position five-set has only two distinct distances — which reduces to the
classification of planar 2-distance sets (the regular pentagon, which is concyclic) and is
left as the next step. -/
theorem h_five_bounds : 2 ≤ h 5 ∧ h 5 ≤ 3 :=
  ⟨h_five_ge_two, h_five_le_three⟩

end Erdos98WIP01
