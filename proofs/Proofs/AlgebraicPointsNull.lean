import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable
import Proofs.AlgebraicRealsNull

/-!
# Algebraic Points in ℝⁿ and ℂⁿ are Negligible: Almost Every Point is Coordinatewise Transcendental

## Open Question (algebraic-numbers-countable-oq-07-oq-03)

The parent entry `algebraic-numbers-countable-oq-07` proves the one-dimensional
measure pillar of the small/co-small trichotomy:

> `volume {x : ℝ | IsAlgebraic ℚ x} = 0` — almost every *real* is transcendental,

and its complex companion `volume {z : ℂ | IsAlgebraic ℚ z} = 0`. Its third
open question asks for the **n-dimensional generalization**:

> "Generalize to ℝⁿ and ℂⁿ: the set of points with at least one algebraic
>  coordinate is null in ℝⁿ, and the algebraic points (all coordinates
>  algebraic) are countable hence null. State and prove the n-dimensional
>  version, where 'almost every point has all coordinates transcendental'."

This entry answers it. Working in the finite-product measure space `Fin n → ℝ`
(equivalently ℝⁿ with the product Lebesgue measure) we prove two independent
smallness statements and reconcile them:

* **The "at least one algebraic coordinate" set is Lebesgue-null.**
  This is the *strong* statement: it is null for **every** `n` (including the
  degenerate `n = 0`, where the set is empty), and the null set here is
  *uncountable* — e.g. in ℝ² the line `{(a, y) : a algebraic}` has the
  cardinality of the continuum yet planar measure zero. The mechanism is
  Fubini/Tonelli: a coordinate cylinder `{x | xᵢ ∈ A}` is the box
  `A × ℝ × ⋯ × ℝ`, whose product measure `volume A · ∞ · ⋯` vanishes because
  the offending factor `volume A = 0` (and `0 · ∞ = 0` in `ℝ≥0∞`).

* **The "all coordinates algebraic" set is countable, hence null.**
  This is the *cardinality* statement: `(algebraic reals)ⁿ` is a finite product
  of countable sets, so it is countable; for `n ≥ 1` it sits inside the
  at-least-one set and is therefore also null. (For `n = 0` the single point
  of ℝ⁰ is "all-algebraic" vacuously and has measure `1`, so the null claim
  genuinely needs `n ≥ 1` — a boundary the one-dimensional parent never sees.)

The two facts are not the same: the null set of the first is far larger
(continuum-sized) than the countable set of the second, illustrating that
"measure zero" is strictly weaker than "countable" once `n ≥ 2`.

Dually, **almost every point of ℝⁿ (and of ℂⁿ) has all coordinates
transcendental**: the complement of the at-least-one-algebraic set is conull.
Everything is proved verbatim for ℂⁿ as well.

## Main results

* `coord_preimage_volume_zero`   : a coordinate cylinder over a null factor is null
* `atLeastOneAlgebraicReal_null` : `volume {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)} = 0`
* `allAlgebraicReal_countable`   : the all-algebraic points of ℝⁿ are countable
* `allAlgebraicReal_null`        : for `n ≥ 1` the all-algebraic points are null
* `ae_all_transcendental`        : a.e. point of ℝⁿ is coordinatewise transcendental
* `atLeastOneAlgebraicComplex_null`, `allAlgebraicComplex_countable`,
  `allAlgebraicComplex_null`, `ae_all_transcendental_complex` : the ℂⁿ analogues

0 sorries, 0 axioms (no `native_decide`).
-/

open MeasureTheory Set

namespace AlgebraicPointsNull

-- ============================================================================
-- § 1. A coordinate cylinder over a null factor is null (Fubini / Tonelli)
-- ============================================================================

/-- **A coordinate cylinder over a null factor has product measure zero.**

If `A` is `volume`-null in the factor space `α`, then the cylinder
`{x : Fin n → α | x i ∈ A}` (i.e. the box `A` in coordinate `i`, `univ`
elsewhere) is null for the product Lebesgue measure. The box factors as
`∏ j, volume (tⱼ)` via `volume_pi_pi`, and the `i`-th factor is `volume A = 0`,
so the whole product vanishes (`0 · ∞ = 0` in `ℝ≥0∞`). -/
theorem coord_preimage_volume_zero
    {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    {n : ℕ} {A : Set α} (hA : volume A = 0) (i : Fin n) :
    volume {x : Fin n → α | x i ∈ A} = 0 := by
  have hset : {x : Fin n → α | x i ∈ A}
      = Set.univ.pi (Function.update (fun _ => (Set.univ : Set α)) i A) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · intro hxi j
      rcases eq_or_ne j i with rfl | hj
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hj]; exact Set.mem_univ _
    · intro h
      have := h i
      rwa [Function.update_self] at this
  rw [hset, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by rw [Function.update_self]; exact hA)

-- ============================================================================
-- § 2. ℝⁿ: at least one algebraic coordinate ⇒ null
-- ============================================================================

/-- **The points of ℝⁿ with at least one algebraic coordinate are Lebesgue-null.**

The set is the finite union over coordinates `i` of the cylinders
`{x | IsAlgebraic ℚ (x i)}`, each null by `coord_preimage_volume_zero` applied
to the parent result `algebraic_reals_null`. A finite (indeed countable) union
of null sets is null. Holds for every `n`, including `n = 0` (empty union). -/
theorem atLeastOneAlgebraicReal_null {n : ℕ} :
    volume {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)} = 0 := by
  have hunion : {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)}
      = ⋃ i, {x : Fin n → ℝ | IsAlgebraic ℚ (x i)} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hunion]
  refine measure_iUnion_null (fun i => ?_)
  exact coord_preimage_volume_zero
    (A := {r : ℝ | IsAlgebraic ℚ r}) AlgebraicRealsNull.algebraic_reals_null i

-- ============================================================================
-- § 3. ℝⁿ: all coordinates algebraic ⇒ countable ⇒ (for n ≥ 1) null
-- ============================================================================

/-- **The points of ℝⁿ with all coordinates algebraic are countable.**

They form `(algebraic reals)ⁿ`, a finite product of the countable set of
algebraic reals; `countable_pi` (finite index, countable factors) gives
countability. This holds for every `n`. -/
theorem allAlgebraicReal_countable {n : ℕ} :
    {x : Fin n → ℝ | ∀ i, IsAlgebraic ℚ (x i)}.Countable :=
  countable_pi (fun _ => AlgebraicNumbersCountable.algebraic_reals_countable)

/-- **For `n ≥ 1`, the all-algebraic points of ℝⁿ are Lebesgue-null.**

Being countable they are null already, but we get it for free by monotonicity:
when `n ≥ 1` the index set `Fin n` is nonempty, so "all coordinates algebraic"
implies "at least one algebraic coordinate", and the latter set is null by
`atLeastOneAlgebraicReal_null`. (For `n = 0` the claim is false — ℝ⁰ is a single
point of measure `1`, all of whose coordinates are vacuously algebraic.) -/
theorem allAlgebraicReal_null {n : ℕ} (hn : 0 < n) :
    volume {x : Fin n → ℝ | ∀ i, IsAlgebraic ℚ (x i)} = 0 := by
  refine measure_mono_null ?_ atLeastOneAlgebraicReal_null
  intro x hx
  exact ⟨⟨0, hn⟩, hx ⟨0, hn⟩⟩

/-- **Almost every point of ℝⁿ has all coordinates transcendental.**

The set of coordinatewise-transcendental points is exactly the complement of
the at-least-one-algebraic set, which is null. Holds for every `n`. -/
theorem ae_all_transcendental {n : ℕ} :
    ∀ᵐ x : Fin n → ℝ ∂volume, ∀ i, Transcendental ℚ (x i) := by
  have hset : {x : Fin n → ℝ | ∀ i, Transcendental ℚ (x i)}
      = {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, Transcendental]
  rw [Filter.eventually_iff, hset]
  exact compl_mem_ae_iff.mpr atLeastOneAlgebraicReal_null

-- ============================================================================
-- § 4. ℂⁿ: the same statements for the complex algebraic numbers
-- ============================================================================

/-- **The points of ℂⁿ with at least one algebraic coordinate are null.**

Identical argument to `atLeastOneAlgebraicReal_null`, using the parent complex
result `algebraic_complex_null` for the null factor. -/
theorem atLeastOneAlgebraicComplex_null {n : ℕ} :
    volume {z : Fin n → ℂ | ∃ i, IsAlgebraic ℚ (z i)} = 0 := by
  have hunion : {z : Fin n → ℂ | ∃ i, IsAlgebraic ℚ (z i)}
      = ⋃ i, {z : Fin n → ℂ | IsAlgebraic ℚ (z i)} := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hunion]
  refine measure_iUnion_null (fun i => ?_)
  exact coord_preimage_volume_zero
    (A := {w : ℂ | IsAlgebraic ℚ w}) AlgebraicRealsNull.algebraic_complex_null i

/-- **The points of ℂⁿ with all coordinates algebraic are countable.** -/
theorem allAlgebraicComplex_countable {n : ℕ} :
    {z : Fin n → ℂ | ∀ i, IsAlgebraic ℚ (z i)}.Countable :=
  countable_pi (fun _ => AlgebraicNumbersCountable.algebraic_complex_countable)

/-- **For `n ≥ 1`, the all-algebraic points of ℂⁿ are null.** -/
theorem allAlgebraicComplex_null {n : ℕ} (hn : 0 < n) :
    volume {z : Fin n → ℂ | ∀ i, IsAlgebraic ℚ (z i)} = 0 := by
  refine measure_mono_null ?_ atLeastOneAlgebraicComplex_null
  intro z hz
  exact ⟨⟨0, hn⟩, hz ⟨0, hn⟩⟩

/-- **Almost every point of ℂⁿ has all coordinates transcendental.** -/
theorem ae_all_transcendental_complex {n : ℕ} :
    ∀ᵐ z : Fin n → ℂ ∂volume, ∀ i, Transcendental ℚ (z i) := by
  have hset : {z : Fin n → ℂ | ∀ i, Transcendental ℚ (z i)}
      = {z : Fin n → ℂ | ∃ i, IsAlgebraic ℚ (z i)}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, Transcendental]
  rw [Filter.eventually_iff, hset]
  exact compl_mem_ae_iff.mpr atLeastOneAlgebraicComplex_null

-- ============================================================================
-- § 5. The at-least-one-algebraic set is uncountable once `n ≥ 2`
-- ============================================================================

/-!
The null set of `atLeastOneAlgebraicReal_null` is *far larger* than the countable
all-algebraic set of `allAlgebraicReal_countable`: for `n ≥ 2` it is already
**uncountable**, of the cardinality of the continuum. This is the precise sense in
which "Lebesgue-null" is strictly weaker than "countable" once `n ≥ 2` — a
phenomenon the one-dimensional parent (`algebraic-numbers-countable-oq-07`) never
sees, since on the line the algebraic reals are *both* null and countable.

The witness is a copy of `ℝ` inside the set: fix coordinate `0` to the algebraic
value `0` and let coordinate `1` range over all reals. Every such point has an
algebraic coordinate (namely coordinate `0`), and the map `t ↦ (point with `t` in
slot `1`)` is injective, so the set has at least the cardinality of `ℝ = 𝔠 > ℵ₀`.
-/

/-- **For `n ≥ 2`, the points of `ℝⁿ` with at least one algebraic coordinate are
uncountable.**  Fixing coordinate `0` at the algebraic value `0` and letting
coordinate `1` range over `ℝ` embeds `ℝ` into the set, so its cardinality is at
least `𝔠 > ℵ₀`.  Together with `atLeastOneAlgebraicReal_null` this shows a
*continuum-sized* set can be Lebesgue-null; contrast `allAlgebraicReal_countable`. -/
theorem atLeastOneAlgebraicReal_uncountable {n : ℕ} (hn : 2 ≤ n) :
    ¬ {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)}.Countable := by
  intro hc
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by decide
  -- The point with `t` in slot `1` and `0` elsewhere lies in the set: its
  -- slot-`0` coordinate is `0`, which is algebraic.
  have hmem : ∀ t : ℝ,
      Function.update (fun _ : Fin n => (0 : ℝ)) ⟨1, h1⟩ t
        ∈ {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)} := by
    intro t
    refine ⟨⟨0, h0⟩, ?_⟩
    rw [Function.update_of_ne hne]
    exact isAlgebraic_zero
  -- This one-parameter family is an injection `ℝ ↪ (the set)`.
  have key : Function.Injective
      (fun t : ℝ => (⟨Function.update (fun _ : Fin n => (0 : ℝ)) ⟨1, h1⟩ t, hmem t⟩ :
        {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)})) := by
    intro s t hst
    have h := congrFun (congrArg Subtype.val hst) ⟨1, h1⟩
    simpa [Function.update_self] using h
  -- `𝔠 = #ℝ ≤ #(set) ≤ ℵ₀`, contradicting `ℵ₀ < 𝔠`.
  have hcard := Cardinal.mk_le_of_injective key
  rw [Cardinal.mk_real] at hcard
  exact absurd (hcard.trans hc.le_aleph0) (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **For `n ≥ 2`, the points of `ℂⁿ` with at least one algebraic coordinate are
uncountable.**  The complex analogue of `atLeastOneAlgebraicReal_uncountable`;
the same real one-parameter family (coordinate `1` ranging over the reals inside
`ℂ`) already embeds `ℝ`, so the set has cardinality at least `𝔠`. -/
theorem atLeastOneAlgebraicComplex_uncountable {n : ℕ} (hn : 2 ≤ n) :
    ¬ {z : Fin n → ℂ | ∃ i, IsAlgebraic ℚ (z i)}.Countable := by
  intro hc
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by decide
  have hmem : ∀ t : ℝ,
      Function.update (fun _ : Fin n => (0 : ℂ)) ⟨1, h1⟩ (t : ℂ)
        ∈ {z : Fin n → ℂ | ∃ i, IsAlgebraic ℚ (z i)} := by
    intro t
    refine ⟨⟨0, h0⟩, ?_⟩
    rw [Function.update_of_ne hne]
    exact isAlgebraic_zero
  have key : Function.Injective
      (fun t : ℝ => (⟨Function.update (fun _ : Fin n => (0 : ℂ)) ⟨1, h1⟩ (t : ℂ), hmem t⟩ :
        {z : Fin n → ℂ | ∃ i, IsAlgebraic ℚ (z i)})) := by
    intro s t hst
    have h := congrFun (congrArg Subtype.val hst) ⟨1, h1⟩
    simpa [Function.update_self] using h
  have hcard := Cardinal.mk_le_of_injective key
  rw [Cardinal.mk_real] at hcard
  exact absurd (hcard.trans hc.le_aleph0) (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **Measure-zero is strictly weaker than countable once `n ≥ 2`.**  Both sets
below are Lebesgue-null (`atLeastOneAlgebraicReal_null`, and
`allAlgebraicReal_null` for `n ≥ 1`), yet the "at least one algebraic coordinate"
set is *uncountable* while the "all coordinates algebraic" set is *countable*.
This crisply separates the two smallness notions that coincide in dimension one. -/
theorem atLeastOne_uncountable_allAlgebraic_countable {n : ℕ} (hn : 2 ≤ n) :
    ¬ {x : Fin n → ℝ | ∃ i, IsAlgebraic ℚ (x i)}.Countable
      ∧ {x : Fin n → ℝ | ∀ i, IsAlgebraic ℚ (x i)}.Countable :=
  ⟨atLeastOneAlgebraicReal_uncountable hn, allAlgebraicReal_countable⟩

end AlgebraicPointsNull
