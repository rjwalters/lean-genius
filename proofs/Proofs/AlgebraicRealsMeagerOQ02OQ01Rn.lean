import Mathlib.NumberTheory.Transcendental.Liouville.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases

/-
  The symmetric Oxtoby decomposition transfers to ℝⁿ
  (algebraic-reals-meager — OQ-02 → OQ-01, ℝⁿ-transfer follow-up)

  The sibling files establish, on the line `ℝ`, the **symmetric Oxtoby
  decomposition**

      ℝ  =  L  ⊔  Lᶜ
            └ comeagre, null, dense       (topologically large, measure-small)
                 └ meagre, conull, dense  (topologically small, measure-large)

  with `L = {x | Liouville x}`, and sharpen it by proving both pieces dense and
  the whole partition `Aff(ℚ)`-equivariant. The one remaining follow-up recorded
  in the problem knowledge asks whether the two-piece phenomenon **transfers to
  `ℝⁿ`**: is there a meagre, dense, *conull* subset of `ℝⁿ`?

  This file answers yes, with the natural coordinatewise construction on
  `ℝⁿ = Fin n → ℝ` (`n ≥ 1`):

      SomeLiouville  =  { x | ∃ i, Liouville (xᵢ) }      (analog of L)
      NoLiouville    =  { x | ∀ i, ¬ Liouville (xᵢ) }    (analog of Lᶜ)

  and shows

      • `NoLiouville`   is **meagre, dense, and conull**   (the informative half);
      • `SomeLiouville` is **comeagre (residual), null, and dense**.

  So the measure/category anomaly is not special to the line: `ℝⁿ` also splits
  into two disjoint dense sets, one meagre-and-conull, the other comeagre-and-null.

  ## The mechanism

  Everything reduces coordinatewise through the projections
  `eval i : (Fin n → ℝ) → ℝ`, which are simultaneously

      • continuous and **open** (`continuous_apply`, `isOpenMap_eval`), and
      • **quasi–measure-preserving** for the product Lebesgue measure
        (`quasiMeasurePreserving_eval`, with `volume = Measure.pi`).

  Openness + continuity push Mathlib's residual filter forward
  (`tendsto_residual_of_isOpenMap`), so each cylinder `{x | Liouville (xᵢ)}` is
  residual because `L` is (`eventually_residual_liouville`). Quasi–measure
  preservation pulls null sets back (`QuasiMeasurePreserving.preimage_null`), so
  each cylinder is *also* null because `L` is (`volume_setOf_liouville`).

  Then:
    • `SomeLiouville = ⋃ᵢ {x | Liouville (xᵢ)}` is null (finite union of null
      sets) and residual (superset of one residual cylinder, `n ≥ 1`);
    • `NoLiouville = SomeLiouvilleᶜ` is therefore meagre and conull;
    • density of `NoLiouville` is the sharp half — a *conull* set is dense
      because `volume` gives every nonempty open set positive mass
      (`Measure.interior_eq_empty_of_null`); density of `SomeLiouville` is the
      routine comeagre ⇒ dense (`dense_of_mem_residual`, `ℝⁿ` Baire).

  ## Honesty / novelty

  No new mathematics: this is the coordinatewise lift of the line case through
  standard Mathlib product-measure and product-topology transfer lemmas. The
  value is the explicit, machine-checked statement that the Oxtoby
  measure/category pathology genuinely persists in every finite dimension, which
  the sibling files leave open. Presented as a modest structural follow-up.

  No new axioms (standard Mathlib triple inherited).

  References:
  - Oxtoby, J.C. (1980). "Measure and Category", Springer GTM 2.
  - Mathlib: `quasiMeasurePreserving_eval`, `volume_pi`,
             `tendsto_residual_of_isOpenMap`, `isOpenMap_eval`,
             `dense_of_mem_residual`, `Measure.interior_eq_empty_of_null`,
             `eventually_residual_liouville`, `volume_setOf_liouville`.

  Tags: liouville-numbers, measure-theory, baire-category, product-measure,
        higher-dimensional, oxtoby-duality, meagre, conull, dense
-/

set_option maxHeartbeats 400000

namespace AlgebraicRealsMeagerOQ02OQ01Rn

open MeasureTheory Filter Set

variable (n : ℕ)

-- ============================================================================
-- Part 0: the abstract engine — a conull set is dense
-- ============================================================================

/-- **A conull set is dense** (in a space whose measure gives every nonempty
    open set positive mass). If `μ sᶜ = 0` then `sᶜ` has empty interior, so `s`
    is dense. This is the measure-side counterpart of `dense_of_mem_residual`
    and the engine that makes the *meagre* half of the decomposition dense.
    (Mirrors the sibling `AlgebraicRealsMeagerOQ02OQ01Dense.dense_of_conull`.) -/
theorem dense_of_conull {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {s : Set X} (hs : μ sᶜ = 0) :
    Dense s := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hs

-- ============================================================================
-- Part I: the two coordinatewise sets on `ℝⁿ = Fin n → ℝ`
-- ============================================================================

/-- **`SomeLiouville`** — the points of `ℝⁿ` with at least one Liouville
    coordinate. The `ℝⁿ` analog of the Liouville set `L`. -/
def SomeLiouville : Set (Fin n → ℝ) := {x | ∃ i, Liouville (x i)}

/-- **`NoLiouville`** — the points of `ℝⁿ` all of whose coordinates are
    non-Liouville. The `ℝⁿ` analog of `Lᶜ`; it is the complement of
    `SomeLiouville`. -/
def NoLiouville : Set (Fin n → ℝ) := {x | ∀ i, ¬ Liouville (x i)}

/-- `NoLiouville` is exactly the complement of `SomeLiouville`. -/
theorem noLiouville_eq_compl : NoLiouville n = (SomeLiouville n)ᶜ := by
  ext x
  simp only [NoLiouville, SomeLiouville, mem_setOf_eq, mem_compl_iff, not_exists]

/-- `SomeLiouville` is the (finite) union over coordinates of the "coordinate `i`
    is Liouville" cylinders. -/
theorem someLiouville_eq_iUnion :
    SomeLiouville n = ⋃ i, {x : Fin n → ℝ | Liouville (x i)} := by
  ext x
  simp only [SomeLiouville, mem_setOf_eq, mem_iUnion]

-- ============================================================================
-- Part II: a single coordinate cylinder is null and residual
-- ============================================================================

/-- **Each coordinate cylinder is null.** `{x | Liouville (xᵢ)}` is the preimage
    of the null set `L` under the quasi–measure-preserving projection `eval i`,
    so it has product-Lebesgue measure zero. -/
theorem cylinder_liouville_null (i : Fin n) :
    volume {x : Fin n → ℝ | Liouville (x i)} = 0 := by
  have h : {x : Fin n → ℝ | Liouville (x i)}
      = Function.eval i ⁻¹' {y : ℝ | Liouville y} := rfl
  rw [h, volume_pi]
  exact (quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure ℝ)) i).preimage_null
    volume_setOf_liouville

/-- **Each coordinate cylinder is residual.** `{x | Liouville (xᵢ)}` is the
    preimage of the residual set `L` under the continuous open projection
    `eval i`, hence residual by `tendsto_residual_of_isOpenMap`. -/
theorem cylinder_liouville_residual (i : Fin n) :
    {x : Fin n → ℝ | Liouville (x i)} ∈ residual (Fin n → ℝ) := by
  have h : {x : Fin n → ℝ | Liouville (x i)}
      = Function.eval i ⁻¹' {y : ℝ | Liouville y} := rfl
  rw [h]
  exact tendsto_residual_of_isOpenMap (continuous_apply i) (isOpenMap_eval i)
    eventually_residual_liouville

-- ============================================================================
-- Part III: `SomeLiouville` is null and residual
-- ============================================================================

/-- **`SomeLiouville` is null.** A finite union of null coordinate cylinders. -/
theorem someLiouville_null : volume (SomeLiouville n) = 0 := by
  rw [someLiouville_eq_iUnion]
  exact measure_iUnion_null fun i => cylinder_liouville_null n i

/-- **`SomeLiouville` is residual (comeagre)** for `n ≥ 1`. It contains a single
    residual coordinate cylinder, and residual sets are upward closed. -/
theorem someLiouville_residual (hn : 0 < n) :
    SomeLiouville n ∈ residual (Fin n → ℝ) := by
  rw [someLiouville_eq_iUnion]
  exact mem_of_superset (cylinder_liouville_residual n ⟨0, hn⟩)
    (subset_iUnion (fun i => {x : Fin n → ℝ | Liouville (x i)}) ⟨0, hn⟩)

/-- **`SomeLiouville` is dense** for `n ≥ 1` (comeagre in a Baire space). -/
theorem someLiouville_dense (hn : 0 < n) : Dense (SomeLiouville n) :=
  dense_of_mem_residual (someLiouville_residual n hn)

-- ============================================================================
-- Part IV: `NoLiouville` is meagre, conull, and dense
-- ============================================================================

/-- **`NoLiouville` is meagre** for `n ≥ 1`: its complement `SomeLiouville` is
    residual. -/
theorem noLiouville_meagre (hn : 0 < n) : IsMeagre (NoLiouville n) := by
  rw [noLiouville_eq_compl, IsMeagre, compl_compl]
  exact someLiouville_residual n hn

/-- **`NoLiouville` is conull**: its complement `SomeLiouville` is null. -/
theorem noLiouville_conull : volume (NoLiouville n)ᶜ = 0 := by
  rw [noLiouville_eq_compl, compl_compl]
  exact someLiouville_null n

/-- **`NoLiouville` is dense — despite being meagre.** It is conull, and a conull
    set in `ℝⁿ` is dense. This is the sharp topological content: the *small*
    (meagre) half of the higher-dimensional Oxtoby decomposition still meets
    every nonempty open box. -/
theorem noLiouville_dense : Dense (NoLiouville n) :=
  dense_of_conull (noLiouville_conull n)

-- ============================================================================
-- Part V: the transferred symmetric Oxtoby decomposition of `ℝⁿ`
-- ============================================================================

/-- **The symmetric Oxtoby decomposition transfers to `ℝⁿ`** (`n ≥ 1`). The
    product Liouville phenomenon splits `ℝⁿ = Fin n → ℝ` into two disjoint dense
    pieces:

    * `NoLiouville`   — **meagre, dense, and conull** (topologically small,
      measure-large);
    * `SomeLiouville` — **comeagre (residual), null, and dense** (topologically
      large, measure-small).

    In particular there is a meagre, dense, conull subset of `ℝⁿ` in every finite
    dimension `n ≥ 1`, answering the `ℝⁿ`-transfer follow-up. -/
theorem oxtoby_transfer_Rn (hn : 0 < n) :
    IsMeagre (NoLiouville n) ∧ Dense (NoLiouville n) ∧ volume (NoLiouville n)ᶜ = 0
      ∧ SomeLiouville n ∈ residual (Fin n → ℝ)
      ∧ volume (SomeLiouville n) = 0 ∧ Dense (SomeLiouville n) :=
  ⟨noLiouville_meagre n hn, noLiouville_dense n, noLiouville_conull n,
   someLiouville_residual n hn, someLiouville_null n, someLiouville_dense n hn⟩

#check @cylinder_liouville_null
#check @cylinder_liouville_residual
#check @someLiouville_null
#check @someLiouville_residual
#check @noLiouville_meagre
#check @noLiouville_conull
#check @noLiouville_dense
#check @oxtoby_transfer_Rn

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `dense_of_conull` | conull ⇒ dense (abstract engine) | Proved |
  | `noLiouville_eq_compl` | `NoLiouville = SomeLiouvilleᶜ` | Proved |
  | `someLiouville_eq_iUnion` | `SomeLiouville = ⋃ᵢ` cylinderᵢ | Proved |
  | `cylinder_liouville_null` | `volume {x | Liouville xᵢ} = 0` | Proved |
  | `cylinder_liouville_residual` | cylinderᵢ residual | Proved |
  | `someLiouville_null` | `volume SomeLiouville = 0` | Proved |
  | `someLiouville_residual` | `SomeLiouville` residual (n≥1) | Proved |
  | `someLiouville_dense` | `SomeLiouville` dense (n≥1) | Proved |
  | `noLiouville_meagre` | `NoLiouville` meagre (n≥1) | Proved |
  | `noLiouville_conull` | `volume NoLiouvilleᶜ = 0` | Proved |
  | `noLiouville_dense` | `NoLiouville` dense | Proved |
  | `oxtoby_transfer_Rn` | full ℝⁿ two-piece decomposition | Proved |

  **Sorries**: 0
  **Axioms**: 0 declared (Mathlib triple inherited)
-/

end AlgebraicRealsMeagerOQ02OQ01Rn
