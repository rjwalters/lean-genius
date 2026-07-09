import Mathlib

/-
  The symmetric Oxtoby decomposition transfers to `ℝⁿ`
  (algebraic-reals-meager — OQ-02 → OQ-01, structural follow-up)

  The sibling files record the **symmetric Oxtoby decomposition** of the real
  line

      ℝ  =  L  ⊔  Lᶜ
            └ comeagre & null      (topologically large, measure-small)
                 └ meagre & conull (topologically small, measure-large)

  with `L = {x | Liouville x}`, and sharpen it by showing both pieces are
  *dense* (`…Dense.lean`) and `Aff(ℚ)`-equivariant (`…Equivariant.lean`). The
  one follow-up left open there was whether the whole phenomenon transfers to
  finite-dimensional real space `ℝⁿ = (ι → ℝ)`. This file settles it.

  ## The product Liouville set

  Define the **product Liouville set**

      Lⁿ  :=  {x : ι → ℝ | ∀ i, Liouville (xᵢ)}  =  ⋂ i, (eval i)⁻¹' L,

  the points *all* of whose coordinates are Liouville. It is the honest
  `n`-dimensional analogue of `L`, and it inherits *both* Oxtoby anomalies:

  * **comeagre** — each coordinate slot `(eval i)⁻¹' L` is residual, because
    `eval i` is a continuous *open* surjection and the preimage of a residual
    set under such a map is residual (`tendsto_residual_of_isOpenMap`); a finite
    intersection of residual sets is residual (`Filter.iInter_mem`).
  * **null** — `Lⁿ ⊆ (eval i)⁻¹' L` for any single coordinate `i`, and that
    coordinate cylinder is Lebesgue-null in the product measure
    (`Measure.pi_eval_preimage_null`, since `L` is null on the line).

  Complementation gives the dual piece `(Lⁿ)ᶜ = {x | ∃ i, ¬ Liouville xᵢ}`,
  which is therefore **meagre** and **conull**. As on the line, *both* pieces
  are **dense**: `Lⁿ` because it is comeagre (`dense_of_mem_residual`), and
  `(Lⁿ)ᶜ` — the meagre half — because it is conull and the product volume gives
  every nonempty open set positive mass (`dense_of_conull`, reused from the
  sibling; the instance `pi.isOpenPosMeasure` supplies the hypothesis).

  So the entire measure/category pathology of the line survives verbatim into
  every finite dimension:

      ℝⁿ  =  Lⁿ  ⊔  (Lⁿ)ᶜ,     both dense,
             └ comeagre & null
                  └ meagre & conull.

  ## Honesty / novelty

  No new mathematics: every step is a one- or two-line appeal to existing
  Mathlib product-space plumbing (`isOpenMap_eval`, `continuous_apply`,
  `tendsto_residual_of_isOpenMap`, `Measure.pi_eval_preimage_null`,
  `pi.isOpenPosMeasure`) composed with the line-level facts already recorded in
  the sibling files. The value is the explicit, machine-checked statement that
  the Oxtoby decomposition is *not* a one-dimensional accident — it is a genuine
  finite-dimensional partition of `ℝⁿ` into two dense sets, one comeagre-and-null
  and one meagre-and-conull. Presented as a modest structural generalization.

  No new axioms (standard Mathlib triple inherited).

  References:
  - Oxtoby, J.C. (1980). "Measure and Category", Springer GTM 2.
  - Mathlib: NumberTheory.Transcendental.Liouville.{Residual,Measure},
             Topology.Baire.BaireMeasurable (`tendsto_residual_of_isOpenMap`),
             MeasureTheory.Constructions.Pi (`Measure.pi_eval_preimage_null`,
             `pi.isOpenPosMeasure`).

  Tags: measure-theory, baire-category, liouville-numbers, meagre, residual,
        product-measure, oxtoby-duality, dense, higher-dimensional
-/

set_option maxHeartbeats 400000

namespace AlgebraicRealsMeagerOQ02OQ01Product

open MeasureTheory Filter Set Function

-- ============================================================================
-- Part I: line-level facts and the abstract conull ⟹ dense engine (recalled)
-- ============================================================================

/-- The Liouville numbers are comeagre (residual) in `ℝ`. -/
theorem liouville_residual : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-- The Liouville numbers are Lebesgue-null on the line. -/
theorem liouville_null : volume {x : ℝ | Liouville x} = 0 :=
  volume_setOf_liouville

/-- **A conull set is dense** (in a space whose measure gives every nonempty
    open set positive mass). Mirror of `dense_of_mem_residual`; the engine that
    makes the *meagre* half of the Oxtoby decomposition dense. Restated from the
    sibling `…Dense.lean` so this file is self-contained. -/
theorem dense_of_conull {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {s : Set X} (hs : μ sᶜ = 0) :
    Dense s := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hs

-- ============================================================================
-- Part II: the product Liouville set `Lⁿ` in `ℝⁿ = (ι → ℝ)`
-- ============================================================================

variable {ι : Type*} [Fintype ι]

/-- The **product Liouville set**: points of `ℝⁿ` *all* of whose coordinates are
    Liouville numbers, written as the intersection of the coordinate cylinders
    `(eval i)⁻¹' L`. -/
def productLiouville (ι : Type*) : Set (ι → ℝ) :=
  ⋂ i, eval i ⁻¹' {x : ℝ | Liouville x}

omit [Fintype ι] in
/-- Membership characterization: `x ∈ Lⁿ ↔ every coordinate of `x` is
    Liouville`. -/
theorem mem_productLiouville {x : ι → ℝ} :
    x ∈ productLiouville ι ↔ ∀ i, Liouville (x i) := by
  simp [productLiouville]

/-- **`Lⁿ` is comeagre.** Each coordinate cylinder `(eval i)⁻¹' L` is residual
    (preimage of the residual set `L` under the continuous open map `eval i`),
    and a finite intersection of residual sets is residual. -/
theorem productLiouville_residual : productLiouville ι ∈ residual (ι → ℝ) := by
  rw [productLiouville, Filter.iInter_mem]
  exact fun i =>
    tendsto_residual_of_isOpenMap (continuous_apply i) (isOpenMap_eval i) liouville_residual

/-- **`Lⁿ` is Lebesgue-null.** It sits inside a single coordinate cylinder
    `(eval i)⁻¹' L`, which is null in the product measure because `L` is null on
    the line (`Measure.pi_eval_preimage_null`). -/
theorem productLiouville_null [Nonempty ι] : volume (productLiouville ι) = 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  rw [productLiouville]
  refine measure_mono_null (iInter_subset (fun i => eval i ⁻¹' {x : ℝ | Liouville x}) i) ?_
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null (fun _ => volume) liouville_null

/-- **`Lⁿ` is dense** (it is comeagre and `ℝⁿ` is a Baire space). -/
theorem dense_productLiouville : Dense (productLiouville ι) :=
  dense_of_mem_residual productLiouville_residual

-- ============================================================================
-- Part III: the dual piece `(Lⁿ)ᶜ` — meagre, conull, yet dense
-- ============================================================================

/-- **The dual set `(Lⁿ)ᶜ = {x | ∃ i, ¬ Liouville xᵢ}` is meagre.** Its
    complement `Lⁿ` is comeagre, so it is meagre by definition of `IsMeagre`. -/
theorem productLiouville_compl_meagre : IsMeagre (productLiouville ι)ᶜ := by
  rw [IsMeagre, compl_compl]
  exact productLiouville_residual

/-- **`(Lⁿ)ᶜ` is conull (full Lebesgue measure).** Its complement `Lⁿ` is
    null. -/
theorem productLiouville_compl_conull [Nonempty ι] :
    volume ((productLiouville ι)ᶜ)ᶜ = 0 := by
  rw [compl_compl]
  exact productLiouville_null

/-- **`(Lⁿ)ᶜ` is dense — despite being meagre.** It is conull, and the product
    volume is an open-positive measure, so `dense_of_conull` applies. This is
    the sharp content: the topologically *small* half of the Oxtoby
    decomposition still meets every nonempty open box in `ℝⁿ`. -/
theorem dense_productLiouville_compl [Nonempty ι] : Dense (productLiouville ι)ᶜ :=
  dense_of_conull (μ := volume) (by rw [compl_compl]; exact productLiouville_null)

-- ============================================================================
-- Part IV: the `n`-dimensional symmetric Oxtoby decomposition
-- ============================================================================

/-- **Headline.** For every nonempty finite index set `ι`, `ℝ^ι` contains a
    set that is simultaneously **meagre**, **dense**, and of **full Lebesgue
    measure** — namely `(Lⁿ)ᶜ`. The one-dimensional Oxtoby pathology is not a
    low-dimensional accident. -/
theorem exists_meagre_dense_conull [Nonempty ι] :
    ∃ S : Set (ι → ℝ), IsMeagre S ∧ Dense S ∧ volume Sᶜ = 0 :=
  ⟨(productLiouville ι)ᶜ, productLiouville_compl_meagre, dense_productLiouville_compl,
    productLiouville_compl_conull⟩

/-- **The symmetric Oxtoby decomposition of `ℝⁿ`.** The disjoint partition
    `ℝ^ι = Lⁿ ⊔ (Lⁿ)ᶜ` has:

    * `Lⁿ` — **comeagre** (`∈ residual`) and **null**;
    * `(Lⁿ)ᶜ` — **meagre** and **conull**;

    with *both* pieces **dense**. This is the verbatim `n`-dimensional analogue
    of the line-level `real_symmetric_oxtoby_dense`. -/
theorem product_symmetric_oxtoby [Nonempty ι] :
    productLiouville ι ∪ (productLiouville ι)ᶜ = univ ∧
      Disjoint (productLiouville ι) (productLiouville ι)ᶜ ∧
      (productLiouville ι ∈ residual (ι → ℝ) ∧
        volume (productLiouville ι) = 0 ∧ Dense (productLiouville ι)) ∧
      (IsMeagre (productLiouville ι)ᶜ ∧
        volume ((productLiouville ι)ᶜ)ᶜ = 0 ∧ Dense (productLiouville ι)ᶜ) :=
  ⟨union_compl_self _, disjoint_compl_right,
    ⟨productLiouville_residual, productLiouville_null, dense_productLiouville⟩,
    ⟨productLiouville_compl_meagre, productLiouville_compl_conull,
      dense_productLiouville_compl⟩⟩

end AlgebraicRealsMeagerOQ02OQ01Product
