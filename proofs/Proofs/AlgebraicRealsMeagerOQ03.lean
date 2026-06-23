import Proofs.AlgebraicRealsMeagerOQ02

/-!
# Measure and Category are Orthogonal: a Meagre Set of Full Measure

## Open Question (algebraic-reals-meager — OQ-03)

The parent entry `algebraic-reals-meager` proves the algebraic reals are **meagre**
(topologically small) and the companion `algebraic-reals-meager-oq-02` adds the
**measure** pillar: they are Lebesgue-null, and — via the Liouville numbers — a set can
be *comeagre yet null* (`exists_residual_dense_null`). That settles one half of the
independence of the two notions of smallness: **category-large ⇏ measure-large**.

OQ-03 asks for the dual witness and the sharpest structural form:

> "Construct a meagre set of full Lebesgue measure (and a null comeagre set) to show
>  measure-smallness and category-smallness are genuinely independent on ℝ."

This entry supplies the missing dual direction and packages the whole picture as the
classical **Lebesgue–Baire orthogonality** of Oxtoby (*Measure and Category*, Thm 1.6):
the real line splits into two complementary "small" pieces — one topologically small,
the other measure-theoretically small.

    ℝ  =  A  ⊔  B          with   A meagre   and   B Lebesgue-null.

Concretely `B` is the Liouville numbers (a dense comeagre null set, from OQ-02) and
`A = Bᶜ` is its complement: a **meagre set of full Lebesgue measure**. The two ideals
of "smallness" are therefore orthogonal — neither contains the other, and together a
meagre set and a null set can cover the entire line.

## Main Results

* `meagre_conull_compl_of_residual_null` — abstract engine: a residual null set has a
  meagre complement of full measure, and the two partition the space (no measurability
  needed — only countable subadditivity of the outer measure).
* `real_meagre_null_decomposition` — **headline.** `ℝ = A ⊔ B` with `A` meagre and
  `B` null: the Oxtoby orthogonal decomposition.
* `exists_meagre_conull` — the explicitly requested object: a meagre set of full
  Lebesgue measure (`volume A = volume univ`, equivalently `volume Aᶜ = 0`).
* `meagre_not_imp_null` / `null_not_imp_meagre` — the two independence non-implications,
  dual to each other; together they show measure-smallness and category-smallness are
  logically independent.
* `oq03_resolution` — the combined statement.

The two non-implications are genuinely dual: OQ-02's `exists_residual_dense_null` gives a
*comeagre* set that is *null* (category-large but measure-small); here `meagre_not_imp_null`
gives a *meagre* set that is *conull* (category-small but measure-large).
-/

open MeasureTheory Filter Set AlgebraicRealsMeagerOQ02

namespace AlgebraicRealsMeagerOQ03

/-- Shorthand for the Liouville numbers, our separating set. -/
abbrev 𝓛 : Set ℝ := {x : ℝ | Liouville x}

/-! ## The abstract orthogonality engine -/

/-- **Measure–category orthogonality (general form).** If `S` is residual (comeagre) and
Lebesgue-null, then its complement `Sᶜ` is meagre, has full measure, and the pair
`Sᶜ, S` partitions `ℝ`. The full-measure claim uses only countable subadditivity of the
outer measure `volume`, so no measurability hypothesis on `S` is required. -/
theorem meagre_conull_compl_of_residual_null {S : Set ℝ}
    (hres : S ∈ residual ℝ) (hnull : volume S = 0) :
    IsMeagre Sᶜ ∧ volume Sᶜ = volume (univ : Set ℝ) ∧ Sᶜ ∪ S = univ := by
  refine ⟨?_, ?_, ?_⟩
  · -- `IsMeagre Sᶜ` unfolds to `Sᶜᶜ ∈ residual`, i.e. `S ∈ residual`.
    simpa [IsMeagre, compl_compl] using hres
  · -- Full measure: `univ ≤ vol Sᶜ + vol S = vol Sᶜ`, and `vol Sᶜ ≤ univ`.
    refine le_antisymm (measure_mono (subset_univ _)) ?_
    have hcov : (univ : Set ℝ) = Sᶜ ∪ S := by
      rw [Set.compl_union_self]
    calc volume (univ : Set ℝ)
        = volume (Sᶜ ∪ S) := by rw [hcov]
      _ ≤ volume Sᶜ + volume S := measure_union_le _ _
      _ = volume Sᶜ := by rw [hnull, add_zero]
  · rw [Set.compl_union_self]

/-! ## The Oxtoby decomposition and the requested witnesses -/

/-- **Lebesgue–Baire orthogonal decomposition (headline).** The real line is the disjoint
union of a meagre set and a Lebesgue-null set:

    ℝ  =  A  ⊔  B,     A meagre,    B null.

Here `B` is the Liouville numbers and `A = Bᶜ`. This is the sharpest form of the
independence of the two ideals of "smallness": together a topologically small set and a
measure-theoretically small set cover the entire line. -/
theorem real_meagre_null_decomposition :
    ∃ A B : Set ℝ, A ∪ B = univ ∧ Disjoint A B ∧ IsMeagre A ∧ volume B = 0 :=
  ⟨𝓛ᶜ, 𝓛, Set.compl_union_self _, disjoint_compl_left,
    (meagre_conull_compl_of_residual_null liouville_residual liouville_null).1,
    liouville_null⟩

/-- **A meagre set of full Lebesgue measure** — the object OQ-03 explicitly requests.
The complement of the Liouville numbers is meagre (its complement, the Liouville set, is
residual) yet has full measure (the Liouville set is null). -/
theorem exists_meagre_conull :
    ∃ A : Set ℝ, IsMeagre A ∧ volume Aᶜ = 0 ∧ volume A = volume (univ : Set ℝ) := by
  obtain ⟨hmeagre, hfull, _⟩ :=
    meagre_conull_compl_of_residual_null liouville_residual liouville_null
  exact ⟨𝓛ᶜ, hmeagre, by rw [compl_compl]; exact liouville_null, hfull⟩

/-! ## The two independence non-implications -/

/-- **Category-small ⇏ measure-small.** There is a meagre set whose Lebesgue measure is
*not* zero — in fact it has full (infinite) measure. Dual to OQ-02's
`exists_residual_dense_null`. -/
theorem meagre_not_imp_null :
    ∃ A : Set ℝ, IsMeagre A ∧ volume A ≠ 0 := by
  obtain ⟨A, hmeagre, _, hfull⟩ := exists_meagre_conull
  refine ⟨A, hmeagre, ?_⟩
  rw [hfull, Real.volume_univ]
  exact ENNReal.top_ne_zero

/-- **Measure-small ⇏ category-small.** There is a Lebesgue-null set that is *not* meagre
— the Liouville numbers, which are comeagre (residual) and hence not meagre in the Baire
space `ℝ`. This is the measure-side dual of `meagre_not_imp_null`. -/
theorem null_not_imp_meagre :
    ∃ B : Set ℝ, volume B = 0 ∧ ¬ IsMeagre B :=
  ⟨𝓛, liouville_null, not_isMeagre_of_mem_residual liouville_residual⟩

/-! ## OQ-03 resolution -/

/-- **OQ-03 resolution.** Measure-smallness and category-smallness are independent on `ℝ`,
in the sharpest (orthogonal-decomposition) form:

1. `ℝ = A ⊔ B` with `A` meagre and `B` Lebesgue-null (Oxtoby orthogonality);
2. a meagre set can have full measure (category-small ⇏ measure-small);
3. a null set can fail to be meagre (measure-small ⇏ category-small).

Statements (2) and (3) are exact duals, witnessed by the complementary pair `(𝓛ᶜ, 𝓛)`. -/
theorem oq03_resolution :
    (∃ A B : Set ℝ, A ∪ B = univ ∧ Disjoint A B ∧ IsMeagre A ∧ volume B = 0) ∧
    (∃ A : Set ℝ, IsMeagre A ∧ volume A ≠ 0) ∧
    (∃ B : Set ℝ, volume B = 0 ∧ ¬ IsMeagre B) :=
  ⟨real_meagre_null_decomposition, meagre_not_imp_null, null_not_imp_meagre⟩

#check @meagre_conull_compl_of_residual_null
#check @real_meagre_null_decomposition
#check @exists_meagre_conull
#check @meagre_not_imp_null
#check @null_not_imp_meagre
#check @oq03_resolution

end AlgebraicRealsMeagerOQ03
