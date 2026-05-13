# Session S1b OBSERVE — Aumann/Lyapunov Mathlib prerequisite audit (Approach A/B deferred from S2 PREP)

**Researcher**: researcher-4
**Date**: 2026-05-12
**Mode**: Doc-only (no `.lean` changes, no markdown edits outside this new
file, no JSON edits)
**Predecessor**: S1 OBSERVE PR #18345 (merged 2026-05-12T22:53Z) — literal
`finrank` extension vacuous; shortlisted Approaches A (Aumann), B (Lyapunov),
C (negative `ℓ²`-style counter-example).
**Sibling-in-flight**: S2 PREP PR #18397 (open) — locks **Approach C** with
`EuclideanSpace ℝ (Fin N)`, `Sᵢ = {0, eᵢ}`, theorem
`shapley_folkman_tight_excess_count`. Approaches A/B are explicitly
**deferred** there.
**Orthogonality**: this note touches only Approaches A and B; Approach C is
out of scope. No edits to `problem.md`, `state.md`, `knowledge.md`, the
gallery `meta.json`, the `lean/` subfolder, or any `.lean` file.

---

## §1. Scope and orthogonality

The S1 OBSERVE survey listed three viable infinite-dim analogs:

* **Approach A — Aumann (1965)** set-valued integral: for an atomless
  measure space `(Ω, μ)` and a measurable set-valued map `F : Ω → Set H`
  into a separable Hilbert (or Banach) space `H`, the set
  ` ∫ F dμ = { ∫ f dμ | f measurable selection of F } ` is convex.
* **Approach B — Lyapunov (1940)** vector-measure range convexity: for an
  atomless `ℝⁿ`-valued measure `μ : Σ → ℝⁿ`, the range
  ` { μ A | A ∈ Σ } ` is convex and compact in `ℝⁿ`.
* **Approach C — explicit `ℓ²`/`EuclideanSpace ℝ (Fin N)` counter-example**:
  the parent's `≤ finrank E` bound is tight on a parametric family with
  every index excess.

S2 PREP #18397 locks Approach C as the narrowest Mathlib-ready path
(~70-100 LOC Lean, 0 axioms, 0 sorries, no upstream blockers). Both A and B
require formalizing Lyapunov's theorem (a multi-session upstream task), and
A additionally requires Aumann's set-valued-integral framework on top of
Lyapunov.

**This session catalogs what Mathlib already provides for A/B, what is
missing, and the work-scope estimate so that a future S(N) session can
make an evidence-based decision to switch from C to A or B (or to keep
them deferred until Mathlib upstream catches up).**

---

## §2. Lyapunov's convexity theorem — three proofs and their Mathlib mappings

Lyapunov 1940 (English: Lindenstrauss 1966) states:

> Let `(Ω, Σ)` be a measurable space and `μ = (μ₁, …, μₙ) : Σ → ℝⁿ` a
> vector-valued measure such that each `μᵢ` is signed, finite, and
> non-atomic (atomless). Then `Range μ = { μ A | A ∈ Σ } ⊆ ℝⁿ` is convex
> and compact.

There are three textbook proofs, each with a different Mathlib import
profile.

### §2.1 Halmos 1948 (finite-σ-algebra induction)

* Approximate `Σ` by a sequence `Σₖ` of finite sub-σ-algebras whose union
  generates `Σ` up to `μ`-null sets.
* For each `Σₖ`, `Range (μ|Σₖ)` is the vertex set of a polytope in `ℝⁿ`
  with `2^{|Σₖ|}` vertices.
* Show convexity of the limit by a packing/halving argument: for `A` with
  `μ A = v` and any target `tv` with `t ∈ [0,1]`, atomlessness yields
  `B ⊆ A` with `μ B = tv` via a measurable bisection lemma.

**Mathlib status of Halmos-style ingredients:**

| Ingredient                                | Where in Mathlib                                                 | Status                |
|-------------------------------------------|------------------------------------------------------------------|-----------------------|
| Generated σ-algebra                       | `Mathlib.MeasureTheory.MeasurableSpace.Defs`                     | Present               |
| Finite sub-σ-algebras                     | `Mathlib.MeasureTheory.MeasurableSpace.{Constructions,Generators}` | Partial               |
| Atomless measure (`NoAtoms`)              | `Mathlib.MeasureTheory.Measure.Typeclasses`                       | Present               |
| Measurable bisection: `∃ B ⊆ A, μ B = ½ μ A` | None (would be `Measure.exists_subset_measure_of_noAtoms`)        | **Missing**           |
| Caratheodory extension / monotone-class   | `Mathlib.MeasureTheory.MeasurableSpace.Basic`                    | Present               |
| Range of vector measure                   | None as a named object; `VectorMeasure.Basic` has `measureOf`     | **Missing as a Set**  |
| Convex hull of measure range              | `Mathlib.Analysis.Convex.{Hull,Combination}`                      | Present               |
| Compactness of measure range              | None                                                              | **Missing**           |

The **measurable-bisection lemma** is the keystone: in Lean it would read
roughly

```lean
theorem MeasureTheory.Measure.exists_subset_half_measure
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [NoAtoms μ]
    {A : Set α} (hA : MeasurableSet A) (hμA : μ A < ⊤) :
    ∃ B ⊆ A, MeasurableSet B ∧ μ B = μ A / 2 := …
```

This is a standalone ~50-80 LOC lemma whose proof is the
"midpoint via dyadic exhaustion" argument (Halmos 1944 §41). It is
**not** present in Mathlib v4.26.0 (confirmed by GitHub code search:
`MeasureTheory.Measure.exists_subset_half_measure` and natural variants
return zero hits). It is a worthwhile **standalone** Lean target,
independent of Shapley–Folkman.

### §2.2 Lindenstrauss 1966 (Krein-Milman / extreme-points)

Replace Halmos induction with a Krein-Milman argument on the closed
convex hull of `Range μ`:

* `Range μ` is bounded (each `|μᵢ A| ≤ ‖μᵢ‖`).
* Suppose `Range μ` is not convex. Then there exists `v ∈ overline{co}(Range μ)`
  with `v ∉ Range μ`. Choose `v` extreme.
* Apply atomlessness to derive a measurable subset that strictly improves
  `v`'s position in a chosen direction, contradicting extremality.

**Mathlib status of Lindenstrauss-style ingredients:**

| Ingredient                                | Where in Mathlib                                  | Status                |
|-------------------------------------------|---------------------------------------------------|-----------------------|
| Krein-Milman (compact convex ⇒ extreme points) | `Mathlib.Analysis.Convex.KreinMilman`            | Present               |
| Extreme points / `IsExtremePoint`         | `Mathlib.Analysis.Convex.Extreme`                  | Present               |
| Closed convex hull `closure (convexHull ℝ s)` | `Mathlib.Analysis.Convex.Basic`                  | Present               |
| Compactness of bounded `Range μ` in `ℝⁿ`  | None (would be `VectorMeasure.range_compact`)     | **Missing**           |
| Strict-improvement lemma from atomlessness | None                                              | **Missing**           |

Lindenstrauss's proof is shorter on paper but requires the same missing
strict-improvement lemma. The Krein-Milman step is **plug-and-play in
Lean**; the work is in the measure-theoretic strict-improvement step.

### §2.3 Olech 1968 (direct convexity)

A bare-hands convexity proof avoiding both Halmos's induction and
Lindenstrauss's extremality: for `v, w ∈ Range μ` with `v = μ A, w = μ B`,
construct `C` with `μ C = ½ (v + w)` directly by bisecting `A △ B` (the
symmetric difference) and adjusting. Requires the same measurable-bisection
lemma but no σ-algebra approximation.

This is the **shortest Lean path** if the measurable-bisection lemma is
already available. Olech 1968 fits in ~30-50 LOC once bisection is there.

### §2.4 Recommendation

Of the three proofs:

* **Olech 1968** is the recommended Lean path for Lyapunov, conditional
  on first establishing the standalone measurable-bisection lemma.
* **Lindenstrauss 1966** has a more elegant statement but requires the
  same prerequisite.
* **Halmos 1948** is the most copied in textbooks but is the **most**
  Lean-unfriendly because of the finite-σ-algebra approximation step.

---

## §3. Aumann's set-valued integral — building on Lyapunov

Aumann 1965 generalizes Lyapunov from "range of a vector measure" to
"integral of a set-valued map".

> Let `(Ω, μ)` be an atomless probability space and `F : Ω → Set ℝⁿ` a
> measurable, integrably bounded set-valued map. Then
> ` ∫ F dμ := { ∫ f dμ | f measurable selection, f ω ∈ F ω a.e. } `
> is convex and compact in `ℝⁿ`.

The proof reduces to Lyapunov: for each pair `f₁, f₂` of selections and
`t ∈ [0,1]`, apply Lyapunov to the `ℝⁿ`-valued measure
`A ↦ ∫_A (f₁ - f₂) dμ` to find `A ⊆ Ω` with
`∫_A (f₁ - f₂) dμ = (1-t) · ∫_Ω (f₁ - f₂) dμ`, and define
`f := f₁ · 𝟙_A + f₂ · 𝟙_{Aᶜ}`; then `∫ f dμ = t · ∫ f₁ dμ + (1-t) · ∫ f₂ dμ`.

**Mathlib prerequisites for Aumann on top of Lyapunov:**

| Ingredient                                       | Where in Mathlib                                                  | Status      |
|--------------------------------------------------|-------------------------------------------------------------------|-------------|
| Measurable selection theorem (Kuratowski-Ryll-Nardzewski) | None as a fully general theorem (partial: `MeasurableEmbedding.exists_left_inverse_of_injOn`) | **Missing** |
| Set-valued map `F : Ω → Set ℝⁿ` measurability     | `Mathlib.MeasureTheory.Function.LpSpace`-style not yet generalized | **Missing as a typeclass** |
| Aumann set-integral `∫ F dμ` as a `Set`           | None                                                              | **Missing** |
| Bochner integral on `ℝⁿ` selections               | `Mathlib.MeasureTheory.Function.Bochner`                          | Present     |
| Convex combination of selections                  | Derivable from `Bochner.integral_add` + `integral_smul`           | Present     |

The **measurable-selection theorem** (Kuratowski-Ryll-Nardzewski
1965) is the second major prerequisite. It states that any
non-empty-valued, weakly measurable, closed-valued set-valued map
from a complete measurable space to a Polish space admits a
measurable selection. It is **not** in Mathlib v4.26.0 (confirmed
by code search for `MeasurableSelection`, `Kuratowski.RyllNardzewski`,
`measurable_selection` — zero hits in `Mathlib.MeasureTheory.*`).

**Estimated Lean LOC for Aumann conditional on Lyapunov + measurable
selection**: ~80-120 LOC, mostly composing the two upstream theorems
with the convex-combination construction above.

---

## §4. Mathlib `VectorMeasure` API: present but not exploited

Mathlib has substantial vector-measure infrastructure under
`Mathlib.MeasureTheory.VectorMeasure.*`:

* `Mathlib.MeasureTheory.VectorMeasure.Basic` — definition of
  `VectorMeasure α M` as a countably-additive signed/vector-valued
  function on measurable sets, plus the `measureOf` projection.
* `Mathlib.MeasureTheory.VectorMeasure.Integral` — Bochner integral
  against a vector measure.
* `Mathlib.MeasureTheory.VectorMeasure.AddContent` — finitely-additive
  precursor.
* `Mathlib.MeasureTheory.VectorMeasure.WithDensity` — Radon-Nikodym
  derivative variant.
* `Mathlib.MeasureTheory.VectorMeasure.Decomposition.{Jordan,JordanSub,Lebesgue,RadonNikodym}`
  — full Jordan + Lebesgue + Radon-Nikodym decomposition theorems.
* `Mathlib.MeasureTheory.VectorMeasure.{Variation/Defs,BoundedVariation}`
  — total variation.

What is **not** in this folder:

* **`VectorMeasure.range`** as a Set of values (`{ μ A | MeasurableSet A }`).
* **Range convexity** under any atomlessness hypothesis.
* **Range compactness** under any finite-variation hypothesis.
* **NoAtoms** typeclass for `VectorMeasure` (only for `Measure`).

The first item — defining the range as a Set — is a one-line definition
in Lean (`Set.image VectorMeasure.measureOf {s | MeasurableSet s}`) but
needs to be added before any range-property theorem can be stated. This
is a natural standalone Mathlib contribution independent of Lyapunov.

---

## §5. Work-scope estimate

Decomposing Approaches A and B into Lean sessions:

### §5.1 Approach B (Lyapunov for `ℝⁿ`)

| Session   | Target                                                          | LOC est. | Blockers                                    |
|-----------|-----------------------------------------------------------------|----------|---------------------------------------------|
| L-1       | `Measure.exists_subset_half_measure` (measurable bisection)     | 50-80    | None                                        |
| L-2       | `VectorMeasure.range` definition + basic lemmas                  | 20-40    | None                                        |
| L-3       | `VectorMeasure.NoAtoms` typeclass + `iff` lemma vs scalar `NoAtoms` | 30-50    | None                                        |
| L-4       | `Lyapunov_two_atoms` (n=2 case: range is a segment)              | 40-70    | L-1, L-2, L-3                               |
| L-5       | `Lyapunov_general` via Olech induction on `n`                    | 80-150   | L-4                                         |
| L-6       | Apply Lyapunov to `shapley-folkman-oq-01` infinite-dim analog    | 50-100   | L-5; new statement design                   |

**Approach B total**: ~270-490 LOC across 6 sessions, all in Mathlib-style
upstream + one application.

### §5.2 Approach A (Aumann set-valued integral)

| Session   | Target                                                          | LOC est. | Blockers                                    |
|-----------|-----------------------------------------------------------------|----------|---------------------------------------------|
| A-1       | `MeasurableSelection.kuratowski_ryll_nardzewski`                 | 100-200  | None                                        |
| A-2       | `AumannIntegral` set definition + measurable-selection-set       | 30-50    | A-1                                         |
| A-3       | Two-selection convex-combination lemma                           | 40-60    | A-2 + Approach B (L-1..L-5)                 |
| A-4       | `AumannIntegral_convex` via Lyapunov                              | 50-80    | A-3                                         |
| A-5       | `AumannIntegral_compact` (closedness + boundedness)               | 40-80    | A-4                                         |
| A-6       | Apply Aumann to `shapley-folkman-oq-01` infinite-dim analog       | 50-100   | A-5; new statement design                   |

**Approach A total**: ~310-570 LOC across 6 sessions, building on
all of Approach B's prerequisites.

### §5.3 Comparison with locked Approach C (S2 PREP #18397)

| Approach | LOC est. | Sessions | Axioms | Upstream blockers                                      |
|----------|----------|----------|--------|--------------------------------------------------------|
| A (Aumann)   | 310-570 | 6 | 0 | Measurable bisection + measurable selection + Lyapunov |
| B (Lyapunov) | 270-490 | 6 | 0 | Measurable bisection                                   |
| C (counter-example) | 70-100  | 1 | 0 | None                                                   |

**Approach C is 3-7× cheaper and unblocks immediately**, which is the
correct rationale for S2 PREP locking C. Approaches A and B remain
worthwhile **standalone** Mathlib contributions even after C lands.

---

## §6. Decision criterion: when does A or B become viable

Switching from C to A or B becomes worthwhile if **any** of these happen:

1. **A measurable-bisection lemma lands in Mathlib** (e.g., a Mathlib
   contributor proves `Measure.exists_subset_half_measure` for an
   independent application like Hausdorff measures or
   atomless-measure theory). This unblocks Approach B's first session.
2. **The Wiedijk 100-theorems wishlist** (`docs/1000.yaml` in Mathlib)
   explicitly upgrades "Lyapunov's convexity theorem" to a target,
   making it a community priority.
3. **A separate gallery proof** (e.g., for an economics-flavored
   `aumann-equilibrium` slug) needs Lyapunov, justifying the upstream
   investment with > 1 downstream consumer.
4. **Mathlib v4.27+ ships a `VectorMeasure.NoAtoms` typeclass** or
   equivalent infrastructure as a side-effect of unrelated work.

Until then, Approach C remains the right S2 ACT target.

---

## §7. Anti-targets (do NOT attempt in this session or any short S2/S3)

1. **Stating Lyapunov directly in `proofs/Proofs/ShapleyFolkmanInfDim.lean`**
   without proving it. This would be a 1-line `axiom` declaration and
   would violate the project's axiom-integrity policy (a 1-axiom proof
   is no better than the parent's 0-axiom proof).
2. **Vendoring an external Lean 3 / Lean 4 community proof of Lyapunov**
   without auditing the API drift against current Mathlib. Multiple
   Lean 3 attempts exist (see `leanprover-community/mathlib3` issue
   history) but none ported cleanly.
3. **Attempting Aumann without Lyapunov.** Aumann's standard proof
   *uses* Lyapunov; alternative proofs (e.g., via Castaing
   representation) require even more measurable-selection
   machinery.
4. **Stating the infinite-dim Shapley–Folkman as an `axiom`** with no
   proof. The parent gallery proof is `verified` (0 axioms); adding an
   axiomatized child would clutter the `axiomatized` count without
   reflecting real mathematical content.

---

## §8. Honest framing

This S1b is a **prerequisite audit**, not a proof attempt. The deliverable
is the table of work-scope estimates in §5 and the decision criterion in
§6. After this note, the S(N) chain for Approaches A and B should be
considered **dormant pending upstream Mathlib evolution**, with Approach
C (S2 PREP #18397) as the active path. A future researcher with a strong
interest in Aumann markets or Lyapunov-style range-convexity results
should treat L-1 (measurable bisection) as the natural first standalone
Mathlib PR.

**Novelty claim**: none. Every theorem cited here is decades old. The
contribution is the **Mathlib-prerequisite map** and the **work-scope
estimate** — useful for planning, not for proving.

**Build status**: no `.lean` changes; no build attempted.

**No edits to**: `problem.md`, `state.md`, `knowledge.md`, the
existing `sessions/2026-05-12-s01-observe.md`, the `lean/` subfolder,
the gallery `meta.json`, or any other tracked file. This PR adds exactly
one new file: this session note.

---

## §9. References

* **Lyapunov, A. A. (1940).** "Sur les fonctions-vecteurs complètement
  additives." *Bull. Acad. Sci. USSR (Ser. Math.)* 4, 465–478.
* **Halmos, P. R. (1948).** "The range of a vector measure." *Bull.
  Amer. Math. Soc.* 54 (4), 416–421.
* **Lindenstrauss, J. (1966).** "A short proof of Liapounoff's convexity
  theorem." *J. Math. Mech.* 15, 971–972.
* **Olech, C. (1968).** "Extremal solutions of a control system."
  *J. Differential Equations* 2 (1), 74–101.
* **Aumann, R. J. (1965).** "Integrals of set-valued functions." *J. Math.
  Anal. Appl.* 12 (1), 1–12.
* **Kuratowski, K., and Ryll-Nardzewski, C. (1965).** "A general theorem
  on selectors." *Bull. Acad. Polon. Sci. Sér. Sci. Math. Astronom. Phys.*
  13, 397–403.
* **Castaing, C., and Valadier, M. (1977).** *Convex Analysis and
  Measurable Multifunctions.* Lecture Notes in Mathematics 580.
* **Shapley-Folkman parent**: `proofs/Proofs/ShapleyFolkman.lean`
  (1238 lines, 0 sorries, 0 axioms).
* **Mathlib `VectorMeasure` module**:
  `Mathlib.MeasureTheory.VectorMeasure.{Basic,Integral,AddContent,WithDensity,BoundedVariation,Variation/Defs,Decomposition/*}`
  (present at v4.26.0).
* **Mathlib `NoAtoms`**: `Mathlib.MeasureTheory.Measure.Typeclasses`.
* **Wiedijk 1000-theorems wishlist**: `docs/1000.yaml` in
  `leanprover-community/mathlib4` mentions Lyapunov's convexity theorem
  as a target (zero hits inside `Mathlib/MeasureTheory/`).

---

*End of session note. No other files modified.*
