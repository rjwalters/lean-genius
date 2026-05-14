/-
  Brouwer Fixed Point OQ-01-OQ-02-OQ-03-OQ-02: S9 ACT-D-3 PREP

  Companion file installing the **G8 functoriality bridge** and the
  **G9 retract-of-zero bridge** — the two remaining categorical pieces
  needed by S9 ACT-D-3 once sibling PR #18011 (G6 Subsingleton-bridge)
  merges. Parallels the `BrouwerFixedPointOQ01OQ02G7.lean` companion
  installed in S8 ACT-D-2 EXEC (PR #18951, build verified in PR #19013).

  Both lemmas are **pure category theory**: no singular homology, no
  topology, no abelian-category machinery. They depend only on:

  * `Mathlib.CategoryTheory.Functor.Basic` — `Functor.map_comp`,
    `Functor.map_id`.
  * `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects` — `Limits.IsZero`,
    `IsZero.to_`, `IsZero.from_`, `IsZero.eq_of_src`, `IsZero.eq_of_tgt`.

  Two theorems are exposed in namespace `BrouwerFixedPointOQ01OQ02`:

  * `map_section_of_section` — **G8**: any functor `F : C ⥤ D` sends a
    one-sided section `i ≫ r = 𝟙 X` in `C` to a one-sided section
    `F.map i ≫ F.map r = 𝟙 (F.obj X)` in `D`. This is the categorical
    abstraction of "singular homology is a functor, so a topological
    retraction induces a section on homology".

  * `isZero_of_section_into_isZero` — **G9**: if `X` is a retract of a
    zero object `Y` (via `i : X ⟶ Y`, `r : Y ⟶ X`, `i ≫ r = 𝟙 X`),
    then `X` is itself a zero object. This is the "retract of zero is
    zero" principle in `IsZero` form, used to derive the substantive
    contradiction in S9 ACT-D-3: combining G8 + the substantive ball
    `IsZero` axiom yields G9's hypothesis on the sphere homology,
    contradicting the substantive sphere `¬ IsZero` axiom.

  Net axiom delta: 0. Net theorem delta: +2 (in the companion file).

  ## How S9 ACT-D-3 will combine the G6 / G7 / G8 / G9 bridges

  After sibling PR #18011 (G6) merges, S9 ACT-D-3 will derive the mock
  composite axiom `H_n_minus_1_sphere_nonzero` (line 261 of the main
  file) substantively via the chain:

  1. `H_n_minus_1_ball_zero_substantive` (S5 ACT-B, main file line 310)
     →  `IsZero (H_{n-1}(B^n))`.
  2. **G8** `map_section_of_section` applied to the inclusion-retraction
     pair `i : 𝕊^{n-1} ⟶ B^n`, `r : B^n ⟶ 𝕊^{n-1}` (built from the
     `Retraction n` structure via TopCat morphisms) at the singular-
     homology functor → a section `H_{n-1}(i) ≫ H_{n-1}(r) = 𝟙` on
     homology.
  3. **G9** `isZero_of_section_into_isZero` with `Y := H_{n-1}(B^n)`
     (zero from step 1) and the section from step 2 → `IsZero
     (H_{n-1}(𝕊^{n-1}))`.
  4. `H_n_minus_1_sphere_nonzero_substantive` (S7 ACT-D-1, main file
     line 375) contradicts step 3.
  5. From the contradiction, extract the existential `∃ ψ, ψ ∘ φ = id`
     shape via **G7** `exists_ne_zero_of_not_isZero` and the **G6**
     Subsingleton-bridge from PR #18011 Part VI.

  Steps 1–4 produce the **substantive contradiction** that closes the
  homological argument; G7 + G6 are the final algebraic transport into
  the `Unit`-flavoured shape consumed by the existing
  `singular_homology_retraction_split` theorem (main file line 395).

  This companion file delivers steps 2 and 3 in advance, parallel to
  G7 (which delivered step 5's first half). After PR #18011 merges,
  S9 ACT-D-3 becomes a clean import-and-wire affair in the main file.

  Companion-file (not inline) per the §N5 Option A precedent from G7:
  build-risk isolation + review parallelism.
-/

import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open CategoryTheory

namespace BrouwerFixedPointOQ01OQ02

/-- **G8 functoriality bridge**: any functor `F : C ⥤ D` sends a one-sided
    section `i ≫ r = 𝟙 X` in `C` to a one-sided section
    `F.map i ≫ F.map r = 𝟙 (F.obj X)` in `D`.

    Proof: rewrite via `Functor.map_comp` then `Functor.map_id`. The two
    rewrites are both definitional unfoldings of the functor laws, so
    the entire proof is `rw [← F.map_comp, h, F.map_id]`.

    Specialized at `F := (AlgebraicTopology.singularHomologyFunctor
    AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)`, this lemma says:
    given continuous maps `i : X ⟶ Y` and `r : Y ⟶ X` in `TopCat` with
    `i ≫ r = 𝟙 X`, the singular-homology functor sends them to a
    section on `H_n(X)`. This is the third leg of the S9 ACT-D-3
    derivation. -/
theorem map_section_of_section {C : Type*} [Category C]
    {D : Type*} [Category D] (F : C ⥤ D)
    {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X) :
    F.map i ≫ F.map r = 𝟙 (F.obj X) := by
  rw [← F.map_comp, h, F.map_id]

/-- **G9 retract-of-zero bridge**: if `X` is a retract of a zero object
    `Y` (witnessed by `i : X ⟶ Y`, `r : Y ⟶ X`, and `i ≫ r = 𝟙 X`),
    then `X` is itself a zero object.

    Proof: for any object `Z`, the unique morphism `X ⟶ Z` is
    `i ≫ hY.to_ Z` — any `f : X ⟶ Z` satisfies
    `f = 𝟙 X ≫ f = (i ≫ r) ≫ f = i ≫ (r ≫ f)`, and `r ≫ f : Y ⟶ Z`
    is unique because `Y` is a zero object (`IsZero.eq_of_src`).
    Dually, the unique morphism `Z ⟶ X` is `hY.from_ Z ≫ r`.

    This is the "retract of zero is zero" principle in `IsZero` form.
    It is used by S9 ACT-D-3 to derive the substantive contradiction:
    the substantive ball axiom `H_n_minus_1_ball_zero_substantive` gives
    `IsZero (H_{n-1}(B^n))`; combined with the G8 section from the
    inclusion-retraction pair, this yields `IsZero (H_{n-1}(𝕊^{n-1}))`,
    contradicting the substantive sphere axiom
    `H_n_minus_1_sphere_nonzero_substantive`. -/
theorem isZero_of_section_into_isZero {C : Type*} [Category C]
    {X Y : C} (hY : Limits.IsZero Y) (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) :
    Limits.IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨i ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
          fun Z => ⟨⟨⟨hY.from_ Z ≫ r⟩, fun f => ?_⟩⟩⟩
  · -- Goal: f = i ≫ hY.to_ Z, given any f : X ⟶ Z.
    -- Step: rewrite f via 𝟙 X = i ≫ r, then use IsZero.eq_of_src on r ≫ f.
    calc f = 𝟙 X ≫ f := (Category.id_comp f).symm
      _ = (i ≫ r) ≫ f := by rw [h]
      _ = i ≫ (r ≫ f) := Category.assoc i r f
      _ = i ≫ hY.to_ Z := by rw [hY.eq_of_src (r ≫ f) (hY.to_ Z)]
  · -- Goal: f = hY.from_ Z ≫ r, given any f : Z ⟶ X.
    -- Step: rewrite f via 𝟙 X = i ≫ r, then use IsZero.eq_of_tgt on f ≫ i.
    calc f = f ≫ 𝟙 X := (Category.comp_id f).symm
      _ = f ≫ (i ≫ r) := by rw [h]
      _ = (f ≫ i) ≫ r := (Category.assoc f i r).symm
      _ = hY.from_ Z ≫ r := by rw [hY.eq_of_tgt (f ≫ i) (hY.from_ Z)]

end BrouwerFixedPointOQ01OQ02
