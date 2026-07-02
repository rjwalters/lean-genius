import Mathlib

/-
# Law of Cosines — OQ-07-OQ-01: The Jordan–von Neumann Theorem
  (the parallelogram law characterises inner-product norms)

## Research Problem: law-of-cosines-oq-07-oq-01

Parent `law-of-cosines-oq-07` proves the **parallelogram law** as a consequence
of Apollonius's median identity:

    ‖x + y‖² + ‖x − y‖² = 2 · (‖x‖² + ‖y‖²)

holds in every real (or complex) inner-product space.  Its first open question
asks for the **converse**: the parallelogram law is not merely *necessary* for a
norm to come from an inner product — it is *sufficient*.  This is the classical
**Fréchet–von Neumann–Jordan theorem** (Jordan–von Neumann 1935): a normed space
whose norm satisfies the parallelogram identity carries a compatible inner
product, recovered from the norm by polarisation.

Mathlib supplies the hard analytic content as `InnerProductSpace.ofNorm`
(the polarisation construction, together with the additivity and homogeneity of
the resulting form).  This entry packages the two directions into a single
**characterisation**:

  * `parallelogram_of_innerProductSpace` — the forward (easy) direction: every
    inner-product norm obeys the parallelogram law.
  * `innerProductSpaceOfParallelogram`  — the converse, as an explicit
    (noncomputable) `InnerProductSpace` structure built from a parallelogram
    hypothesis.
  * `nonempty_innerProductSpace_iff_parallelogram` — the headline biconditional:
    a norm admits a *compatible inner product* **iff** it satisfies the
    parallelogram law.  No `InnerProductSpaceable` typeclass appears in the
    statement — it is phrased purely in terms of the norm.

The forward direction is `parallelogram_law_with_norm`; the converse is
`nonempty_innerProductSpace`.  Both are Mathlib lemmas; the contribution here is
the clean two-sided packaging answering the parent's open question, plus a
concrete confirmation on the Euclidean plane.

DISTINCT from `law-of-cosines-oq-07-oq-02` (sum of the squared medians), which
develops the *metric/affine* side of the parent; this entry develops its
*functional-analytic* side.

Tags: functional-analysis, inner-product-space, parallelogram-law,
jordan-von-neumann, law-of-cosines
-/

open RCLike

namespace LawOfCosinesOQ07OQ01

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

omit [NormedSpace 𝕜 E] in
/-- **Forward direction (necessity).** In any inner-product space the norm
satisfies the parallelogram identity.  This is the statement the parent entry
`law-of-cosines-oq-07` derives from Apollonius's median identity; here it is the
easy half of the Jordan–von Neumann characterisation. -/
theorem parallelogram_of_innerProductSpace [InnerProductSpace 𝕜 E] (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) :=
  parallelogram_law_with_norm 𝕜 x y

/-- **Converse direction (sufficiency): the Fréchet–von Neumann–Jordan theorem.**
A normed `𝕜`-space whose norm satisfies the parallelogram identity can be endowed
with a compatible inner product, obtained from the norm by polarisation.  This is
a thin wrapper around Mathlib's `InnerProductSpace.ofNorm`, exposed here as the
explicit answer to the parent's open question. -/
noncomputable def innerProductSpaceOfParallelogram
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 E :=
  InnerProductSpace.ofNorm (𝕜 := 𝕜) h

/-- **The Jordan–von Neumann characterisation.**  A normed `𝕜`-space admits a
compatible inner product **if and only if** its norm satisfies the parallelogram
identity.  The statement mentions only the norm — the inner product is existentially
quantified via `Nonempty (InnerProductSpace 𝕜 E)`. -/
theorem nonempty_innerProductSpace_iff_parallelogram :
    Nonempty (InnerProductSpace 𝕜 E) ↔
      ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  constructor
  · rintro ⟨inst⟩
    letI := inst
    exact fun x y => parallelogram_law_with_norm 𝕜 x y
  · intro h
    haveI : InnerProductSpaceable E := ⟨h⟩
    exact nonempty_innerProductSpace 𝕜 E

/-- Restated for the reader who wants the converse as a bare implication:
the parallelogram identity guarantees *some* compatible inner product exists. -/
theorem exists_inner_of_parallelogram
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    Nonempty (InnerProductSpace 𝕜 E) :=
  (nonempty_innerProductSpace_iff_parallelogram (𝕜 := 𝕜)).2 h

/-- Concrete confirmation on the Euclidean plane `EuclideanSpace ℝ (Fin 2)`:
being an honest inner-product space, its norm satisfies the parallelogram law,
so the characterisation recognises it. -/
example : ∀ x y : EuclideanSpace ℝ (Fin 2),
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) :=
  (nonempty_innerProductSpace_iff_parallelogram (𝕜 := ℝ)).1 ⟨inferInstance⟩

end LawOfCosinesOQ07OQ01
