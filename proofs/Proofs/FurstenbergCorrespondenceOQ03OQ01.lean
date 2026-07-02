import Mathlib
import Proofs.FurstenbergCorrespondenceOQ03

/-!
# Furstenberg OQ-03-OQ-01: the `NoConstantTerm` hypothesis is essential

A child of `furstenberg-correspondence-oq-03`, which states the polynomial
Szemerédi theorem (Bergelson–Leibman) and its `PolynomialSzemerediProperty`
**under the standing hypothesis `NoConstantTerm p`** (every `pᵢ(0) = 0`). The
parent verifies that this hypothesis makes every configuration collapse to the
base point at `d = 0` and forces `d ∣ pᵢ(d)`, but it does not show the
hypothesis is *necessary*.

This entry supplies the missing necessity: **without `NoConstantTerm`, the
conclusion genuinely fails**, even for a set as large as the even integers
(density `1/2`). The obstruction is a single parity congruence.

Concretely, take `E = { n : ℤ | Even n }` and the constant-term family
`badFamily = ![0, 2X + 1]` (so `badFamily 1` has `pᵢ(0) = 1 ≠ 0`). The two
configuration points are `x` and `x + (2d + 1)`, which can never both be even.
Hence `E` fails the unconstrained pattern property, while it has density `1/2`
and while the *no-constant-term* square family `![0, X²]` **does** realize a
nontrivial configuration inside `E`.

Results:
* `badFamily_hasConstantTerm` — `badFamily` is outside Bergelson–Leibman's scope.
* `even_avoids_badConfig` — no `{x, x + 2d + 1}` lies in `E`.
* `UnconstrainedSzemerediProperty` / `even_not_unconstrainedSzemeredi` — the
  even integers fail the constant-term-allowed pattern property.
* `even_count_range` — `E` has density `1/2` (exactly `N` evens below `2N`), so
  the failure is not a smallness artefact.
* `squareFamily_realized_in_even` — the *no-constant-term* square family still
  lands in `E`, isolating the constant term as the sole obstruction.

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).
-/

open Polynomial

namespace FurstenbergCorrespondenceOQ03OQ01

open FurstenbergOQ03 (configPoint NoConstantTerm squareFamily)

/-- The even integers, the positive-density set that will avoid a constant-term
    pattern. -/
def E : Set ℤ := {n : ℤ | Even n}

/-- A two-point family with a **nonzero constant term**: `p₀ = 0`, `p₁ = 2X + 1`.
    Its second polynomial has `p₁(0) = 1 ≠ 0`, so it lies outside the
    Bergelson–Leibman hypothesis. -/
noncomputable def badFamily : Fin 2 → ℤ[X] := ![0, 2 * X + 1]

/-!
## Section 1: `badFamily` is outside Bergelson–Leibman's scope
-/

/-- `badFamily` violates `NoConstantTerm`: `(2X + 1).eval 0 = 1 ≠ 0`. -/
theorem badFamily_hasConstantTerm : ¬ NoConstantTerm badFamily := by
  intro h
  have h1 := h 1
  simp [badFamily] at h1

/-!
## Section 2: the parity obstruction
-/

/-- The two configuration points of `badFamily` are `x` and `x + (2d + 1)`. -/
theorem configPoint_badFamily (x d : ℤ) :
    configPoint badFamily x d 0 = x ∧
    configPoint badFamily x d 1 = x + (2 * d + 1) := by
  refine ⟨?_, ?_⟩ <;> simp [configPoint, badFamily]

/-- **The parity obstruction.** No `d` (nonzero or not) makes both configuration
    points of `badFamily` even: `x` and `x + (2d + 1)` have opposite parities. -/
theorem even_avoids_badConfig (x d : ℤ) :
    ¬ (configPoint badFamily x d 0 ∈ E ∧ configPoint badFamily x d 1 ∈ E) := by
  obtain ⟨h0, h1⟩ := configPoint_badFamily x d
  rw [h0, h1]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  omega

/-!
## Section 3: the even integers fail the constant-term-allowed property
-/

/-- The pattern property **without** the `NoConstantTerm` hypothesis: every
    finite nonempty family (constant term allowed) is realized as a nontrivial
    configuration. This is the over-strong statement Bergelson–Leibman does
    *not* claim. -/
def UnconstrainedSzemerediProperty (A : Set ℤ) : Prop :=
  ∀ (k : ℕ) (p : Fin k → ℤ[X]), 0 < k →
    ∃ x d : ℤ, d ≠ 0 ∧ ∀ i, configPoint p x d i ∈ A

/-- **The even integers fail the unconstrained property.** Witnessed by
    `badFamily`, whose configuration can never lie in `E`. Since `E` has
    density `1/2` (`even_count_range`), this shows the `NoConstantTerm`
    hypothesis of Bergelson–Leibman cannot be dropped. -/
theorem even_not_unconstrainedSzemeredi : ¬ UnconstrainedSzemerediProperty E := by
  intro h
  obtain ⟨x, d, _, hmem⟩ := h 2 badFamily (by norm_num)
  exact even_avoids_badConfig x d ⟨hmem 0, hmem 1⟩

/-!
## Section 4: the avoiding set has density 1/2
-/

/-- **`E` has density `1/2`:** exactly `N` of the naturals below `2N` are even.
    So the pattern-avoiding set is genuinely large — the failure in
    `even_not_unconstrainedSzemeredi` is not a smallness artefact. -/
theorem even_count_range (N : ℕ) :
    ((Finset.range (2 * N)).filter (fun n => Even n)).card = N := by
  have hset : (Finset.range (2 * N)).filter (fun n => Even n)
      = (Finset.range N).image (fun m => 2 * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, k, rfl⟩
      exact ⟨k, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨by omega, ⟨m, by omega⟩⟩
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := by
    intro a b h
    simp only [] at h
    omega
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-!
## Section 5: the constant term is the *only* obstruction
-/

/-- **Contrast: the no-constant-term square family *does* land in `E`.** Taking
    `x = 0`, `d = 2` gives the configuration `{0, 4} ⊆ E`. So the failure in
    `even_not_unconstrainedSzemeredi` is caused precisely by the constant term,
    not by any inherent scarcity of polynomial configurations in `E`. -/
theorem squareFamily_realized_in_even :
    ∃ x d : ℤ, d ≠ 0 ∧ ∀ i, configPoint squareFamily x d i ∈ E := by
  refine ⟨0, 2, by norm_num, ?_⟩
  intro i
  fin_cases i <;> simp [configPoint, squareFamily, E] <;> decide

end FurstenbergCorrespondenceOQ03OQ01
