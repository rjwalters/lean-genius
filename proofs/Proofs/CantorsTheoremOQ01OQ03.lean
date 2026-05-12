import Proofs.CantorsTheoremOQ01
import Proofs.CantorsTheoremOQ01OQ02
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-
# König's Constraint, Formalized Without Axioms

## Open Question (resolved YES): cantors-theorem-oq-01-oq-03

The parent file `CantorsTheoremOQ01.lean` mentioned König's theorem
`cf(2^κ) > κ` only in commentary (Part 7) and did not formalize it.
The open question oq-01-oq-03 asked:

  **"Can König's constraint be formalized in Lean4 without axioms?
   (Requires formalizing infinite product cardinal arithmetic)"**

This file resolves the question affirmatively. The cofinality form
`cf(2^κ) > κ` for any infinite κ is exactly Mathlib's
`Cardinal.lt_cof_power`, which is a *theorem* (not an `axiom`). All
results below are proved with 0 `axiom` declarations and 0 `sorry`s.

## Caveats on "Without Axioms"

- **"Without explicit `axiom` declarations":** YES. This file uses only
  Mathlib's `Cardinal.lt_cof_power`, `Cardinal.aleph0_le_continuum`,
  `Cardinal.aleph0_le_aleph`, etc. — all theorems.
- **"Without the Axiom of Choice":** NO. Mathlib's set-theoretic library
  uses `Classical.choice` silently. König's theorem in its full
  generality (for arbitrary cardinal-indexed products `∏ g_i > ∑ f_i`
  whenever `f_i < g_i`) requires Choice — the witness for each
  `f_i < g_i` must be chosen.

So "without axioms" is read as **"without axioms beyond ZFC"**, which
is the standard formal-mathematics convention and was the intent of the
parent question.

## Main Results

1. `konig_general` — for any infinite κ, κ < cf(2^κ)
2. `konig_constraint_continuum` — applied to 𝔠 (parallels sibling oq-02)
3. `konig_constraint_aleph` — applied to ℵ_α
4. `konig_constraint_beth` — applied to ℶ_α (ordinal generalization of
   sibling oq-02's `konig_constraint_beth (n : ℕ)`)
5. `cf_powerSet_real_gt_continuum` — cf(|𝒫(ℝ)|) > 𝔠
6. `cf_powerSet_real_ne_aleph0` — cf(|𝒫(ℝ)|) ≠ ℵ₀
7. `oq01oq03_resolution` — bundle theorem affirmatively answering the OQ

## Relationship to Parent and Sibling

- Parent `CantorsTheoremOQ01`: asserts `|𝒫(ℝ)| = ℶ₂` and mentions König
  in a docstring (Part 7) as motivation, without proof.
- Sibling `CantorsTheoremOQ01OQ02`: extends the beth tower to ℶ₃ and
  includes one König specialization (`konig_constraint_powerSet_real`)
  as a side observation. We import that file but state König in its
  general form `∀ infinite κ, κ < cf(2^κ)`, then specialize.

The new content here vs the sibling:
- `konig_general` (universally quantified, not just specialized to 𝔠).
- `konig_constraint_aleph` (parameterized over arbitrary aleph index).
- `konig_constraint_beth` (parameterized over arbitrary *ordinal* index;
  sibling's version is restricted to `n : ℕ`).
- `cf_powerSet_real_ne_aleph0` (canonical "rules out ℵ_ω" corollary).
- `oq01oq03_resolution` (bundles four forms as the OQ resolution).
-/

set_option linter.unusedVariables false

namespace CantorsTheoremOQ01OQ03

open Cardinal

-- ============================================================
-- PART 1: King's Cofinality Theorem in General Form
-- ============================================================

/-- **König's Theorem (cofinality form)**: For any infinite cardinal κ,
    the cofinality of `2^κ` strictly exceeds κ.

    This is the foundational ZFC constraint on the cardinal arithmetic
    of power sets. It rules out `2^κ` being any cardinal whose cofinality
    is ≤ κ — for κ = ℵ₀, this rules out 2^ℵ₀ = ℵ_ω; for κ = 𝔠, this
    rules out 2^𝔠 = ℵ_ω, ℵ_{ω·2}, etc.

    Proved without explicit axioms via Mathlib's `Cardinal.lt_cof_power`. -/
theorem konig_general {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) :
    κ < (2 ^ κ).ord.cof :=
  Cardinal.lt_cof_power hκ (by norm_num)

-- ============================================================
-- PART 2: Specializations
-- ============================================================

/-- **König's constraint for the continuum**: 𝔠 < cf(2^𝔠).

    Specialization of `konig_general` to κ = 𝔠 = 2^ℵ₀.
    Equivalent statement to `CantorsTheoremOQ01OQ02.konig_constraint_powerSet_real`,
    proved here as an immediate corollary of the general form. -/
theorem konig_constraint_continuum :
    (𝔠 : Cardinal.{0}) < (2 ^ (𝔠 : Cardinal.{0})).ord.cof :=
  konig_general Cardinal.aleph0_le_continuum

/-- **König's constraint for ℵ_α**: For any ordinal α, ℵ_α < cf(2^ℵ_α).

    This says that for *every* infinite aleph cardinal κ = ℵ_α (regardless
    of whether α is small or large), `2^κ` has cofinality strictly greater
    than κ. The constraint is uniform over the entire aleph hierarchy. -/
theorem konig_constraint_aleph (α : Ordinal.{0}) :
    (Cardinal.aleph α : Cardinal.{0}) <
      (2 ^ (Cardinal.aleph α : Cardinal.{0})).ord.cof :=
  konig_general (Cardinal.aleph0_le_aleph α)

/-- **König's constraint for ℶ_α (ordinal generalization)**: For any
    ordinal α, ℶ_α < cf(2^ℶ_α).

    Generalizes sibling `CantorsTheoremOQ01OQ02.konig_constraint_beth`,
    which is stated only for `n : ℕ`, to arbitrary ordinals. The proof
    reuses sibling's `beth_zero.symm` + `beth_strictMono.monotone` chain
    to establish `ℵ₀ ≤ ℶ_α`, then invokes `konig_general`. -/
theorem konig_constraint_beth (α : Ordinal.{0}) :
    (Cardinal.beth α : Cardinal.{0}) <
      (2 ^ (Cardinal.beth α : Cardinal.{0})).ord.cof := by
  apply konig_general
  calc (ℵ₀ : Cardinal.{0})
      = Cardinal.beth 0 := Cardinal.beth_zero.symm
    _ ≤ Cardinal.beth α :=
        Cardinal.beth_strictMono.monotone (Ordinal.zero_le _)

-- ============================================================
-- PART 3: Application to |𝒫(ℝ)|
-- ============================================================

/-- **König's constraint for |𝒫(ℝ)|**: cf(|𝒫(ℝ)|) > 𝔠.

    Combines `konig_constraint_continuum` with the parent's
    `card_powerSet_real_formula` (|𝒫(ℝ)| = 2^𝔠). -/
theorem cf_powerSet_real_gt_continuum :
    (𝔠 : Cardinal.{0}) < (#(Set ℝ)).ord.cof := by
  rw [CantorsTheoremOQ01.card_powerSet_real_formula]
  exact konig_constraint_continuum

/-- **Corollary: cf(|𝒫(ℝ)|) ≠ ℵ₀.**

    From cf(|𝒫(ℝ)|) > 𝔠 ≥ ℵ₀, the cofinality of |𝒫(ℝ)| is strictly
    greater than ℵ₀. This rules out, e.g., |𝒫(ℝ)| = ℵ_ω (which has
    cofinality ℵ₀). -/
theorem cf_powerSet_real_ne_aleph0 :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ ℵ₀ := by
  intro h
  -- h : (#(Set ℝ)).ord.cof = ℵ₀
  -- But cf_powerSet_real_gt_continuum says 𝔠 < (#(Set ℝ)).ord.cof
  -- and aleph0_le_continuum says ℵ₀ ≤ 𝔠.
  have h1 : (𝔠 : Cardinal.{0}) < ℵ₀ := h ▸ cf_powerSet_real_gt_continuum
  have h2 : (ℵ₀ : Cardinal.{0}) ≤ 𝔠 := Cardinal.aleph0_le_continuum
  exact absurd (h1.trans_le h2) (lt_irrefl _)

-- ============================================================
-- PART 4: Resolution Bundle
-- ============================================================

/-- **Resolution of `cantors-theorem-oq-01-oq-03`**: König's constraint
    cf(2^κ) > κ (for any infinite κ) IS formalizable in Lean4 without
    explicit `axiom` declarations.

    This bundle theorem packages four salient forms of König's constraint
    proved above, demonstrating the affirmative resolution of the OQ. -/
theorem oq01oq03_resolution :
    -- (1) General König for any infinite cardinal
    (∀ {κ : Cardinal.{0}}, ℵ₀ ≤ κ → κ < (2 ^ κ).ord.cof) ∧
    -- (2) König applied to 𝔠
    ((𝔠 : Cardinal.{0}) < (2 ^ (𝔠 : Cardinal.{0})).ord.cof) ∧
    -- (3) König applied to |𝒫(ℝ)|
    ((𝔠 : Cardinal.{0}) < (#(Set ℝ)).ord.cof) ∧
    -- (4) Cofinality of |𝒫(ℝ)| is not ℵ₀
    ((#(Set ℝ) : Cardinal.{0}).ord.cof ≠ ℵ₀) :=
  ⟨@konig_general,
   konig_constraint_continuum,
   cf_powerSet_real_gt_continuum,
   cf_powerSet_real_ne_aleph0⟩

/-
## Conclusion

**OQ-01-OQ-03**: "Can König's constraint be formalized in Lean4 without
axioms? (Requires formalizing infinite product cardinal arithmetic)"

**Resolution: YES (affirmative)**

Mathlib's `Cardinal.lt_cof_power` (in `Mathlib.SetTheory.Cardinal.Cofinality`)
provides exactly the cofinality form of König's theorem:

  `Cardinal.lt_cof_power : ℵ₀ ≤ κ → 1 < c → κ < (c ^ κ).ord.cof`

(Specializing c = 2 yields the classical König constraint.)

This file packages four salient corollaries:

- **General**: ∀ infinite κ, κ < cf(2^κ)
- **𝔠-specialized**: 𝔠 < cf(2^𝔠)
- **Power-set-of-ℝ specialized**: 𝔠 < cf(|𝒫(ℝ)|)
- **Cofinality not ℵ₀**: cf(|𝒫(ℝ)|) ≠ ℵ₀

All proofs: 0 sorries, 0 explicit `axiom` declarations.

### Note on "infinite product cardinal arithmetic"

The OQ statement said this would *require* formalizing infinite product
cardinal arithmetic. In fact, Mathlib already has `Cardinal.sum_lt_prod`
(König's full inequality `∑ f < ∏ g` whenever `∀ i, f i < g i`), and
`Cardinal.lt_cof_power` is derived from it. So infinite-product cardinal
arithmetic IS formalized in Mathlib — the OQ's caveat is satisfied,
not a blocker.
-/

end CantorsTheoremOQ01OQ03

-- Export key theorems
#check CantorsTheoremOQ01OQ03.konig_general
#check CantorsTheoremOQ01OQ03.konig_constraint_continuum
#check CantorsTheoremOQ01OQ03.konig_constraint_aleph
#check CantorsTheoremOQ01OQ03.konig_constraint_beth
#check CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum
#check CantorsTheoremOQ01OQ03.cf_powerSet_real_ne_aleph0
#check CantorsTheoremOQ01OQ03.oq01oq03_resolution
