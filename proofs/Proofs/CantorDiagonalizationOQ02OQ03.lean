import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic

/-
# Diagonal Argument Generalized to Regular Cardinals (OQ-02 → OQ-03)

## Research Question

Does the Cantor diagonal argument for countable ordinals (OQ-02) generalize to
arbitrary regular cardinals?

## Answer: Yes

For any regular cardinal κ, the "diagonal step" generalizes perfectly:
- Let S be a set of ordinals below κ.ord with #S < κ
- Then sup(S) < κ.ord (by regularity/cofinality)
- So S fails to cover all ordinals below κ.ord

This is the defining property of regular cardinals: cf(κ) = κ means
the ordinal κ.ord cannot be reached as a supremum of fewer than κ ordinals.

The case κ = ℵ₁ recovers OQ-02 (countable ordinals have cardinality ℵ₁).

## Key Mathlib Results Used

- `Cardinal.IsRegular`: κ is regular iff ℵ₀ ≤ κ and cf(κ.ord) = κ
- `Cardinal.sup_lt_ord_of_isRegular`: the generalized diagonal step
- `Cardinal.lsub_lt_ord_of_isRegular`: strict sup version
- `Ordinal.lt_lsub`: each element is strictly below lsub
-/

open Cardinal Ordinal

namespace CantorDiagRegular

-- ══════════════════════════════════════════════════════════════════
-- § 1: The Generalized Diagonal Step
-- ══════════════════════════════════════════════════════════════════

/-- **The generalized diagonal step**: For a regular cardinal κ, any family
    of fewer than κ ordinals below κ.ord has its supremum still below κ.ord.

    This directly generalizes the countable ordinal diagonal argument:
    "a countable union of countable ordinals is countable."
    For regular κ: "a <κ-sized union of <κ.ord ordinals stays below κ.ord." -/
theorem diagonal_step {κ : Cardinal} (hκ : κ.IsRegular)
    {ι : Type*} (hι : #ι < κ)
    (f : ι → Ordinal) (hf : ∀ i, f i < κ.ord) :
    Ordinal.sup f < κ.ord :=
  sup_lt_ord_of_isRegular hκ hι hf

-- ══════════════════════════════════════════════════════════════════
-- § 2: No Small Enumeration Suffices
-- ══════════════════════════════════════════════════════════════════

/-- For regular κ, no function from a <κ-sized index set can cover all
    ordinals below κ.ord. For every such function f, there exists β < κ.ord
    strictly above every f(i).

    Uses `lsub` (strict sup = sup of successors) as the witness:
    lsub f > f(i) for all i, and lsub f < κ.ord by regularity. -/
theorem no_small_surjection {κ : Cardinal} (hκ : κ.IsRegular)
    {ι : Type*} (hι : #ι < κ)
    (f : ι → Ordinal) (hf : ∀ i, f i < κ.ord) :
    ∃ β : Ordinal, β < κ.ord ∧ ∀ i, f i < β :=
  ⟨Ordinal.lsub f, lsub_lt_ord_of_isRegular hκ hι hf,
    fun i => Ordinal.lt_lsub f i⟩

-- ══════════════════════════════════════════════════════════════════
-- § 3: Recovering OQ-02 as a Special Case
-- ══════════════════════════════════════════════════════════════════

/-- ℵ₁ is regular. -/
theorem aleph_one_regular : (Cardinal.aleph 1).IsRegular :=
  Cardinal.isRegular_aleph_one

/-- Special case κ = ℵ₁: a countable set of countable ordinals has
    countable supremum. This is the diagonal step from OQ-02. -/
theorem countable_ordinals_diagonal_step
    {ι : Type*} (hι : #ι < Cardinal.aleph 1)
    (f : ι → Ordinal) (hf : ∀ i, f i < (Cardinal.aleph 1).ord) :
    Ordinal.sup f < (Cardinal.aleph 1).ord :=
  diagonal_step aleph_one_regular hι f hf

/-- No countable enumeration can cover all countable ordinals. -/
theorem countable_ordinals_no_enum
    {ι : Type*} (hι : #ι < Cardinal.aleph 1)
    (f : ι → Ordinal) (hf : ∀ i, f i < (Cardinal.aleph 1).ord) :
    ∃ β : Ordinal, β < (Cardinal.aleph 1).ord ∧ ∀ i, f i < β :=
  no_small_surjection aleph_one_regular hι f hf

-- ══════════════════════════════════════════════════════════════════
-- § 4: The Aleph Hierarchy is Regular
-- ══════════════════════════════════════════════════════════════════

/-- Every successor aleph ℵ_{n+1} is regular. -/
theorem aleph_succ_regular (n : ℕ) : (Cardinal.aleph (n + 1)).IsRegular :=
  Cardinal.isRegular_aleph_succ n

/-- The diagonal step for any successor aleph ℵ_{n+1}. -/
theorem aleph_succ_diagonal_step (n : ℕ)
    {ι : Type*} (hι : #ι < Cardinal.aleph (n + 1))
    (f : ι → Ordinal) (hf : ∀ i, f i < (Cardinal.aleph (n + 1)).ord) :
    Ordinal.sup f < (Cardinal.aleph (n + 1)).ord :=
  diagonal_step (aleph_succ_regular n) hι f hf

/-- The diagonal argument works at every level of the aleph hierarchy:
    for each n, no set of fewer than ℵ_{n+1} ordinals below ℵ_{n+1}.ord
    can cover all ordinals below ℵ_{n+1}.ord. -/
theorem aleph_hierarchy_diagonal (n : ℕ)
    {ι : Type*} (hι : #ι < Cardinal.aleph (n + 1))
    (f : ι → Ordinal) (hf : ∀ i, f i < (Cardinal.aleph (n + 1)).ord) :
    ∃ β, β < (Cardinal.aleph (n + 1)).ord ∧ ∀ i, f i < β :=
  no_small_surjection (aleph_succ_regular n) hι f hf

-- ══════════════════════════════════════════════════════════════════
-- § 5: Summary
-- ══════════════════════════════════════════════════════════════════

/-- **Main theorem**: The Cantor diagonal argument generalizes to all regular
    cardinals. For regular κ and any <κ-sized family of ordinals < κ.ord,
    there exists an ordinal < κ.ord not covered by the family. -/
theorem cantor_diagonal_generalized (κ : Cardinal) (hκ : κ.IsRegular) :
    ∀ {ι : Type*}, #ι < κ →
    ∀ f : ι → Ordinal, (∀ i, f i < κ.ord) →
    ∃ β : Ordinal, β < κ.ord ∧ ∀ i, f i < β :=
  fun hι f hf => no_small_surjection hκ hι f hf

end CantorDiagRegular
