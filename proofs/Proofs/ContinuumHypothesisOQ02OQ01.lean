import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

/-
# De-axiomatizing the Bounding Number Lower Bound: ℵ₁ ≤ 𝔟

## Open Question: continuum-hypothesis-oq-02-oq-01

The companion entry `continuum-hypothesis-oq-02` ("What Is the 'True' Size of the
Continuum?") develops the ZFC constraints on 2^ℵ₀:

  * **Cantor**:  ℵ₁ ≤ 2^ℵ₀
  * **König**:   cf(2^ℵ₀) > ℵ₀   (the cofinality constraint)

and introduces the cardinal characteristics 𝔟 (bounding number) and 𝔡
(dominating number), with the ZFC chain

  ℵ₁ ≤ 𝔟 ≤ 𝔡 ≤ 2^ℵ₀.

In that file the lower bound **ℵ₁ ≤ 𝔟** was *axiomatized*
(`axiom bounding_number_uncountable`), with the docstring noting that "the formal
proof requires constructing the diagonal function and showing it eventually
dominates each element."

**This entry discharges that axiom.** We give the classical Hausdorff
diagonalization argument from Mathlib alone:

> No countable family of functions ℕ → ℕ is unbounded in the eventual-domination
> preorder ≤*, because a countable family {f₀, f₁, …} is dominated by its
> diagonal g(k) = max_{i ≤ k} fᵢ(k) + 1.

Hence every unbounded family is *uncountable*, so 𝔟 ≥ ℵ₁.

We also record the **general König cofinality constraint** in its sharp form,
generalizing the special case κ = ℵ₀ proved in the parent:

  for every infinite cardinal κ,   κ < cf(2^κ).

## Key Results

* `general_konig_cofinality` — for all κ ≥ ℵ₀, κ < cf(2^κ)   (sharp König constraint)
* `diagonal_dominates`       — the diagonal g eventually dominates each member of
                               a countably-enumerated family
* `unbounded_uncountable`    — an unbounded family has cardinality ≥ ℵ₁
* `bounding_number_uncountable` — ℵ₁ ≤ 𝔟 (the de-axiomatized result)

All statements are over `Cardinal.{0}` and use only Mathlib; no project-local
axioms are introduced.

## Mathlib Dependencies

* `Cardinal.lt_cof_power`            — König: ℵ₀ ≤ a → 1 < b → a < cf(bᵃ)
* `Cardinal.countable_iff_lt_aleph_one` — s.Countable ↔ #s < ℵ₁
* `Set.Countable.exists_eq_range`    — a nonempty countable set is a range ℕ → α
* `Cardinal.cantor`                  — Cantor: κ < 2^κ
* `Cardinal.succ_aleph0`             — succ ℵ₀ = ℵ₁
* `Finset.le_sup`                    — a ∈ s → f a ≤ s.sup f
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace ContinuumHypothesisOQ02OQ01

open Cardinal

-- ============================================================
-- PART 0: Eventual domination and the cardinal characteristics
--          (definitions inlined to match continuum-hypothesis-oq-02)
-- ============================================================

/-- The eventual-domination preorder: `f ≤* g` means `f n ≤ g n` for all but
    finitely many `n`. -/
def eventuallyDominates (f g : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≤ g n

/-- A family `F` is **unbounded** if no single function eventually dominates
    every member of `F`. -/
def IsUnbounded (F : Set (ℕ → ℕ)) : Prop :=
  ∀ g : ℕ → ℕ, ∃ f ∈ F, ¬eventuallyDominates f g

/-- The **bounding number** 𝔟: the least cardinality of an unbounded family in
    `(ℕ → ℕ, ≤*)`. (The `else` branch uses the continuum `2^ℵ₀`, exactly as in
    `continuum-hypothesis-oq-02`, so that `boundingNumber ≤ 2^ℵ₀`.) -/
noncomputable def boundingNumber : Cardinal.{0} :=
  ⨅ (F : Set (ℕ → ℕ)), if IsUnbounded F then Cardinal.mk F else (2 ^ ℵ₀ : Cardinal.{0})

-- ============================================================
-- PART 1: The general König cofinality constraint (sharp form)
-- ============================================================

/-- **General König cofinality constraint.** For every infinite cardinal `κ`,
    the cofinality of `2^κ` exceeds `κ`:

      κ < cf(2^κ).

    The parent entry proves only the case `κ = ℵ₀` (cf(2^ℵ₀) > ℵ₀). This is the
    full-strength statement: it follows directly from `Cardinal.lt_cof_power`,
    König's theorem in Mathlib. In particular `2^κ` is never a cardinal of
    cofinality ≤ κ — e.g. it is never `ℵ_{κ + ω}`-type singular. -/
theorem general_konig_cofinality {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) :
    κ < (2 ^ κ : Cardinal.{0}).ord.cof :=
  Cardinal.lt_cof_power hκ (by norm_num)

/-- The parent's special case recovered: cf(2^ℵ₀) > ℵ₀. -/
theorem konig_cofinality_aleph0 :
    (ℵ₀ : Cardinal.{0}) < (2 ^ (ℵ₀ : Cardinal.{0})).ord.cof :=
  general_konig_cofinality le_rfl

-- ============================================================
-- PART 2: The diagonalization — countable families are bounded
-- ============================================================

/-- The **diagonal** of an enumerated family `e : ℕ → (ℕ → ℕ)`:

      g(k) = (max over i ≤ k of e i k) + 1.

    It eventually dominates every member `e j`: for all `k ≥ j` we have
    `e j k ≤ g k`, because `j ∈ {0, …, k}` so `e j k ≤ max_{i ≤ k} e i k < g k`. -/
theorem diagonal_dominates (e : ℕ → ℕ → ℕ) (j : ℕ) :
    eventuallyDominates (e j)
      (fun k => (Finset.range (k + 1)).sup (fun i => e i k) + 1) := by
  refine ⟨j, fun k hk => ?_⟩
  have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hle : e j k ≤ (Finset.range (k + 1)).sup (fun i => e i k) := Finset.le_sup hmem
  omega

/-- **An unbounded family is uncountable: ℵ₁ ≤ #F.**

    Proof (Hausdorff diagonalization). Suppose `F` were countable. If `F = ∅`
    then `F` is not unbounded (witness `g = 0`: there is no member). Otherwise
    write `F = range e` for some enumeration `e : ℕ → (ℕ → ℕ)`. The diagonal
    `g(k) = max_{i ≤ k} e i k + 1` eventually dominates every `e j`
    (`diagonal_dominates`), so no member of `F` escapes `g`, contradicting
    `IsUnbounded F` applied to `g`. Hence `F` is uncountable, i.e.
    `¬ (#F < ℵ₁)`, i.e. `ℵ₁ ≤ #F`. -/
theorem unbounded_uncountable {F : Set (ℕ → ℕ)} (h : IsUnbounded F) :
    ℵ₁ ≤ Cardinal.mk F := by
  -- ℵ₁ ≤ #F  ↔  ¬ (#F < ℵ₁)  ↔  ¬ F.Countable
  rw [← not_lt, ← Cardinal.countable_iff_lt_aleph_one]
  intro hcount
  rcases Set.eq_empty_or_nonempty F with hE | hne
  · -- empty F is not unbounded: there is no member to witness against g = 0
    obtain ⟨f, hf, _⟩ := h (fun _ => 0)
    rw [hE] at hf
    exact (Set.not_mem_empty f) hf
  · -- write F = range e and diagonalize
    obtain ⟨e, he⟩ := hcount.exists_eq_range hne
    obtain ⟨f, hfF, hfnd⟩ :=
      h (fun k => (Finset.range (k + 1)).sup (fun i => e i k) + 1)
    rw [he] at hfF
    obtain ⟨j, rfl⟩ := hfF
    exact hfnd (diagonal_dominates e j)

-- ============================================================
-- PART 3: The bounding number is uncountable (de-axiomatized)
-- ============================================================

/-- ℵ₁ ≤ 2^ℵ₀ (Cantor): needed for the non-unbounded branch of the infimum. -/
theorem aleph_one_le_two_pow_aleph0 : ℵ₁ ≤ (2 ^ ℵ₀ : Cardinal.{0}) := by
  rw [← Cardinal.succ_aleph0]
  exact Order.succ_le_of_lt (Cardinal.cantor ℵ₀)

/-- **ℵ₁ ≤ 𝔟 — the de-axiomatized bounding-number lower bound.**

    This is the result `continuum-hypothesis-oq-02` declared as
    `axiom bounding_number_uncountable`. We prove it from the diagonalization:
    the infimum `𝔟 = ⨅_F (if IsUnbounded F then #F else 2^ℵ₀)` is bounded below
    by ℵ₁ term-by-term —
      * unbounded `F`: `ℵ₁ ≤ #F` by `unbounded_uncountable`;
      * non-unbounded `F`: `ℵ₁ ≤ 2^ℵ₀` by Cantor. -/
theorem bounding_number_uncountable : ℵ₁ ≤ boundingNumber := by
  unfold boundingNumber
  apply le_ciInf
  intro F
  by_cases h : IsUnbounded F
  · simp only [h, ite_true]
    exact unbounded_uncountable h
  · simp only [h, ite_false]
    exact aleph_one_le_two_pow_aleph0

/-- 𝔟 is uncountable in the strict sense ℵ₀ < 𝔟 (immediate corollary). -/
theorem aleph0_lt_boundingNumber : ℵ₀ < boundingNumber :=
  lt_of_lt_of_le Cardinal.aleph0_lt_aleph_one bounding_number_uncountable

end ContinuumHypothesisOQ02OQ01

-- Export key theorems
#check @ContinuumHypothesisOQ02OQ01.general_konig_cofinality
#check @ContinuumHypothesisOQ02OQ01.unbounded_uncountable
#check @ContinuumHypothesisOQ02OQ01.bounding_number_uncountable
