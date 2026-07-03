/-
  Unconditional simplicity of Aₙ (n ≥ 5), reduced to a single classical lemma
  (Open Question OQ-03-OQ-01 of abel-ruffini-galois-extensions).

  ## STATUS: WORK IN PROGRESS (1 sorry — the classical combinatorial core)

  This file is *not* a verified gallery entry.  It isolates and states the single
  remaining hard lemma needed to upgrade the parent file's *conditional* reduction
  (`AbelRuffiniGaloisExtensionsOQ03`) into an **unconditional** proof that the
  alternating group `Aₙ` is simple for every `n ≥ 5`, generalizing Mathlib's
  `alternatingGroup.isSimpleGroup_five` (which covers only `Fin 5`).

  ## What the parent already established (0 sorry)

  `AbelRuffiniGaloisExtensionsOQ03` proved the *formal* half of the classical
  theorem:

    `isSimpleGroup_of_forall_normal_contains_threeCycle`
      (5 ≤ card α) → (every nontrivial normal H ⊴ Aₙ contains a 3-cycle)
                   → IsSimpleGroup (Aₙ)

  together with the converse and the headline `iff`.  The genuinely combinatorial
  content of the simplicity theorem was thereby isolated to the single statement

      **every nontrivial normal subgroup of `Aₙ` (n ≥ 5) contains a 3-cycle.**

  ## What this file adds

  * `exists_mem_isThreeCycle_of_normal` — the isolated classical lemma, currently a
    `sorry`.  This is the *only* open content; it is a KNOWN result (not an open
    conjecture), so it is a candidate for Aristotle / a dedicated formalization
    session.
  * `isSimpleGroup_alternating` — the unconditional simplicity theorem for all
    `n ≥ 5`, obtained by feeding the lemma into the parent's reduction.  This body
    is complete; it inherits exactly one `sorry` transitively.

  ## Proof plan for `exists_mem_isThreeCycle_of_normal`
     (Jordan's minimal-support / commutator argument)

  Let `H ⊴ Aₙ` be normal with `H ≠ ⊥`, `n = card α ≥ 5`.

  1. Since `alternatingGroup α` is finite and `H ≠ ⊥`, the set
     `{ x ∈ H | x ≠ 1 }` is a nonempty finite set.  Choose `σ` in it minimizing
     `(σ : Perm α).support.card`  (`Finset.exists_min_image`).

  2. `σ ≠ 1` and `σ` is even, so `σ` moves at least 3 points:
     `#σ.support ≥ 3`  (an even permutation cannot move exactly 1 or 2 points;
     `sum_cycleType` + `two_le_of_mem_cycleType`).

  3. **Claim: `σ` is a 3-cycle.**  If `#σ.support = 3` then `σ.IsThreeCycle`
     directly (`card_support_eq_three_iff`), and `σ ∈ H`, so we are done.

  4. Otherwise `#σ.support ≥ 4`; derive a contradiction with minimality by
     exhibiting a nonidentity element of `H` supported on strictly fewer points.
     Split on the cycle type of `σ`:

     * **(A) `σ` has a cycle of length `≥ 3`.**  Write that cycle as `(a b c …)`.
       Since `#σ.support ≥ 5` in this branch (an even perm with a ≥3-cycle moving
       ≥4 points moves ≥5), pick two further moved points `d, e` and set
       `τ = (c d e)` (a 3-cycle, hence in `Aₙ`).  The commutator
       `ρ = τ σ τ⁻¹ σ⁻¹` lies in `H` (normality: `τ σ τ⁻¹ ∈ H`, `σ⁻¹ ∈ H`), is
       `≠ 1`, and satisfies `ρ.support ⊆ σ.support ∪ τ • σ.support` with the
       count strictly below `#σ.support` — contradiction.

     * **(B) `σ` is a product of disjoint transpositions** (all cycle lengths 2),
       necessarily `≥ 2` of them (evenness).  With `σ = (a b)(c d) …` choose a 5th
       point `e` (exists, `n ≥ 5`) and `τ = (c d e)`.  The commutator
       `ρ = τ σ τ⁻¹ σ⁻¹ ∈ H` is a 3-cycle or moves strictly fewer points,
       contradicting minimality (or finishing directly).

  ## Mathlib API this plan relies on (all confirmed present)

  * `Equiv.Perm.support_mul_le`, `Equiv.Perm.support_conj`,
    `Equiv.Perm.card_support_conj`      — support of products / conjugates
  * `Equiv.Perm.sum_cycleType`, `Equiv.Perm.two_le_of_mem_cycleType`
  * `card_support_eq_three_iff`          — 3 moved points ⇔ 3-cycle
  * `Equiv.Perm.isThreeCycle_swap_mul_swap_same`
  * `Subgroup.Normal.conj_mem`           — commutator membership
  * `Finset.exists_min_image`            — minimal-support selection

  ## Size / buildability assessment

  The strict-support-decrease counting in step 4 is the crux (≈300–800 lines,
  comparable to Mathlib's `Fin 5` casework but for arbitrary `α`).  Classified
  HARD, not OPEN.  Best executed via Aristotle (currently unavailable) or a
  dedicated session with a working build loop.
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

open Equiv Equiv.Perm Subgroup

namespace AbelRuffiniGaloisExtensionsOQ03OQ01

open alternatingGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The formal reduction (re-derived, 0 sorry)

These two lemmas reproduce the verified reduction from
`AbelRuffiniGaloisExtensionsOQ03`, inlined here so that this file depends only on
Mathlib (allowing single-file elaboration).  They contain no `sorry`; only
`exists_mem_isThreeCycle_of_normal` below does. -/

/-- If a normal subgroup `H ⊴ Aₙ` (`n ≥ 5`) contains a 3-cycle, then `H = ⊤`.
Upgrades Mathlib's `IsThreeCycle.alternating_normalClosure` (normal closure of a
single 3-cycle) to an arbitrary normal subgroup. -/
theorem threeCycle_normal_eq_top
    (h5 : 5 ≤ Fintype.card α)
    {H : Subgroup (alternatingGroup α)} (hHn : H.Normal)
    {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α)) (hgH : g ∈ H) :
    H = ⊤ := by
  haveI := hHn
  have hclosed : normalClosure ({g} : Set (alternatingGroup α)) ≤ H :=
    normalClosure_le_normal (Set.singleton_subset_iff.2 hgH)
  have hgeq : (⟨(g : Perm α), hg.mem_alternatingGroup⟩ : alternatingGroup α) = g :=
    Subtype.ext rfl
  have htop : normalClosure ({g} : Set (alternatingGroup α)) = ⊤ := by
    rw [← hgeq]; exact hg.alternating_normalClosure h5
  rw [htop] at hclosed
  exact top_le_iff.1 hclosed

/-- If every nontrivial normal subgroup of `Aₙ` (`n ≥ 5`) contains a 3-cycle, then
`Aₙ` is simple. -/
theorem isSimpleGroup_of_forall_normal_contains_threeCycle
    (h5 : 5 ≤ Fintype.card α)
    (hcrux : ∀ (H : Subgroup (alternatingGroup α)), H.Normal → H ≠ ⊥ →
        ∃ g : alternatingGroup α, IsThreeCycle (g : Perm α) ∧ g ∈ H) :
    IsSimpleGroup (alternatingGroup α) := by
  haveI : Nontrivial (alternatingGroup α) := nontrivial_of_three_le_card (by omega)
  refine ⟨fun H hHn => ?_⟩
  rcases eq_or_ne H ⊥ with h | h
  · exact Or.inl h
  · obtain ⟨g, hg, hgH⟩ := hcrux H hHn h
    exact Or.inr (threeCycle_normal_eq_top h5 hHn hg hgH)

/-! ### The classical combinatorial core (WIP) -/

/-- **The classical combinatorial core (KNOWN result, WIP).** Every nontrivial
normal subgroup of the alternating group on `α` (with `5 ≤ card α`) contains a
3-cycle.  This is the sole open ingredient of the simplicity theorem; see the file
header for the intended minimal-support / commutator proof plan.

Currently a `sorry`: HARD, not OPEN. -/
theorem exists_mem_isThreeCycle_of_normal
    (h5 : 5 ≤ Fintype.card α)
    (H : Subgroup (alternatingGroup α)) (hHn : H.Normal) (hbot : H ≠ ⊥) :
    ∃ g : alternatingGroup α, IsThreeCycle (g : Equiv.Perm α) ∧ g ∈ H := by
  sorry

/-- **Unconditional simplicity of `Aₙ` for `n ≥ 5`.** Feeds the classical 3-cycle
lemma into the parent file's formal reduction
(`isSimpleGroup_of_forall_normal_contains_threeCycle`).  The body is complete; the
result inherits exactly one `sorry`, namely `exists_mem_isThreeCycle_of_normal`.

When that lemma is discharged, this generalizes Mathlib's `Fin 5`-only
`alternatingGroup.isSimpleGroup_five` to every finite `α` with `5 ≤ card α`. -/
theorem isSimpleGroup_alternating (h5 : 5 ≤ Fintype.card α) :
    IsSimpleGroup (alternatingGroup α) :=
  isSimpleGroup_of_forall_normal_contains_threeCycle
    h5 (fun H hHn hbot => exists_mem_isThreeCycle_of_normal h5 H hHn hbot)

end AbelRuffiniGaloisExtensionsOQ03OQ01
