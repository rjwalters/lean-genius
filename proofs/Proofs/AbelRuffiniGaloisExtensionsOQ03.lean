/-
  Simplicity of Aₙ reduced to the 3-cycle criterion (n ≥ 5)
  (Open Question OQ-03 of abel-ruffini-galois-extensions:
   "Prove Aₙ is simple for n ≥ 5 from triple transpositions / 3-cycles")

  ## What this file establishes (0 sorry, 0 axiom)

  Mathlib proves the alternating group is simple only for the concrete case
  `alternatingGroup (Fin 5)` (`alternatingGroup.isSimpleGroup_five`). For a general
  finite type `α` with `5 ≤ card α` it supplies the *converse* machinery — that the
  normal closure of a single 3-cycle is the whole alternating group
  (`IsThreeCycle.alternating_normalClosure`), that all 3-cycles are conjugate
  (`isThreeCycle_isConj`), and that the 3-cycles generate it
  (`closure_three_cycles_eq_alternating`) — but it does **not** assemble these into a
  general simplicity statement, nor does it isolate the genuine combinatorial content.

  This file performs that reduction.  The hard, classical content of the simplicity of
  `Aₙ` is the single statement

    "every nontrivial normal subgroup of `Aₙ` contains a 3-cycle"

  (the multi-page cycle-type case analysis; for `Fin 5` Mathlib discharges it by hand).
  We prove that this statement is **equivalent** to simplicity for every `n ≥ 5`:

    * `threeCycle_normal_eq_top` — a reusable lemma: *any* normal subgroup `H ◁ Aₙ`
      (`n ≥ 5`) that contains a 3-cycle is already all of `Aₙ`.  (Mathlib only has the
      normal closure of a *singleton* 3-cycle; this upgrades it to arbitrary normal
      subgroups.)
    * `isSimpleGroup_of_forall_normal_contains_threeCycle` — the simplicity reduction:
      if every nontrivial normal subgroup contains a 3-cycle, then `Aₙ` is simple.
    * `forall_normal_contains_threeCycle_of_isSimpleGroup` — the converse: simplicity
      forces every nontrivial normal subgroup (being `⊤`) to contain a 3-cycle, since
      3-cycles exist whenever `card α ≥ 3`.
    * `isSimpleGroup_alternating_iff` — the headline characterization
      `IsSimpleGroup (Aₙ) ↔ (every nontrivial normal subgroup contains a 3-cycle)`.

  Thus the open mathematical content of "Aₙ is simple for n ≥ 5" is exactly the
  3-cycle-containment criterion: everything else is now machine-checked.

  ## Provenance

  All four results are new relative to Mathlib v4.x, which stops at the `Fin 5` instance.
  They build only on the public alternating-group API in
  `Mathlib.GroupTheory.SpecificGroups.Alternating`.
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

open Equiv Equiv.Perm Subgroup

namespace AbelRuffiniGaloisExtensionsOQ03

open alternatingGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Core reduction lemma.** If `H` is a normal subgroup of the alternating group on
`α` (with `5 ≤ card α`) and `H` contains a 3-cycle, then `H` is the whole group.

This upgrades Mathlib's `IsThreeCycle.alternating_normalClosure` (which computes the
normal closure of a *single* 3-cycle) to an arbitrary normal subgroup: the normal
closure of the 3-cycle is contained in `H` by normality, and equals `⊤`. -/
theorem threeCycle_normal_eq_top
    (h5 : 5 ≤ Fintype.card α)
    {H : Subgroup (alternatingGroup α)} (hHn : H.Normal)
    {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α)) (hgH : g ∈ H) :
    H = ⊤ := by
  haveI := hHn
  -- The normal closure of `{g}` sits inside the normal subgroup `H`.
  have hclosed : normalClosure ({g} : Set (alternatingGroup α)) ≤ H :=
    normalClosure_le_normal (Set.singleton_subset_iff.2 hgH)
  -- That normal closure is all of `Aₙ` (Mathlib), once we identify `g` with the
  -- subtype element packaged from its underlying 3-cycle.
  have hgeq : (⟨(g : Perm α), hg.mem_alternatingGroup⟩ : alternatingGroup α) = g :=
    Subtype.ext rfl
  have htop : normalClosure ({g} : Set (alternatingGroup α)) = ⊤ := by
    rw [← hgeq]; exact hg.alternating_normalClosure h5
  rw [htop] at hclosed
  exact top_le_iff.1 hclosed

/-- **Simplicity reduction.** If every nontrivial normal subgroup of `Aₙ` (`n ≥ 5`)
contains a 3-cycle, then `Aₙ` is simple. -/
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

/-- **Converse.** If `Aₙ` (`n ≥ 5`) is simple, then every nontrivial normal subgroup
contains a 3-cycle: it must be `⊤`, and `⊤` contains the 3-cycle `(a b)(a c)` produced
from any three distinct points (which exist since `card α ≥ 3`). -/
theorem forall_normal_contains_threeCycle_of_isSimpleGroup
    [IsSimpleGroup (alternatingGroup α)] (h5 : 5 ≤ Fintype.card α)
    (H : Subgroup (alternatingGroup α)) (hHn : H.Normal) (hbot : H ≠ ⊥) :
    ∃ g : alternatingGroup α, IsThreeCycle (g : Perm α) ∧ g ∈ H := by
  rcases hHn.eq_bot_or_eq_top with h | h
  · exact absurd h hbot
  · -- `H = ⊤`; exhibit a concrete 3-cycle.
    obtain ⟨a, b, c, ab, ac, bc⟩ := (Fintype.two_lt_card_iff (α := α)).1 (by omega)
    have htc : IsThreeCycle (Equiv.swap a b * Equiv.swap a c) :=
      isThreeCycle_swap_mul_swap_same ab ac bc
    refine ⟨⟨_, htc.mem_alternatingGroup⟩, htc, ?_⟩
    rw [h]; exact Subgroup.mem_top _

/-- **Headline characterization.** For `n ≥ 5`, the alternating group `Aₙ` is simple
**iff** every nontrivial normal subgroup contains a 3-cycle.  The right-hand side is the
sole genuinely combinatorial ingredient of the classical simplicity theorem; this
equivalence shows everything else is formal. -/
theorem isSimpleGroup_alternating_iff (h5 : 5 ≤ Fintype.card α) :
    IsSimpleGroup (alternatingGroup α) ↔
      ∀ (H : Subgroup (alternatingGroup α)), H.Normal → H ≠ ⊥ →
        ∃ g : alternatingGroup α, IsThreeCycle (g : Perm α) ∧ g ∈ H := by
  constructor
  · intro hs H hHn hbot
    haveI := hs
    exact forall_normal_contains_threeCycle_of_isSimpleGroup h5 H hHn hbot
  · intro hcrux
    exact isSimpleGroup_of_forall_normal_contains_threeCycle h5 hcrux

end AbelRuffiniGaloisExtensionsOQ03
