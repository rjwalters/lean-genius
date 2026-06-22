/-
# The Aₐ ↔ Sₐ Solvability Bridge: the Sign Extension is Transparent to Solvability
  (Abel-Ruffini OQ-04-OQ-02-OQ-02-OQ-08)

Open question spawned from `AbelRuffiniOQ04OQ02OQ02` (Aₙ solvable iff n ≤ 4):

  "The alternating classification (Aₙ solvable iff n ≤ 4) and the symmetric
   classification (Sₙ solvable iff n ≤ 4) share a threshold. Is that coincidence,
   or is there a structural reason — independent of the threshold and of the
   choice of underlying set — forcing the two to agree?"

## Answer: a single equivalence, for an ARBITRARY finite set.

For **any** finite type `α`, the alternating group `Aα` is solvable *iff* the full
symmetric group `Sα` is solvable:

  **Bridge:   IsSolvable (alternatingGroup α)  ↔  IsSolvable (Perm α).**

The sign extension `1 → Aα → Sα → {±1} → 1` is completely transparent to
solvability, in both directions:

  * (→)  If the kernel `Aα` is solvable then, because the quotient
         `Sα / Aα ≅ ℤ/2` is abelian (hence solvable), the middle group `Sα` is
         solvable. Concretely `Aα.subtype : Aα →* Sα` has image `Aα`, and
         `Perm.sign : Sα →* ℤˣ` has kernel exactly `Aα`
         (`mem_alternatingGroup`), so `ker sign ≤ range subtype` and
         `solvable_of_ker_le_range` applies.
  * (←)  `Aα` is a *subgroup* of `Sα`, and subgroups of solvable groups are
         solvable (`subgroup_solvable_of_solvable`).

This is the structural fact the two sibling classifications only recorded
numerically. It holds with no cardinality hypothesis at all, so the threshold
agreement at `n = 5` is *forced*, not coincidental: specialising the bridge to
`α = Fin n` makes the parent's `alternating_solvable_iff` (Aₙ solvable ↔ n ≤ 4)
and the sibling `AbelRuffiniOQ04OQ02` classification (Sₙ solvable ↔ n ≤ 4)
*literally the same theorem* viewed through the sign sequence.

| n  | Aₙ solvable | Sₙ solvable | bridge says |
|----|-------------|-------------|-------------|
| ≤4 | yes         | yes         | agree ✓     |
| ≥5 | no          | no          | agree ✓     |

The transition at `n = 5` is the algebraic heart of Abel–Ruffini: a general
quintic has Galois group `S₅`, non-solvable because its alternating subgroup
`A₅` is simple and non-abelian — hence no solution in radicals.

Parent:  `AbelRuffiniOQ04OQ02OQ02.lean`  (Aₙ solvable iff n ≤ 4)
Sibling: `AbelRuffiniOQ04OQ02.lean`       (Sₙ solvable iff n ≤ 4)
Sibling: `AbelRuffiniOQ04OQ02OQ02OQ06.lean` (derived-length gap A₄ vs A₅)

References:
- Galois (1832); Jordan, *Traité des substitutions* (1870)
- Hungerford, *Algebra* (1974), §II.7;  Lang, *Algebra* (3rd ed.), §I.8
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02

set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08

open AbelRuffiniOQ04OQ02OQ02

-- ============================================================
-- PART 1: The Sign Exact Sequence, Both Directions (any finite α)
-- ============================================================

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Kernel direction (general `α`).** If the alternating subgroup `Aα` is
solvable, then the full symmetric group `Sα` is solvable.

This is the substantive half: it uses the short exact sequence
`1 → Aα → Sα → {±1} → 1`. The map `Aα.subtype : Aα →* Sα` has image `Aα`, and
`Perm.sign : Sα →* ℤˣ` has kernel exactly `Aα`, so `ker sign ≤ range subtype`.
With kernel and quotient both solvable, `solvable_of_ker_le_range` delivers `Sα`. -/
theorem sym_solvable_of_alternating_solvable
    (h : IsSolvable (alternatingGroup α)) : IsSolvable (Perm α) := by
  apply solvable_of_ker_le_range (alternatingGroup α).subtype Perm.sign
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  exact ⟨⟨x, Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩

/-- **Subgroup direction (general `α`).** If the symmetric group `Sα` is solvable,
then its alternating subgroup `Aα` is solvable, because subgroups of solvable
groups are solvable (`subgroup_solvable_of_solvable`). -/
theorem alternating_solvable_of_sym_solvable
    (h : IsSolvable (Perm α)) : IsSolvable (alternatingGroup α) := by
  haveI := h
  infer_instance

-- ============================================================
-- PART 2: The Solvability Bridge (any finite α)
-- ============================================================

/-- **Solvability bridge (any finite `α`).** The alternating group `Aα` is
solvable *iff* the symmetric group `Sα` is solvable. The index-2 sign extension
is completely transparent to solvability — passing to the abelian quotient `ℤ/2`
neither creates nor destroys it — with no hypothesis on the cardinality of `α`. -/
theorem alternating_solvable_iff_sym_solvable (α : Type*) [DecidableEq α] [Fintype α] :
    IsSolvable (alternatingGroup α) ↔ IsSolvable (Perm α) :=
  ⟨sym_solvable_of_alternating_solvable, alternating_solvable_of_sym_solvable⟩

/-- Contrapositive form, both directions: `Sα` is non-solvable iff `Aα` is. -/
theorem sym_not_solvable_iff_alternating_not_solvable (α : Type*) [DecidableEq α] [Fintype α] :
    ¬IsSolvable (Perm α) ↔ ¬IsSolvable (alternatingGroup α) :=
  not_congr (alternating_solvable_iff_sym_solvable α).symm

-- ============================================================
-- PART 3: Specialisation to Fin n — the threshold agreement is forced
-- ============================================================

/-- Specialising the bridge to `α = Fin n`: `Aₙ` solvable iff `Sₙ` solvable. -/
theorem alternating_fin_solvable_iff_sym_fin_solvable (n : ℕ) :
    IsSolvable (alternatingGroup (Fin n)) ↔ IsSolvable (Perm (Fin n)) :=
  alternating_solvable_iff_sym_solvable (Fin n)

/-- **The symmetric classification is the alternating one, via the bridge.**
Combining the bridge with the parent's `alternating_solvable_iff` recovers
`Sₙ` solvable ↔ `n ≤ 4` (matching the sibling entry `AbelRuffiniOQ04OQ02`'s
`solvable_iff_le_four`) — but now *derived* from the alternating classification
rather than proved independently. The two thresholds are one theorem. -/
theorem sym_solvable_iff (n : ℕ) : IsSolvable (Perm (Fin n)) ↔ n ≤ 4 := by
  rw [← alternating_fin_solvable_iff_sym_fin_solvable, alternating_solvable_iff]

/-- The full chain at a glance: `Sₙ` solvable ↔ `Aₙ` solvable ↔ `n ≤ 4`. -/
theorem solvability_trichotomy (n : ℕ) :
    (IsSolvable (Perm (Fin n)) ↔ IsSolvable (alternatingGroup (Fin n))) ∧
      (IsSolvable (Perm (Fin n)) ↔ n ≤ 4) :=
  ⟨(alternating_fin_solvable_iff_sym_fin_solvable n).symm, sym_solvable_iff n⟩

-- ============================================================
-- PART 4: Corollaries and the joint sharp threshold
-- ============================================================

/-- For `n ≤ 4`, `Sₙ` is solvable (transport the parent's `Aₙ` solvability). -/
theorem sym_solvable_of_le_four {n : ℕ} (hn : n ≤ 4) : IsSolvable (Perm (Fin n)) :=
  sym_solvable_of_alternating_solvable (alternating_solvable_of_le_four hn)

/-- For `n ≥ 5`, `Sₙ` is NOT solvable: the bridge moves the parent's
`an_not_solvable_of_ge_five` across the sign sequence. -/
theorem sym_not_solvable_of_ge_five {n : ℕ} (hn : 5 ≤ n) :
    ¬IsSolvable (Perm (Fin n)) := by
  rw [sym_not_solvable_iff_alternating_not_solvable]
  exact an_not_solvable_of_ge_five hn

/-- S₄ (order 24) is solvable — the largest solvable symmetric group (Ferrari's
quartic formula). -/
theorem s4_solvable : IsSolvable (Perm (Fin 4)) := sym_solvable_of_le_four (le_refl 4)

/-- S₅ (order 120) is NOT solvable — the obstruction to a general quintic formula. -/
theorem s5_not_solvable : ¬IsSolvable (Perm (Fin 5)) := sym_not_solvable_of_ge_five (le_refl 5)

/-- **Joint sharp threshold.** At `n = 4` both A₄ and S₄ are solvable; at `n = 5`
both A₅ and S₅ fail. The bridge forces the two transitions to coincide. -/
theorem joint_sharp_threshold :
    (IsSolvable (alternatingGroup (Fin 4)) ∧ IsSolvable (Perm (Fin 4))) ∧
      (¬IsSolvable (alternatingGroup (Fin 5)) ∧ ¬IsSolvable (Perm (Fin 5))) :=
  ⟨⟨a4_solvable, s4_solvable⟩, ⟨a5_not_solvable, s5_not_solvable⟩⟩

end AbelRuffiniOQ04OQ02OQ02OQ08
