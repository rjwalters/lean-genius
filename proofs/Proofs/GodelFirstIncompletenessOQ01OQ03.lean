import Mathlib

/-!
# Gödel First Incompleteness OQ-01 / OQ-03: (In)dependence of the Five Axioms

## The Open Question (OQ-03 of `godel-first-incompleteness-oq01`)

The parent file `GodelFirstIncompletenessOQ01` proves First Incompleteness from five axioms on
an opaque provability predicate `Provable`, and asks:

> The five axioms are "independent" in the sense that removing any one breaks the proof — but
> are they actually independent as logical assertions? Could any of them be derived from the
> others?

## The answer (and a soundness finding)

We analyze the four substantive axioms, instantiated at the single relevant trio of sentences
`G`, `Prov(⌜G⌝)`, `¬G` (codes `42`, `84`, `43` in the parent's encoding). Writing `P` for the
provability predicate, the parent's axioms restrict to:

* `D1G P`      : `P G → P (Prov ⌜G⌝)`            (D1 at `φ = G`)
* `SelfRef P`  : `P G ↔ ¬ P (Prov ⌜G⌝)`          (meta self-reference)
* `OmegaCons P`: `¬ P G → ¬ P (Prov ⌜G⌝)`        (ω-consistency at `G`)
* `NegGProv P` : `P (¬G) → P (Prov ⌜G⌝)`         (object-level diagonal)

Two results, both surprising for a file advertised as *non-vacuous*:

1. **`core_inconsistency`**: `D1G P`, `SelfRef P`, `OmegaCons P` are **jointly inconsistent**
   for *every* `P`. (D1 forces `PG → PprovG`; self-reference forces `PG → ¬PprovG`, hence `¬PG`;
   but self-reference also turns `¬PG` into `PprovG`, while ω-consistency turns it into `¬PprovG`
   — contradiction.) Consequently the parent's axiom set has **no model**
   (`no_model_of_all_axioms`): its First Incompleteness theorem holds, but *vacuously* — a subtler
   form of the very vacuity (`Provable := fun _ => False`) the parent set out to avoid. The flaw
   is that the **meta-level** equivalence `⊢G ↔ ¬⊢Prov⌜G⌝` was asserted as an axiom; in genuine
   arithmetic only the *object-level* `F ⊢ (G ↔ ¬Prov⌜G⌝)` holds.

2. **`negGProv_derivable`**: the fourth axiom `NegGProv` is **derivable** from `D1G ∧ SelfRef`
   (they already force `P (Prov ⌜G⌝)`), so it is *not* independent.

For the three mutually-inconsistent axioms we show the inconsistency is **minimal**: each is
independent of the other two (a model satisfies the other two but not it). So the honest answer
to OQ-03 is: the axioms are **not** independent — three over-determine into a contradiction and
the fourth is redundant.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`. Stated abstractly over an
arbitrary `P : ℕ → Prop` so nothing imports the parent's (inconsistent) global axioms.
-/

namespace GodelFirstIncompletenessOQ01OQ03

/-- Code of the Gödel sentence `G` (parent: `G = ⟨42⟩`). -/
def gCode : ℕ := 42
/-- Code of `Prov(⌜G⌝)` (parent: `Prov (godelNum G) = ⟨42 * 2⟩`). -/
def provGCode : ℕ := 84
/-- Code of `¬G` (parent: `neg G = ⟨42 + 1⟩`). -/
def negGCode : ℕ := 43

/-- D1 (representability) at `φ = G`: provability of `G` entails provability of `Prov(⌜G⌝)`. -/
def D1G (P : ℕ → Prop) : Prop := P gCode → P provGCode

/-- Meta self-reference: `G` provable iff `Prov(⌜G⌝)` not provable. -/
def SelfRef (P : ℕ → Prop) : Prop := P gCode ↔ ¬ P provGCode

/-- ω-consistency at `G`: if `G` is unprovable, so is `Prov(⌜G⌝)`. -/
def OmegaCons (P : ℕ → Prop) : Prop := ¬ P gCode → ¬ P provGCode

/-- Object-level diagonal: provability of `¬G` entails provability of `Prov(⌜G⌝)`. -/
def NegGProv (P : ℕ → Prop) : Prop := P negGCode → P provGCode

/-!
## Result 1: three of the axioms are jointly inconsistent
-/

/-- **The core inconsistency.** No provability predicate satisfies `D1G`, `SelfRef`, and
    `OmegaCons` simultaneously. -/
theorem core_inconsistency (P : ℕ → Prop)
    (h1 : D1G P) (h2 : SelfRef P) (h3 : OmegaCons P) : False := by
  simp only [D1G, SelfRef, OmegaCons] at h1 h2 h3
  tauto

/-- **The parent's axiom set has no model.** Since three of the four axioms already contradict,
    no `P` satisfies all four. The parent's First Incompleteness theorem is therefore vacuously
    true (it follows from contradictory hypotheses), not genuinely non-vacuous. -/
theorem no_model_of_all_axioms :
    ¬ ∃ P : ℕ → Prop, D1G P ∧ SelfRef P ∧ OmegaCons P ∧ NegGProv P := by
  rintro ⟨P, h1, h2, h3, _⟩
  exact core_inconsistency P h1 h2 h3

/-!
## Result 2: the fourth axiom is derivable (not independent)
-/

/-- **`NegGProv` is derivable from `D1G ∧ SelfRef`.** These two already force `P (Prov ⌜G⌝)`,
    so `NegGProv` (anything → `P (Prov ⌜G⌝)`) holds trivially. The object-level diagonal axiom
    is redundant. -/
theorem negGProv_derivable (P : ℕ → Prop) (h1 : D1G P) (h2 : SelfRef P) : NegGProv P := by
  simp only [D1G, SelfRef, NegGProv] at h1 h2 ⊢
  tauto

/-!
## Result 3: the inconsistency is minimal — each of the three is independent of the other two
-/

/-- `D1G` is independent of `SelfRef ∧ OmegaCons`: a model satisfies the latter two but not `D1G`.
    Witness: only `G` is provable (`P n ↔ n = G`). -/
theorem d1G_independent : ∃ P : ℕ → Prop, SelfRef P ∧ OmegaCons P ∧ ¬ D1G P := by
  refine ⟨fun n => n = gCode, ?_, ?_, ?_⟩ <;>
    simp only [D1G, SelfRef, OmegaCons, gCode, provGCode] <;> decide

/-- `SelfRef` is independent of `D1G ∧ OmegaCons`: a model satisfies the latter two but not
    `SelfRef`. Witness: nothing is provable (`P n ↔ False`). -/
theorem selfRef_independent : ∃ P : ℕ → Prop, D1G P ∧ OmegaCons P ∧ ¬ SelfRef P := by
  refine ⟨fun _ => False, ?_, ?_, ?_⟩ <;>
    simp only [D1G, SelfRef, OmegaCons, gCode, provGCode] <;> decide

/-- `OmegaCons` is independent of `D1G ∧ SelfRef`: a model satisfies the latter two but not
    `OmegaCons`. Witness: only `Prov(⌜G⌝)` is provable (`P n ↔ n = Prov ⌜G⌝`). -/
theorem omegaCons_independent : ∃ P : ℕ → Prop, D1G P ∧ SelfRef P ∧ ¬ OmegaCons P := by
  refine ⟨fun n => n = provGCode, ?_, ?_, ?_⟩ <;>
    simp only [D1G, SelfRef, OmegaCons, gCode, provGCode] <;> decide

end GodelFirstIncompletenessOQ01OQ03

/-!
## Summary

Answering OQ-03 (are the parent's five axioms independent / derivable?):

- `core_inconsistency`: `D1G`, `SelfRef`, `OmegaCons` are jointly inconsistent for every `P`.
- `no_model_of_all_axioms`: hence the parent's axiom set has no model — First Incompleteness
  holds there only vacuously (a subtler vacuity than `Provable := fun _ => False`). Root cause:
  the **meta-level** self-reference `⊢G ↔ ¬⊢Prov⌜G⌝` was taken as an axiom, whereas only the
  object-level `F ⊢ (G ↔ ¬Prov⌜G⌝)` is legitimate.
- `negGProv_derivable`: the object-level diagonal axiom is derivable from `D1G ∧ SelfRef`, so it
  is redundant — not independent.
- `d1G_independent`, `selfRef_independent`, `omegaCons_independent`: the three contradictory
  axioms form a *minimal* inconsistent set; each is independent of the other two.

So the axioms are **not** independent: three over-determine into a contradiction, and the fourth
is redundant.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
