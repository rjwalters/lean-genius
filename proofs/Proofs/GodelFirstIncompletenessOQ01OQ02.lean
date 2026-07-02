import Mathlib

/-!
# Gödel First Incompleteness OQ-01 / OQ-02: A Consistent Repair — Incompleteness from a Satisfiable Axiom Set

## The Open Question (OQ-02 of `godel-first-incompleteness-oq01`)

The parent file `GodelFirstIncompletenessOQ01` derives First Incompleteness from five axioms on an
opaque provability predicate `Provable`.  The sibling analysis `…OQ01OQ03` then discovered a flaw:
three of those axioms are **jointly inconsistent for every `P`**, so the parent's axiom set has
**no model** and its First Incompleteness theorem holds only *vacuously* (from contradictory
hypotheses) — a subtler cousin of the `Provable := fun _ => False` vacuity the parent set out to
avoid.  The root cause diagnosed there: the **meta-level** self-reference `⊢G ↔ ¬⊢Prov⌜G⌝` was
taken as an axiom, whereas only the **object-level** fixed point `F ⊢ (G ↔ ¬Prov⌜G⌝)` is legitimate.

> **OQ-02.**  Is there a *consistent* (model-having) axiom set on the trio `G`, `Prov(⌜G⌝)`, `¬G`
> from which First Incompleteness follows **non-vacuously** — i.e. the undecidability of `G` is a
> genuine consequence of *satisfiable* hypotheses, not of a contradiction?

## The answer: yes — replace the meta self-reference by the object-level diagonal clauses

Working, like OQ-03, abstractly over an arbitrary `P : ℕ → Prop` on the four codes
`G = 42`, `Prov(⌜G⌝) = 84`, `¬G = 43`, `¬Prov(⌜G⌝) = 85`, we take the five clauses that Gödel's
proof *actually uses* — none of them the illegitimate meta equivalence:

* `D1G P`      : `P G → P provG`         (Σ₁-completeness / derivability D1 at `φ = G`)
* `FixG P`     : `P G → P negProvG`      (object-level fixed point `F ⊢ (G → ¬Prov⌜G⌝)`)
* `Consistent P`: `¬ (P provG ∧ P negProvG)`  (consistency: `F` proves no sentence and its negation)
* `NegGProv P` : `P negG → P provG`      (object-level fixed point `F ⊢ (¬G → Prov⌜G⌝)`)
* `OmegaCons P`: `¬ P G → ¬ P provG`     (ω-consistency at `G`)

From these we prove, **for every `P`**:

* `godel_not_provable`      : `¬ P G`          (the consistency half — needs `D1G`, `FixG`, `Consistent`)
* `neg_godel_not_provable`  : `¬ P negG`       (the ω-consistency half — adds `NegGProv`, `OmegaCons`)
* `first_incompleteness`    : `¬ P G ∧ ¬ P negG`  (`G` is undecidable)

and, crucially, that the hypotheses are **satisfiable**:

* `has_model`               : `∃ P, D1G P ∧ FixG P ∧ Consistent P ∧ NegGProv P ∧ OmegaCons P`
* `has_nontrivial_model`    : the same, with a `P` that is **not** identically `False`
                              (witness: `¬Prov⌜G⌝` is provable) — so incompleteness here is not the
                              `Provable := fun _ => False` cheat.

Hence First Incompleteness follows from a *consistent* theory: this is the honest, non-vacuous
statement the parent aimed for, obtained by exactly the repair OQ-03 pointed to.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.  Everything is stated over an
arbitrary `P`, so nothing imports the parent's (inconsistent) global axioms.
-/

namespace GodelFirstIncompletenessOQ01OQ02

/-- Code of the Gödel sentence `G` (parent: `G = ⟨42⟩`). -/
def gCode : ℕ := 42
/-- Code of `Prov(⌜G⌝)` (parent: `Prov (godelNum G) = ⟨42 * 2⟩`). -/
def provGCode : ℕ := 84
/-- Code of `¬G` (parent: `neg G = ⟨42 + 1⟩`). -/
def negGCode : ℕ := 43
/-- Code of `¬Prov(⌜G⌝)` (`neg` of `provG`: `⟨84 + 1⟩`). -/
def negProvGCode : ℕ := 85

/-- Derivability D1 (Σ₁-completeness) at `φ = G`: provability of `G` entails provability of
    `Prov(⌜G⌝)`. -/
def D1G (P : ℕ → Prop) : Prop := P gCode → P provGCode

/-- Object-level fixed point, forward half: `F ⊢ (G → ¬Prov⌜G⌝)`, so provability of `G` entails
    provability of `¬Prov(⌜G⌝)`.  (This replaces OQ-03's illegitimate meta equivalence
    `P G ↔ ¬ P provG`.) -/
def FixG (P : ℕ → Prop) : Prop := P gCode → P negProvGCode

/-- Consistency of `F`: it does not prove both `Prov(⌜G⌝)` and its negation `¬Prov(⌜G⌝)`. -/
def Consistent (P : ℕ → Prop) : Prop := ¬ (P provGCode ∧ P negProvGCode)

/-- Object-level fixed point, backward half: `F ⊢ (¬G → Prov⌜G⌝)`, so provability of `¬G` entails
    provability of `Prov(⌜G⌝)`. -/
def NegGProv (P : ℕ → Prop) : Prop := P negGCode → P provGCode

/-- ω-consistency at `G`: if `G` is unprovable, so is `Prov(⌜G⌝)`. -/
def OmegaCons (P : ℕ → Prop) : Prop := ¬ P gCode → ¬ P provGCode

/-!
## The incompleteness theorem, from consistent hypotheses
-/

/-- **Consistency half of First Incompleteness.**  `G` is not provable.  If it were, `D1G` gives
    `P provG` and the object-level fixed point `FixG` gives `P negProvG`, contradicting
    `Consistent`. -/
theorem godel_not_provable (P : ℕ → Prop)
    (hD1 : D1G P) (hFix : FixG P) (hCon : Consistent P) : ¬ P gCode := by
  simp only [D1G, FixG, Consistent] at hD1 hFix hCon
  tauto

/-- **ω-consistency half of First Incompleteness.**  `¬G` is not provable.  If it were, `NegGProv`
    gives `P provG`; but `godel_not_provable` gives `¬ P G`, whence `OmegaCons` gives `¬ P provG` —
    a contradiction. -/
theorem neg_godel_not_provable (P : ℕ → Prop)
    (hD1 : D1G P) (hFix : FixG P) (hCon : Consistent P)
    (hNeg : NegGProv P) (hOmega : OmegaCons P) : ¬ P negGCode := by
  have hG : ¬ P gCode := godel_not_provable P hD1 hFix hCon
  simp only [NegGProv, OmegaCons] at hNeg hOmega
  tauto

/-- **First Incompleteness (non-vacuous form).**  From the five consistent clauses, `G` is
    undecidable: neither `G` nor `¬G` is provable. -/
theorem first_incompleteness (P : ℕ → Prop)
    (hD1 : D1G P) (hFix : FixG P) (hCon : Consistent P)
    (hNeg : NegGProv P) (hOmega : OmegaCons P) : ¬ P gCode ∧ ¬ P negGCode :=
  ⟨godel_not_provable P hD1 hFix hCon,
   neg_godel_not_provable P hD1 hFix hCon hNeg hOmega⟩

/-!
## The hypotheses are satisfiable — the repair is genuinely non-vacuous

Unlike the parent's axiom set (which `…OQ01OQ03.no_model_of_all_axioms` shows has *no* model),
the repaired set has a model.  So the incompleteness conclusion above is drawn from *satisfiable*
hypotheses, not from a contradiction.
-/

/-- **The repaired axiom set has a model.**  Witness: nothing provable (`P := fun _ => False`)
    satisfies all five clauses vacuously.  This already refutes the parent's flaw
    (`no_model_of_all_axioms`). -/
theorem has_model :
    ∃ P : ℕ → Prop, D1G P ∧ FixG P ∧ Consistent P ∧ NegGProv P ∧ OmegaCons P := by
  refine ⟨fun _ => False, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [D1G, FixG, Consistent, NegGProv, OmegaCons] <;> decide

/-- **A model in which something is provable.**  Taking `¬Prov(⌜G⌝)` to be the one provable
    sentence (`P n ↔ n = negProvG`) still satisfies all five clauses, and here `P` is *not*
    identically `False`.  So the incompleteness of `G` does not rely on the degenerate
    `Provable := fun _ => False` reading — a genuine, non-empty theory can be incomplete. -/
theorem has_nontrivial_model :
    ∃ P : ℕ → Prop,
      (D1G P ∧ FixG P ∧ Consistent P ∧ NegGProv P ∧ OmegaCons P) ∧ (∃ n, P n) := by
  refine ⟨fun n => n = negProvGCode, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨negProvGCode, rfl⟩⟩ <;>
    simp only [D1G, FixG, Consistent, NegGProv, OmegaCons] <;> decide

/-- **In every model, `Prov(⌜G⌝)` is unprovable too.**  Combining `godel_not_provable` with
    ω-consistency: since `G` is unprovable, so is `Prov(⌜G⌝)`.  (In particular no model of the
    repaired set proves `Prov(⌜G⌝)` — consistent with `provG` never being a theorem.) -/
theorem provG_not_provable (P : ℕ → Prop)
    (hD1 : D1G P) (hFix : FixG P) (hCon : Consistent P) (hOmega : OmegaCons P) :
    ¬ P provGCode := by
  have hG : ¬ P gCode := godel_not_provable P hD1 hFix hCon
  simp only [OmegaCons] at hOmega
  exact hOmega hG

end GodelFirstIncompletenessOQ01OQ02

/-!
## Summary

Answering OQ-02 (is there a *consistent* axiom set giving First Incompleteness non-vacuously?):

- The repair is exactly the one OQ-03 pointed to: drop the illegitimate meta self-reference
  `P G ↔ ¬ P provG` and use the object-level fixed-point clauses `FixG` (`P G → P negProvG`) and
  `NegGProv` (`P negG → P provG`) together with derivability `D1G`, `Consistent`, and `OmegaCons`.
- `godel_not_provable`, `neg_godel_not_provable`, `first_incompleteness`: `G` is undecidable for
  every `P` satisfying the five clauses.
- `has_model`, `has_nontrivial_model`: the five clauses are *satisfiable* (and satisfiable by a
  non-empty theory), so the conclusion is drawn from consistent hypotheses — the honest,
  non-vacuous First Incompleteness the parent aimed for, and a direct fix of the vacuity found in
  `…OQ01OQ03`.
- `provG_not_provable`: in every such model `Prov(⌜G⌝)` is unprovable as well.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
