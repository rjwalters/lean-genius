/-
# Erdős Problem 193: Collinear Points in Lattice Walks

Let `S ⊆ ℤ³` be a finite set and let `A = {a₁, a₂, …} ⊂ ℤ³` be an
infinite `S`-walk, meaning `aᵢ₊₁ − aᵢ ∈ S` for all `i`.
Must `A` contain three collinear points?

Originally posed by Gerver and Ramsey. Proved in `ℤ²`;
the three-dimensional case remains **OPEN**.

*Reference:* [erdosproblems.com/193](https://www.erdosproblems.com/193)
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/- ## Basic definitions -/

/-- A point in `ℤ^d` is represented as `Fin d → ℤ`. -/
abbrev LatPoint (d : ℕ) := Fin d → ℤ

/-- An infinite walk in `ℤ^d` is a sequence `ℕ → LatPoint d`. -/
abbrev Walk (d : ℕ) := ℕ → LatPoint d

/-- The step set: a finite subset of `ℤ^d`. -/
abbrev StepSet (d : ℕ) := Finset (LatPoint d)

/-- A walk is an `S`-walk if every consecutive step belongs to `S`. -/
def IsStepWalk {d : ℕ} (S : StepSet d) (w : Walk d) : Prop :=
    ∀ i : ℕ, (fun j => w (i + 1) j - w i j) ∈ S

/-- A walk visits distinct points (is injective). -/
def IsInjective {d : ℕ} (w : Walk d) : Prop :=
    Function.Injective w

/- ## Collinearity -/

/-- Three points `p, q, r` in `ℤ^d` are collinear if `q − p` and `r − p`
are parallel, i.e., there exist integers `a, b` (not both zero) such that
`a • (q − p) = b • (r − p)`. -/
def AreCollinear {d : ℕ} (p q r : LatPoint d) : Prop :=
    ∃ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ j : Fin d, a * (q j - p j) = b * (r j - p j)

/-- A walk contains three collinear points if there exist distinct indices
whose images are collinear. -/
def HasThreeCollinear {d : ℕ} (w : Walk d) : Prop :=
    ∃ i j k : ℕ, i < j ∧ j < k ∧ AreCollinear (w i) (w j) (w k)

/- ## Main conjecture -/

/-- Erdős Problem 193: Every infinite injective `S`-walk in `ℤ³` contains
three collinear points. -/
def ErdosProblem193 : Prop :=
    ∀ (S : StepSet 3) (w : Walk 3),
      IsStepWalk S w → IsInjective w → HasThreeCollinear w

/- ## Known results -/

/-- In `ℤ²`, every infinite injective `S`-walk contains three collinear
points (Gerver–Ramsey). -/
axiom gerver_ramsey_2d :
    ∀ (S : StepSet 2) (w : Walk 2),
      IsStepWalk S w → IsInjective w → HasThreeCollinear w

/- ## Basic properties -/

/-- Collinearity is reflexive: any point is collinear with itself.
    Uses witnesses (0, 1): 0·(q-p) = 1·(p-p) = 0. -/
theorem collinear_refl {d : ℕ} (p q : LatPoint d) :
    AreCollinear p q p := by
  exact ⟨0, 1, Or.inr one_ne_zero, fun j => by ring⟩

/-- Collinearity is symmetric in the outer two points.
    Given a(q-p) = b(r-p), witnesses (a, a-b) satisfy a(q-r) = (a-b)(p-r). -/
theorem collinear_symm {d : ℕ} (p q r : LatPoint d) :
    AreCollinear p q r → AreCollinear r q p := by
  rintro ⟨a, b, hab, h⟩
  refine ⟨a, a - b, ?_, fun j => ?_⟩
  · -- a ≠ 0 ∨ a - b ≠ 0: if a = 0 then b ≠ 0 so a - b = -b ≠ 0
    rcases ne_or_eq a 0 with ha | rfl
    · exact Or.inl ha
    · exact Or.inr (by simpa using hab.resolve_left (not_not.mpr rfl))
  · -- a * (q j - r j) = (a - b) * (p j - r j) follows from a*(q_j-p_j) = b*(r_j-p_j)
    have := h j; linarith

/-- A constant walk (all points equal) trivially has collinear triples. -/
theorem collinear_const {d : ℕ} (v : LatPoint d) :
    AreCollinear v v v := collinear_refl v v
