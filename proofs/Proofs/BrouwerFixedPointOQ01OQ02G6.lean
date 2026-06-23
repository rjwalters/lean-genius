/-
  Brouwer Fixed Point OQ-01-OQ-02-OQ-03-OQ-02: S13 ACT — G6 companion file

  G6 algebraic Unit-bridge generalization — extracted from the still-open
  PR #18011's Part VI to a standalone companion file paralleling G7
  (`BrouwerFixedPointOQ01OQ02G7.lean`) and G8/G9
  (`BrouwerFixedPointOQ01OQ02G8.lean`).

  Companion-file pivot activated at S13 ACT after the S12 PREP (#19474)
  drain-wave trigger ledger reached 2/2 without rebase activity on PR
  #18011 (`updatedAt: 2026-05-12T08:58:14Z`, ~4 days stale, mergeable:
  CONFLICTING, state: OPEN).

  Generalizes the three Part-V Unit-specific lemmas of the main file
  (`unique_hom_to_unit`, `unique_hom_from_unit_is_zero`,
  `comp_through_unit_is_zero`) to arbitrary subsingleton additive
  commutative groups (the real shape of `H_{n-1}(B^n)` in the
  singular-homology setting), and consolidates the algebraic obstruction
  in `no_split_through_subsingleton`.

  No new imports beyond `Mathlib.Algebra.Group.Hom.Basic` and the integer
  dependencies that AddMonoidHom + the integer-Zero instance already pull
  transitively. No new axioms. Pure algebra.

  Net theorem delta vs. main file: +4 (no_split_through_subsingleton and
  three named helpers in namespace `BrouwerOQ01OQ02`). Net axiom delta: 0.

  Build pending — Docker daemon hung at S13 author time (Server header
  past 10s, no Containers/Runtime; host disk 6.6 Gi free). Risk inventory
  per S12 PREP §5: F1 (`AddMonoidHom.ext`) very low; F2 (`Subsingleton.elim`)
  very low; F3 (`map_zero`) very low; F4 (`zero_comp`) very low; F5
  (universe polymorphism) nil. Estimated probability of clean first-iter
  build: ~92%.
-/

import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.Defs

namespace BrouwerOQ01OQ02

/-- Local re-statement of the main file's `id_Z_ne_zero` (line 168) to keep
    this companion file self-contained. Renamed with a `_g6` suffix to avoid
    namespace clash should both files be open in the same scope. -/
theorem id_Z_ne_zero_g6 : (AddMonoidHom.id ℤ) ≠ (0 : ℤ →+ ℤ) := by
  intro h
  have := AddMonoidHom.ext_iff.mp h 1
  simp [AddMonoidHom.id_apply] at this

/-- Any AddMonoidHom into a subsingleton additive group is uniquely determined.
    Generalizes `unique_hom_to_unit` from `Unit` to any subsingleton target. -/
theorem unique_hom_to_subsingleton
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Subsingleton H]
    (φ₁ φ₂ : G →+ H) : φ₁ = φ₂ := by
  apply AddMonoidHom.ext; intro x
  exact Subsingleton.elim _ _

/-- Any AddMonoidHom out of a subsingleton additive group is the zero map.
    Generalizes `unique_hom_from_unit_is_zero` from `Unit` to any
    subsingleton source. -/
theorem hom_from_subsingleton_is_zero
    {G H : Type*} [AddCommGroup G] [Subsingleton G] [AddCommGroup H]
    (ψ : G →+ H) : ψ = 0 := by
  apply AddMonoidHom.ext; intro x
  have hx : x = (0 : G) := Subsingleton.elim _ _
  rw [hx, ψ.map_zero, AddMonoidHom.zero_apply]

/-- Any composition `ℤ →+ G →+ ℤ` through a subsingleton group `G` is the
    zero map. Generalizes `comp_through_unit_is_zero` from `Unit` to any
    subsingleton intermediate group. -/
theorem comp_through_subsingleton_is_zero
    {G : Type*} [AddCommGroup G] [Subsingleton G]
    (φ : ℤ →+ G) (ψ : G →+ ℤ) : ψ.comp φ = 0 := by
  rw [hom_from_subsingleton_is_zero ψ, AddMonoidHom.zero_comp]

/-- **G6 algebraic bridge**: The identity `AddMonoidHom.id ℤ` cannot factor
    through any subsingleton additive group. Once ACT-D-3 EXEC discharges the
    topological side, the algebraic contradiction lands directly through this
    lemma, independent of the specific carrier-type choice. -/
theorem no_split_through_subsingleton
    {G : Type*} [AddCommGroup G] [Subsingleton G]
    (φ : ℤ →+ G) (ψ : G →+ ℤ) :
    ψ.comp φ ≠ AddMonoidHom.id ℤ := by
  intro h
  have hzero : ψ.comp φ = 0 := comp_through_subsingleton_is_zero φ ψ
  rw [hzero] at h
  exact id_Z_ne_zero_g6 h.symm

end BrouwerOQ01OQ02
