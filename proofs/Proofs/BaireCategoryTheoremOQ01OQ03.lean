import Mathlib

/-!
# Perfect complete metric spaces have at least the cardinality of the continuum

The parent entry (`BaireCategoryTheoremOQ01.lean`) derives the **uncountability of `ℝ`**
from the Baire category theorem: a nonempty complete metric space is non-meagre, so it
cannot be a countable union of singletons, hence it is uncountable.

This file *sharpens* that conclusion from "uncountable" to "has cardinality at least the
continuum `𝔠 = 2^{ℵ₀}`".  The mechanism is the classical **Cantor scheme**: inside any
nonempty perfect set of a complete metric space one can build a binary tree of nested
closed balls with vanishing diameter, producing a continuous injection of the Cantor
space `ℕ → Bool` into the set.  Mathlib packages exactly this construction as
`Perfect.exists_nat_bool_injection`, and we turn the resulting injection into a cardinal
inequality.

## Main results

* `Cardinal.mk_nat_arrow_bool` — the Cantor space has cardinality the continuum,
  `#(ℕ → Bool) = 𝔠`.
* `continuum_le_mk_of_perfect` — **the core statement**: a nonempty perfect subset `C`
  of a complete metric space satisfies `𝔠 ≤ #C`.
* `not_countable_of_perfect` — consequently such a `C` is uncountable (a quantitative
  strengthening of the Cantor–Bendixson "perfect sets are uncountable" fact).
* `continuum_le_mk_of_perfectSpace` — for a nonempty complete metric space **with no
  isolated points** (`PerfectSpace`), the whole space has `𝔠 ≤ #α`.
* `uncountable_of_perfectSpace` — hence such a space is `Uncountable`.
* `continuum_le_mk_real` — the concrete witness `𝔠 ≤ #ℝ`, recovering and sharpening the
  parent's `real_uncountable` (`ℝ` is connected, `T1`, and nontrivial, so it is a
  `PerfectSpace`).

This is the cardinal-arithmetic refinement of the Baire-category uncountability theorem
absent from the gallery; `Mathlib` supplies the Cantor-scheme injection but not the
cardinality corollary.
-/

open Set Cardinal

namespace BaireCategoryTheoremOQ01OQ03

/-- The Cantor space `ℕ → Bool` has cardinality the continuum, `#(ℕ → Bool) = 𝔠`.

`#(ℕ → Bool) = #Bool ^ #ℕ = 2 ^ ℵ₀ = 𝔠`. -/
theorem mk_nat_arrow_bool : #(ℕ → Bool) = 𝔠 := by
  rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]

variable {α : Type} [MetricSpace α] [CompleteSpace α]

/-- **Core statement.** A nonempty perfect subset `C` of a complete metric space has
cardinality at least the continuum.

The Cantor scheme inside `C` (Mathlib's `Perfect.exists_nat_bool_injection`) yields a
*continuous injection* `f : (ℕ → Bool) → α` with range contained in `C`; restricting its
codomain to `C` gives an injection of the continuum-sized Cantor space into `C`. -/
theorem continuum_le_mk_of_perfect {C : Set α} (hC : Perfect C) (hne : C.Nonempty) :
    𝔠 ≤ #C := by
  obtain ⟨f, hrange, _, hinj⟩ := hC.exists_nat_bool_injection hne
  -- Restrict the codomain of `f` to the subtype `C`.
  have hmem : ∀ x : ℕ → Bool, f x ∈ C := fun x => hrange (mem_range_self x)
  let g : (ℕ → Bool) → C := fun x => ⟨f x, hmem x⟩
  have hginj : Function.Injective g := fun a b hab => hinj (congrArg Subtype.val hab)
  have hle : #(ℕ → Bool) ≤ #C := Cardinal.mk_le_of_injective hginj
  rwa [mk_nat_arrow_bool] at hle

/-- A nonempty perfect subset of a complete metric space is uncountable — the
quantitative Cantor–Bendixson statement that perfect sets carry continuum-many points. -/
theorem not_countable_of_perfect {C : Set α} (hC : Perfect C) (hne : C.Nonempty) :
    ¬ C.Countable := by
  intro hcount
  have hco : Countable C := Set.countable_coe_iff.mpr hcount
  have hle : #C ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr hco
  have hge : 𝔠 ≤ #C := continuum_le_mk_of_perfect hC hne
  exact absurd (hge.trans hle) (not_le.mpr aleph0_lt_continuum)

/-- **Whole-space form.** A nonempty complete metric space with no isolated points
(a `PerfectSpace`) has cardinality at least the continuum. -/
theorem continuum_le_mk_of_perfectSpace [Nonempty α] [PerfectSpace α] : 𝔠 ≤ #α := by
  have h := continuum_le_mk_of_perfect (C := (univ : Set α))
    (PerfectSpace.univ_perfect (α := α)) univ_nonempty
  rwa [Cardinal.mk_univ] at h

/-- A nonempty complete metric space with no isolated points is uncountable. -/
theorem uncountable_of_perfectSpace [Nonempty α] [PerfectSpace α] : Uncountable α := by
  rw [← Cardinal.aleph0_lt_mk_iff]
  exact aleph0_lt_continuum.trans_le continuum_le_mk_of_perfectSpace

/-- **Concrete witness.** The real line has cardinality at least the continuum,
recovering (and quantitatively sharpening) the parent file's `real_uncountable`.

`ℝ` is connected, `T1`, and nontrivial, hence a `PerfectSpace`; it is also a complete
metric space, so the whole-space form applies. -/
theorem continuum_le_mk_real : 𝔠 ≤ #ℝ := continuum_le_mk_of_perfectSpace

end BaireCategoryTheoremOQ01OQ03
