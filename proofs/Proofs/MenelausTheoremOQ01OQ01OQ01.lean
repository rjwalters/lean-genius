import Proofs.MenelausTheoremOQ01
import Mathlib.Tactic

/-
# Menelaus follow-up: realisable sign patterns (biconditional characterisation)

Open question: `menelaus-theorem-oq-01-oq-01-oq-01`
Parent: `Proofs/MenelausTheoremOQ01.lean` (`menelaus-theorem-oq-01-oq-01`).

## What this adds

The parent proves the *forward* parity dichotomy: a collinear transversal
(`menelausProduct cfg = -1`) forces an **odd** number of the three division points to be
external (`external_parity_odd`), and the Ceva value `+1` forces an **even** number
(`external_parity_even`). Those are one-directional: they say "if a configuration exists,
its sign pattern has the stated parity".

This file proves the **converse / realisability** direction and packages both into sharp
biconditionals. A sign pattern `(sX, sY, sZ) ∈ Bool³` (where `sᵢ = true` means "point `i`
is external", i.e. its signed ratio is negative) is **realisable by a genuine
non-degenerate transversal with product `-1`** *if and only if* it has an odd number of
`true`s. Symmetrically, it is realisable with product `+1` iff it has an even number.

The forward implication reuses the parent's parity theorems; the backward (existence)
implication is the new content — four explicit witness configurations on the fixed
triangle `(0,0),(1,0),(0,1)`, one realising each admissible pattern.

`odd #true` is encoded as `sX ^^ sY ^^ sZ = true` (`xor` of the three bits), `even` as
`= false`.

## Status
- [x] Four explicit witnesses for the odd (Menelaus) patterns
- [x] Four explicit witnesses for the even (Ceva) patterns
- [x] `realisable_iff_odd`: product `-1` realisability ⟺ odd parity
- [x] `realisable_iff_even`: product `+1` realisability ⟺ even parity
- [x] 0 sorries, 0 axioms
-/

namespace MenelausTheoremOQ01OQ01OQ01

open MenelausTheorem MenelausTheoremOQ01

set_option linter.unusedVariables false

/-! ### Sign ↔ boolean bookkeeping helpers -/

/-- Package "`p` holds" as the boolean iff `p ↔ (true = true)`. -/
private theorem iff_true_of {p : Prop} (hp : p) : p ↔ (true = true) :=
  ⟨fun _ => rfl, fun _ => hp⟩

/-- Package "`p` fails" as the boolean iff `p ↔ (false = true)`. -/
private theorem iff_false_of {p : Prop} (hp : ¬ p) : p ↔ (false = true) :=
  ⟨fun h => absurd h hp, fun h => absurd h (by decide)⟩

/-- A negative ratio pins the corresponding sign bit to `true`. -/
private theorem bit_of_neg {r : ℝ} {s : Bool} (hneg : r < 0) (h : r < 0 ↔ s = true) :
    s = true := h.mp hneg

/-- A positive ratio pins the corresponding sign bit to `false`. -/
private theorem bit_of_pos {r : ℝ} {s : Bool} (hpos : 0 < r) (h : r < 0 ↔ s = true) :
    s = false := by
  rcases s with _ | _
  · rfl
  · exact absurd (h.mpr rfl) (not_lt.mpr hpos.le)

/-! ### Witnesses for the odd (Menelaus, product `-1`) patterns

All four use the fixed non-degenerate triangle `(0,0),(1,0),(0,1)`; only the division
parameters `t,u,v` change. In each case `menelausProduct = (t/(1-t))·(u/(1-u))·(v/(1-v))`
equals `-1`, and the three signed ratios realise the advertised sign pattern. -/

/-- **All three external.** `t = 2, u = 2, v = -1/3` gives `rX = rY = -2`, `rZ = -1/4`. -/
theorem witness_odd_XYZ :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = -1 ∧ rX cfg < 0 ∧ rY cfg < 0 ∧ rZ cfg < 0 := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := 2, u := 2, v := -1/3,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-- **Only `X` external.** `t = -1, u = 2/3, v = 1/2` gives `rX = -1/2`, `rY = 2`, `rZ = 1`. -/
theorem witness_odd_X :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = -1 ∧ rX cfg < 0 ∧ 0 < rY cfg ∧ 0 < rZ cfg := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := -1, u := 2/3, v := 1/2,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-- **Only `Y` external.** `t = 2/3, u = -1, v = 1/2` gives `rX = 2`, `rY = -1/2`, `rZ = 1`. -/
theorem witness_odd_Y :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = -1 ∧ 0 < rX cfg ∧ rY cfg < 0 ∧ 0 < rZ cfg := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := 2/3, u := -1, v := 1/2,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-- **Only `Z` external.** `t = 2/3, u = 1/2, v = -1` gives `rX = 2`, `rY = 1`, `rZ = -1/2`. -/
theorem witness_odd_Z :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = -1 ∧ 0 < rX cfg ∧ 0 < rY cfg ∧ rZ cfg < 0 := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := 2/3, u := 1/2, v := -1,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-! ### Witnesses for the even (Ceva, product `+1`) patterns -/

/-- **None external.** `t = u = v = 1/2` gives `rX = rY = rZ = 1`. -/
theorem witness_even_none :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = 1 ∧ 0 < rX cfg ∧ 0 < rY cfg ∧ 0 < rZ cfg := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := 1/2, u := 1/2, v := 1/2,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-- **`Y,Z` external.** `t = 1/2, u = -1, v = 2` gives `rX = 1`, `rY = -1/2`, `rZ = -2`. -/
theorem witness_even_YZ :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = 1 ∧ 0 < rX cfg ∧ rY cfg < 0 ∧ rZ cfg < 0 := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := 1/2, u := -1, v := 2,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-- **`X,Z` external.** `t = -1, u = 1/2, v = 2` gives `rX = -1/2`, `rY = 1`, `rZ = -2`. -/
theorem witness_even_XZ :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = 1 ∧ rX cfg < 0 ∧ 0 < rY cfg ∧ rZ cfg < 0 := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := -1, u := 1/2, v := 2,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-- **`X,Y` external.** `t = -1, u = 2, v = 1/2` gives `rX = -1/2`, `rY = -2`, `rZ = 1`. -/
theorem witness_even_XY :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = 1 ∧ rX cfg < 0 ∧ rY cfg < 0 ∧ 0 < rZ cfg := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := -1, u := 2, v := 1/2,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num

/-! ### Master biconditionals -/

/-- **Realisable sign patterns of a Menelaus transversal.** Encoding `sᵢ = true` as
    "division point `i` is external" (signed ratio `< 0`), a pattern `(sX, sY, sZ)` is
    realisable by some genuine non-degenerate configuration whose signed Menelaus product
    is `-1` **iff** it has an odd number of external points (`sX ^^ sY ^^ sZ = true`).

    Forward: the parent's `external_parity_odd`. Backward: the four explicit witnesses. -/
theorem realisable_iff_odd (sX sY sZ : Bool) :
    (∃ cfg : MenelausConfig, menelausProduct cfg = -1 ∧
       (rX cfg < 0 ↔ sX = true) ∧ (rY cfg < 0 ↔ sY = true) ∧ (rZ cfg < 0 ↔ sZ = true))
    ↔ (sX ^^ sY ^^ sZ) = true := by
  constructor
  · rintro ⟨cfg, hp, hX, hY, hZ⟩
    rcases external_parity_odd cfg hp with
      ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · rw [bit_of_neg a hX, bit_of_neg b hY, bit_of_neg c hZ]; decide
    · rw [bit_of_neg a hX, bit_of_pos b hY, bit_of_pos c hZ]; decide
    · rw [bit_of_pos a hX, bit_of_neg b hY, bit_of_pos c hZ]; decide
    · rw [bit_of_pos a hX, bit_of_pos b hY, bit_of_neg c hZ]; decide
  · intro hodd
    rcases sX with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _
    · exact absurd hodd (by decide)
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_odd_Z
      exact ⟨cfg, hp, iff_false_of (not_lt.mpr hx.le),
        iff_false_of (not_lt.mpr hy.le), iff_true_of hz⟩
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_odd_Y
      exact ⟨cfg, hp, iff_false_of (not_lt.mpr hx.le),
        iff_true_of hy, iff_false_of (not_lt.mpr hz.le)⟩
    · exact absurd hodd (by decide)
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_odd_X
      exact ⟨cfg, hp, iff_true_of hx,
        iff_false_of (not_lt.mpr hy.le), iff_false_of (not_lt.mpr hz.le)⟩
    · exact absurd hodd (by decide)
    · exact absurd hodd (by decide)
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_odd_XYZ
      exact ⟨cfg, hp, iff_true_of hx, iff_true_of hy, iff_true_of hz⟩

/-- **Realisable sign patterns of a Ceva (concurrent) configuration.** A pattern is
    realisable by a genuine non-degenerate configuration with signed product `+1` **iff**
    it has an even number of external points (`sX ^^ sY ^^ sZ = false`).

    Forward: the parent's `external_parity_even`. Backward: the four even witnesses. -/
theorem realisable_iff_even (sX sY sZ : Bool) :
    (∃ cfg : MenelausConfig, menelausProduct cfg = 1 ∧
       (rX cfg < 0 ↔ sX = true) ∧ (rY cfg < 0 ↔ sY = true) ∧ (rZ cfg < 0 ↔ sZ = true))
    ↔ (sX ^^ sY ^^ sZ) = false := by
  constructor
  · rintro ⟨cfg, hp, hX, hY, hZ⟩
    rcases external_parity_even cfg hp with
      ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · rw [bit_of_pos a hX, bit_of_pos b hY, bit_of_pos c hZ]; decide
    · rw [bit_of_pos a hX, bit_of_neg b hY, bit_of_neg c hZ]; decide
    · rw [bit_of_neg a hX, bit_of_pos b hY, bit_of_neg c hZ]; decide
    · rw [bit_of_neg a hX, bit_of_neg b hY, bit_of_pos c hZ]; decide
  · intro heven
    rcases sX with _ | _ <;> rcases sY with _ | _ <;> rcases sZ with _ | _
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_even_none
      exact ⟨cfg, hp, iff_false_of (not_lt.mpr hx.le),
        iff_false_of (not_lt.mpr hy.le), iff_false_of (not_lt.mpr hz.le)⟩
    · exact absurd heven (by decide)
    · exact absurd heven (by decide)
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_even_YZ
      exact ⟨cfg, hp, iff_false_of (not_lt.mpr hx.le),
        iff_true_of hy, iff_true_of hz⟩
    · exact absurd heven (by decide)
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_even_XZ
      exact ⟨cfg, hp, iff_true_of hx,
        iff_false_of (not_lt.mpr hy.le), iff_true_of hz⟩
    · obtain ⟨cfg, hp, hx, hy, hz⟩ := witness_even_XY
      exact ⟨cfg, hp, iff_true_of hx, iff_true_of hy,
        iff_false_of (not_lt.mpr hz.le)⟩
    · exact absurd heven (by decide)

/-- **Corollary: exactly four sign patterns are Menelaus-realisable.** Listing the four
    odd patterns explicitly confirms the count `2³ / 2 = 4`. -/
theorem four_odd_patterns_realisable :
    (∃ cfg : MenelausConfig, menelausProduct cfg = -1 ∧
       rX cfg < 0 ∧ rY cfg < 0 ∧ rZ cfg < 0) ∧
    (∃ cfg : MenelausConfig, menelausProduct cfg = -1 ∧
       rX cfg < 0 ∧ 0 < rY cfg ∧ 0 < rZ cfg) ∧
    (∃ cfg : MenelausConfig, menelausProduct cfg = -1 ∧
       0 < rX cfg ∧ rY cfg < 0 ∧ 0 < rZ cfg) ∧
    (∃ cfg : MenelausConfig, menelausProduct cfg = -1 ∧
       0 < rX cfg ∧ 0 < rY cfg ∧ rZ cfg < 0) :=
  ⟨witness_odd_XYZ, witness_odd_X, witness_odd_Y, witness_odd_Z⟩

end MenelausTheoremOQ01OQ01OQ01
