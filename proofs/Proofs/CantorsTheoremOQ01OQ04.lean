/-
# |𝒫(𝒫(ℝ))| = ℶ₃: The Third Beth Number via Iterated Power Sets

## Open Question: cantors-theorem-oq-01-oq-04

This entry resolves open question #4 of `cantors-theorem-oq-01` ("The Cardinality
of 𝒫(ℝ)"), which proved `|𝒫(ℝ)| = ℶ₂`.  The follow-up asks for the next rung of
the beth tower:

  **Is `|𝒫(𝒫(ℝ))| = ℶ₃`?  (Yes — provable in ZFC, the same pattern as ℶ₂.)**

The answer is yes, and the proof is a clean application of Cantor's power-set
cardinality law twice:

  |𝒫(𝒫(ℝ))| = 2^|𝒫(ℝ)| = 2^(2^|ℝ|) = 2^(2^(2^ℵ₀)) = ℶ₃.

The beth tower is `ℶ₀ = ℵ₀`, `ℶ₁ = 2^ℵ₀ = 𝔠 = |ℝ|`, `ℶ₂ = 2^𝔠 = |𝒫(ℝ)|`,
`ℶ₃ = 2^ℶ₂ = |𝒫(𝒫(ℝ))|`, each level the power set of the previous one.

Unlike the *aleph*-index of these cardinals (which is independent of ZFC — the
content of the parent's open question), the *beth*-index is pinned down outright:
every iterated power set of ℝ lands exactly on a beth number, by definition of the
beth function as `ℶ_{α+1} = 2^{ℶ_α}`.

## What is proved

* `card_powerSet_powerSet_real_eq_beth_three` — `|𝒫(𝒫(ℝ))| = ℶ₃` (main result).
* `beth_two_eq`, `beth_three_eq` — the successor unfoldings `ℶ₂ = 2^ℶ₁`, `ℶ₃ = 2^ℶ₂`.
* `card_real_eq_beth_one`, `card_powerSet_real_eq_beth_two` — the lower rungs,
  re-derived here so the file is self-contained.
* `card_real_lt_powerSet`, `card_powerSet_real_lt_powerSet_powerSet` — Cantor's
  strict inequalities `|ℝ| < |𝒫(ℝ)| < |𝒫(𝒫(ℝ))|`.
* `beth_tower_strictMono` — `ℶ₁ < ℶ₂ < ℶ₃`, the strictly increasing tower.

No axioms beyond Lean/Mathlib's foundations; 0 sorries.
-/
import Mathlib

namespace CantorsTheoremOQ01OQ04

open Cardinal

/-- `ℶ₂ = 2^ℶ₁` (the beth successor unfolding at 2). -/
theorem beth_two_eq : (beth 2 : Cardinal.{0}) = 2 ^ beth 1 := by
  have o2 : (2 : Ordinal) = Order.succ (1 : Ordinal) := by
    rw [Order.succ_eq_add_one]; norm_num
  rw [o2, beth_succ]

/-- `ℶ₃ = 2^ℶ₂` (the beth successor unfolding at 3). -/
theorem beth_three_eq : (beth 3 : Cardinal.{0}) = 2 ^ beth 2 := by
  have o3 : (3 : Ordinal) = Order.succ (2 : Ordinal) := by
    rw [Order.succ_eq_add_one]; norm_num
  rw [o3, beth_succ]

/-- `|ℝ| = ℶ₁`: the cardinality of the reals is the first beth number
(`Cardinal.mk_real` says `#ℝ = 𝔠`, and `Cardinal.beth_one` says `ℶ₁ = 𝔠`). -/
theorem card_real_eq_beth_one : (#ℝ : Cardinal.{0}) = beth 1 := by
  rw [mk_real, beth_one]

/-- `|𝒫(ℝ)| = ℶ₂`: re-derivation of the parent result `cantors-theorem-oq-01`,
`#(Set ℝ) = 2^#ℝ = 2^ℶ₁ = ℶ₂`. -/
theorem card_powerSet_real_eq_beth_two : (#(Set ℝ) : Cardinal.{0}) = beth 2 := by
  rw [mk_set, card_real_eq_beth_one, beth_two_eq]

/-- **Main result: `|𝒫(𝒫(ℝ))| = ℶ₃`.**

`#(Set (Set ℝ)) = 2^#(Set ℝ) = 2^ℶ₂ = ℶ₃`, applying the power-set cardinality
law `Cardinal.mk_set` to the second power set and unfolding the beth successor. -/
theorem card_powerSet_powerSet_real_eq_beth_three :
    (#(Set (Set ℝ)) : Cardinal.{0}) = beth 3 := by
  rw [mk_set, card_powerSet_real_eq_beth_two, beth_three_eq]

/-- Cantor's theorem for ℝ: `|ℝ| < |𝒫(ℝ)|`. -/
theorem card_real_lt_powerSet : (#ℝ : Cardinal.{0}) < #(Set ℝ) := by
  rw [mk_set]; exact cantor _

/-- Cantor's theorem one level up: `|𝒫(ℝ)| < |𝒫(𝒫(ℝ))|`. -/
theorem card_powerSet_real_lt_powerSet_powerSet :
    (#(Set ℝ) : Cardinal.{0}) < #(Set (Set ℝ)) := by
  have h : (#(Set (Set ℝ)) : Cardinal.{0}) = 2 ^ #(Set ℝ) := mk_set
  rw [h]; exact cantor _

/-- The beth tower is strictly increasing through the third level: `ℶ₁ < ℶ₂ < ℶ₃`. -/
theorem beth_tower_strictMono :
    (beth 1 : Cardinal.{0}) < beth 2 ∧ (beth 2 : Cardinal.{0}) < beth 3 :=
  ⟨beth_strictMono (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)),
   beth_strictMono (by exact_mod_cast (show (2 : ℕ) < 3 by norm_num))⟩

/-- **Summary of the ZFC-provable facts about `|𝒫(𝒫(ℝ))|`.**

1. `|𝒫(𝒫(ℝ))| = ℶ₃` (the third beth number);
2. the Cantor tower `|ℝ| < |𝒫(ℝ)| < |𝒫(𝒫(ℝ))|`;
3. the beth tower `ℶ₁ < ℶ₂ < ℶ₃`. -/
theorem cantors_theorem_oq01oq04_summary :
    ((#(Set (Set ℝ)) : Cardinal.{0}) = beth 3) ∧
    ((#ℝ : Cardinal.{0}) < #(Set ℝ) ∧ (#(Set ℝ) : Cardinal.{0}) < #(Set (Set ℝ))) ∧
    ((beth 1 : Cardinal.{0}) < beth 2 ∧ (beth 2 : Cardinal.{0}) < beth 3) :=
  ⟨card_powerSet_powerSet_real_eq_beth_three,
   ⟨card_real_lt_powerSet, card_powerSet_real_lt_powerSet_powerSet⟩,
   beth_tower_strictMono⟩

end CantorsTheoremOQ01OQ04
