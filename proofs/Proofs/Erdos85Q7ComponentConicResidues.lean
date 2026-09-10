import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite local certificates for the H3 component conics.
These residue statements alone do not formalize the number-field embedding,
primitive denominator clearing, or graph-to-form reduction. -/
namespace Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem q7_h3_conic_mod9 (u v z : Fin 9)
    (h : (u.val ^ 2 + v.val ^ 2) % 9 = (3 * z.val ^ 2) % 9) :
    u.val % 3 = 0 ∧ v.val % 3 = 0 ∧ z.val % 3 = 0 := by
  have hall : ∀ u v z : Fin 9,
      (u.val ^ 2 + v.val ^ 2) % 9 = (3 * z.val ^ 2) % 9 →
      u.val % 3 = 0 ∧ v.val % 3 = 0 ∧ z.val % 3 = 0 := by decide
  exact hall u v z h

theorem q7_h3_conic_mod49 (u v z : Fin 49)
    (h : (u.val ^ 2 + 42 * v.val ^ 2) % 49 = (40 * z.val ^ 2) % 49) :
    u.val % 7 = 0 ∧ v.val % 7 = 0 ∧ z.val % 7 = 0 := by
  have hall : ∀ u v z : Fin 49,
      (u.val ^ 2 + 42 * v.val ^ 2) % 49 = (40 * z.val ^ 2) % 49 →
      u.val % 7 = 0 ∧ v.val % 7 = 0 ∧ z.val % 7 = 0 := by decide
  exact hall u v z h
end Erdos85
#print axioms Erdos85.q7_h3_conic_mod9
#print axioms Erdos85.q7_h3_conic_mod49
