import Mathlib

/-!
# Boundary-ring parity for n = 2 Tucker path-following (negative result)

`sperner-mathlib4-oq-02` asks whether the parent door-counting engine extends to
**Tucker's lemma** / Borsuk–Ulam.  The n = 1 case is settled
(`SpernerTuckerOneDim.lean`, `SpernerTuckerBorsukUlamOneDim.lean`), the abstract
n ≥ 2 *path-following* engine is isolated in `SpernerTuckerPathFollowing.lean`,
and the n = 2 Tucker conclusion itself is confirmed by kernel `decide` on the
hexagon-plus-center triangulation (`SpernerTuckerHexagon.lean`).

The path-following engine's crux hypothesis is
`Odd #{boundary ends}` (`exists_interior_degree_one`): a fully complementary
(interior) simplex is forced **only when the boundary path-ends are odd in
number**.  A natural-looking shortcut for the geometric instantiation would be to
take that odd count from the boundary **circle** directly — i.e. count the
complementary edges around the boundary ring `v₀-v₁-⋯-v₅-v₀`.

This file proves that shortcut **cannot work**.  For the antipodally-symmetric
hexagon boundary (labels `{±1, ±2}`, `λ(vᵢ₊₃) = -λ(vᵢ)`), the number of
complementary edges on the boundary ring is **always even** — the exhaustive
distribution over the 64 antipodal ring labellings is `{0, 2, 6}`, never odd.

Consequence (recorded for the next session): the engine's odd boundary parity
must come from the refined *almost-complementary* simplex structure — equivalently
the inductive (n−1)-Tucker on the boundary sphere — **not** from the raw circle's
complementary-edge count.  This is the Lean-checked form of the knowledge-base
correction and rules out a wrong instantiation route.

Proved by kernel `decide` (0 sorries, 0 `axiom`s; `#print axioms` shows only
propext / Classical.choice / Quot.sound — no `Lean.ofReduceBool`, no
`native_decide`).
-/

namespace SpernerTuckerBoundaryParity

/-- Signed labels `{+1, -1, +2, -2}` encoded as `Fin 4`:
`0 ↦ +1`, `1 ↦ -1`, `2 ↦ +2`, `3 ↦ -2`. -/
abbrev Label := Fin 4

/-- Label negation: swaps `+k ↔ -k` on each axis (`0↔1`, `2↔3`). -/
def lneg : Label → Label := ![1, 0, 3, 2]

/-- `lneg` is an involution (negating twice is the identity). -/
theorem lneg_involutive : Function.Involutive lneg := by
  intro x; fin_cases x <;> decide

/-- An edge `(a, b)` is **complementary** when `a = -b`: same axis, opposite sign. -/
def compb (a b : Label) : Bool := a == lneg b

/-- Number of complementary edges around the boundary ring of the hexagon
`v₀-v₁-v₂-v₃-v₄-v₅-v₀`, given the three free labels `l0 = λ(v₀)`, `l1 = λ(v₁)`,
`l2 = λ(v₂)` and the antipodal rule `λ(vᵢ₊₃) = -λ(vᵢ)` (so
`[v₀,…,v₅] = [l0, l1, l2, -l0, -l1, -l2]`). -/
def ringCount (l0 l1 l2 : Label) : Nat :=
  (if compb l0 l1 then 1 else 0)
    + (if compb l1 l2 then 1 else 0)
    + (if compb l2 (lneg l0) then 1 else 0)
    + (if compb (lneg l0) (lneg l1) then 1 else 0)
    + (if compb (lneg l1) (lneg l2) then 1 else 0)
    + (if compb (lneg l2) l0 then 1 else 0)

/-- **Boundary-ring parity is even (negative result).**
The number of complementary edges on the antipodally-labelled hexagon boundary
ring is always even — never odd.  Hence the path-following engine
(`SpernerTuckerPathFollowing.exists_interior_degree_one`) cannot be supplied the
raw boundary-circle complementary-edge count as its required
`Odd #{boundary ends}` hypothesis; the odd parity must come from the refined
almost-complementary structure / inductive (n−1)-Tucker instead.

Kernel-checked over all `4³ = 64` antipodal ring labellings. -/
theorem ring_complementary_count_even :
    ∀ l0 l1 l2 : Label, Even (ringCount l0 l1 l2) := by decide

/-- The ring count is never odd — the contrapositive reading of
`ring_complementary_count_even`, stated for direct use as "the circle parity
shortcut is unavailable". -/
theorem ring_complementary_count_not_odd :
    ∀ l0 l1 l2 : Label, ¬ Odd (ringCount l0 l1 l2) := by
  intro l0 l1 l2 hodd
  exact (Nat.not_odd_iff_even.mpr (ring_complementary_count_even l0 l1 l2)) hodd

end SpernerTuckerBoundaryParity
