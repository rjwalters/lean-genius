import Mathlib

/-!
# n = 2 Tucker on the hexagon: the first machine-checked n ≥ 2 instance

`sperner-mathlib4-oq-02` asks whether the parent door-counting engine extends to
**Tucker's lemma** / Borsuk–Ulam.  The n = 1 case is settled
(`SpernerTuckerOneDim.lean`, `SpernerTuckerBorsukUlamOneDim.lean`) by a direct
sign-change parity, and the abstract path-following engine for general `n` is in
`SpernerTuckerPathFollowing.lean`.

This file gives the **first fully machine-checked `n = 2` instance** of Tucker's
conclusion, on the standard small antipodally symmetric triangulation of `B²`
(a hexagon with its centre), entirely by kernel `decide` (0 axioms).  It serves two
purposes that the Python verification artifact (`verify_tucker.py`) could only
assert informally:

1. **Tucker holds** (`hexagon_tucker`): *every* antipodal labelling has a
   complementary edge — the conclusion is true for `n = 2`.
2. **The direct-parity route provably does not lift**
   (`count_even_witness`, `count_odd_witness`): the complementary-edge *count* is
   **not** a parity invariant for `n = 2` — there are antipodal labellings with an
   even count and others with an odd count.  This is the Lean confirmation of the
   knowledge-base "Insight 3": the n = 1 discrete-FTC parity argument cannot be
   ported to `n ≥ 2`, which is exactly why the path-following engine is needed.

## Model

Boundary of the hexagon: six vertices `0,…,5` in antipodal pairs, `v(i+3) = -v(i)`,
plus an interior centre.  The triangulation has six triangles `(centre, v i, v (i+1))`;
its edges are the boundary edges `v i — v (i+1)` and the spokes `centre — v i`.

Labels lie in `{+1, +2, -1, -2}`, encoded as `Fin 4` via `0↦+1, 1↦+2, 2↦-1, 3↦-2`;
`negL` is the label negation, an involution.  A boundary labelling is **antipodal**
when `v(i+3) = -v(i)`, which we build in by setting the second triple of vertices to
the negations of the first.  An edge is **complementary** when its two labels are
negatives of each other.
-/

namespace SpernerTuckerHexagon

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`):
`+1 ↔ -1`, `+2 ↔ -2`.  It is an involution. -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- `negL` is an involution: negating twice is the identity. -/
theorem negL_involutive : Function.Involutive negL := by
  intro x; fin_cases x <;> decide

/-- Two labels are **complementary** when one is the negation of the other. -/
def Compl (x y : Fin 4) : Prop := x = negL y

instance (x y : Fin 4) : Decidable (Compl x y) := inferInstanceAs (Decidable (x = negL y))

/-- The six boundary labels from three free labels `a, b, c` of `v 0, v 1, v 2`,
with the antipodal condition `v(i+3) = -v(i)` built in for `v 3, v 4, v 5`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- The next boundary vertex around the hexagon (cyclic successor). -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-- The boundary labelling really is **antipodal**: `v(i+3) = -v(i)` for all `i`. -/
theorem V_antipodal : ∀ (a b c : Fin 4) (i : Fin 6), V a b c (i + 3) = negL (V a b c i) := by
  decide

/-- **n = 2 Tucker on the hexagon.**  For every antipodal boundary labelling (free
labels `a, b, c` on `v 0, v 1, v 2`, the rest forced antipodally) and every centre
label `d`, the triangulation has a complementary edge: either a boundary edge
`v i — v (i+1)` or a spoke `centre — v i`.  Checked exhaustively over all `4⁴ = 256`
antipodal labellings. -/
theorem hexagon_tucker :
    ∀ a b c d : Fin 4,
      (∃ i : Fin 6, Compl (V a b c i) (V a b c (rot i))) ∨
      (∃ i : Fin 6, Compl d (V a b c i)) := by
  decide

/-- The number of complementary edges of the triangulation under a given labelling:
complementary boundary edges plus complementary spokes. -/
def countCompl (a b c d : Fin 4) : ℕ :=
  ((List.finRange 6).filter (fun i => decide (Compl (V a b c i) (V a b c (rot i))))).length
  + ((List.finRange 6).filter (fun i => decide (Compl d (V a b c i)))).length

/-- There is an antipodal labelling whose complementary-edge count is **even**. -/
theorem count_even_witness : ∃ a b c d : Fin 4, Even (countCompl a b c d) := by decide

/-- There is an antipodal labelling whose complementary-edge count is **odd**. -/
theorem count_odd_witness : ∃ a b c d : Fin 4, Odd (countCompl a b c d) := by decide

/-- **The complementary-edge count is not a parity invariant for `n = 2`.**
Some antipodal labelling has an even count and some has an odd count, so no
"count the target object, show it is odd" argument (the n = 1 route) can prove
Tucker here — the path-following engine is genuinely required. -/
theorem count_parity_not_invariant :
    (∃ a b c d : Fin 4, Even (countCompl a b c d)) ∧
    (∃ a b c d : Fin 4, Odd (countCompl a b c d)) :=
  ⟨count_even_witness, count_odd_witness⟩

end SpernerTuckerHexagon
