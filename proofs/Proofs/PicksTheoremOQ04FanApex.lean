import Mathlib
import Proofs.PicksTheoremOQ04

/-!
# Pick's Theorem OQ-04 — Apex-independence of the fan triangulation

`PicksTheoremOQ04.lean` proves the fan-triangulation bridge
`shoelace_eq_fan : shoelace (v₀ :: rest) = fanAux v₀ rest`: the signed area of a
polygon equals the sum of the triangle determinants of its fan triangulation *from the
first vertex*.  That result is silent on the choice of apex.

This companion proves the sharper and structurally central fact: the fan sum from **any**
apex `o ∈ ℤ²` — a vertex, an interior point, or a point entirely outside the polygon —
computes the *same* signed area:

    fanCyc o (v₀ :: … :: v_{m-1})  =  Σ_k cross2 o v_k v_{k+1 mod m}  =  shoelace vs      (∀ o)

Here `fanCyc o` sums the triangle determinant `cross2 o v_k v_{k+1}` over **all** `m`
cyclic edges (unlike the parent's `fanAux`, which skips the two edges incident to the
apex `v₀` — they are degenerate there).  The proof is a one-line telescoping: the key
identity `cross2 o a b = cross a b + cross b o − cross a o` (already in the parent) makes
the `o`-dependent terms cancel around the cycle, leaving exactly `shoelace vs`.

Consequences (all 0-axiom):
* `fanCyc_eq_shoelace` — the headline apex-independence identity;
* `fanCyc_apex_independent` — any two apexes give the same value;
* `shoelace_eq_fanCyc` — general fan bridge (parent's `shoelace_eq_fan` is the `o = v₀` case);
* `fanCyc_first_eq_fanAux` — coherence: at apex `v₀` the cyclic fan collapses to the
  parent's `fanAux`;
* `fanCyc_translate` — the cyclic fan sum is translation invariant.

**Why this matters.** Apex-independence is precisely the fact that a polygon may be
triangulated from *any* point without changing its area — the justification of the
fan/ear-triangulation method, which the parent file names as the remaining open direction
toward a constructive Pick's theorem.
-/

set_option linter.unusedVariables false

namespace PicksTheoremOQ04

-- ============================================================
-- The cyclic fan sum from an arbitrary apex
-- ============================================================

/-- `fanCycAux o first vs` sums the triangle determinant `cross2 o a b` over consecutive
    vertices of `vs`, then closes the loop with the triangle `(o, last, first)`.  This is
    the exact `cross2`-analogue of the parent's `shoelaceAux`. -/
def fanCycAux (o first : Pt) : List Pt → ℤ
  | [] => 0
  | [a] => cross2 o a first
  | a :: b :: t => cross2 o a b + fanCycAux o first (b :: t)

/-- The cyclic fan sum of a closed polygon from apex `o`: the sum of the triangle
    determinants `cross2 o v_k v_{k+1 mod m}` over **all** `m` cyclic edges. -/
def fanCyc (o : Pt) : List Pt → ℤ
  | [] => 0
  | v0 :: rest => fanCycAux o v0 (v0 :: rest)

/-- Telescoping bridge: the cyclic fan chain from apex `o` differs from the shoelace chain
    by exactly the boundary `o`-terms `cross first o − cross a o`.  Proved by induction on
    the tail with the leading vertex universally quantified; the interior `o`-terms cancel
    in pairs via the key identity `cross2_eq`. -/
lemma fanCycAux_eq (o first : Pt) (t : List Pt) :
    ∀ a : Pt,
      fanCycAux o first (a :: t) = shoelaceAux first (a :: t) + cross first o - cross a o := by
  induction t with
  | nil =>
    intro a
    simp only [fanCycAux, shoelaceAux]
    rw [cross2_eq]
  | cons b t' ih =>
    intro a
    simp only [fanCycAux, shoelaceAux]
    rw [ih b, cross2_eq]; ring

/-- **Apex-independence (headline).**  For any apex `o`, the cyclic fan sum equals the
    signed shoelace area of the polygon.  The apex-dependent boundary terms
    `cross v₀ o − cross v₀ o` cancel, so the result is independent of `o`. -/
theorem fanCyc_eq_shoelace (o : Pt) (vs : List Pt) :
    fanCyc o vs = shoelace vs := by
  cases vs with
  | nil => rfl
  | cons v0 rest =>
    show fanCycAux o v0 (v0 :: rest) = shoelace (v0 :: rest)
    rw [fanCycAux_eq o v0 rest v0]
    have hs : shoelace (v0 :: rest) = shoelaceAux v0 (v0 :: rest) := rfl
    rw [hs]; ring

/-- The fan triangulation from any two apexes computes the same signed area — the geometric
    content of apex-independence. -/
theorem fanCyc_apex_independent (o o' : Pt) (vs : List Pt) :
    fanCyc o vs = fanCyc o' vs := by
  rw [fanCyc_eq_shoelace, fanCyc_eq_shoelace]

/-- **General fan bridge.**  The signed area equals the fan sum from *any* point `p`.
    The parent's `shoelace_eq_fan` is the special case `p = v₀` (where the two edges at
    `v₀` become degenerate and drop out, recovering `fanAux`). -/
theorem shoelace_eq_fanCyc (p : Pt) (vs : List Pt) :
    shoelace vs = fanCyc p vs :=
  (fanCyc_eq_shoelace p vs).symm

/-- Coherence with the parent bridge: at apex `v₀` the cyclic fan sum collapses to the
    parent's open fan sum `fanAux v₀ rest` (the two edges incident to `v₀` contribute
    degenerate triangles of determinant `0`). -/
theorem fanCyc_first_eq_fanAux (v0 : Pt) (rest : List Pt) :
    fanCyc v0 (v0 :: rest) = fanAux v0 rest := by
  rw [fanCyc_eq_shoelace, shoelace_eq_fan]

/-- The cyclic fan sum is translation invariant: translating both the apex and the polygon
    by the same vector leaves it unchanged. -/
theorem fanCyc_translate (d o : Pt) (vs : List Pt) :
    fanCyc (shift d o) (translate d vs) = fanCyc o vs := by
  rw [fanCyc_eq_shoelace, fanCyc_eq_shoelace, shoelace_translate]

/-- For a triangle the cyclic fan from any apex `o` is the sum of its three sub-triangle
    determinants, and equals the single triangle determinant `cross2 a b c`. -/
theorem fanCyc_triangle (o a b c : Pt) :
    fanCyc o [a, b, c] = cross2 a b c := by
  rw [fanCyc_eq_shoelace, shoelace_triangle_fan]

-- ============================================================
-- Concrete cross-checks: fan from an off-polygon apex
-- ============================================================

/-- Unit right triangle, fan from the apex `(5, 5)` (well outside the triangle): the three
    signed sub-triangle areas still sum to `shoelace = 1`. -/
example : fanCyc (5, 5) [(0, 0), (1, 0), (0, 1)] = 1 := by decide

/-- `3 × 4` rectangle, fan from an interior apex `(1, 1)`: sums to `shoelace = 24`. -/
example : fanCyc (1, 1) [(0, 0), (3, 0), (3, 4), (0, 4)] = 24 := by decide

/-- Apex-independence, checked numerically: fanning the rectangle from `(1, 1)` and from
    `(100, -7)` gives the same value. -/
example :
    fanCyc (1, 1) [(0, 0), (3, 0), (3, 4), (0, 4)]
      = fanCyc (100, -7) [(0, 0), (3, 0), (3, 4), (0, 4)] := by decide

end PicksTheoremOQ04

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `Lean.ofReduceBool` (no `native_decide`) and no `sorryAx`.
#print axioms PicksTheoremOQ04.fanCyc_eq_shoelace
#print axioms PicksTheoremOQ04.fanCyc_apex_independent
#print axioms PicksTheoremOQ04.shoelace_eq_fanCyc
