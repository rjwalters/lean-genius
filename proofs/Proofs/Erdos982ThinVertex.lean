/-
Erdős Problem #982 — The "thin vertex" pigeonhole reduction

Source: https://erdosproblems.com/982
Parent file: Proofs/Erdos982Problem.lean (states the open conjecture with axioms)

Statement of the open problem:
If n distinct points in ℝ² form a convex polygon, then some vertex has at least
⌊n/2⌋ distinct distances to the other vertices.  This remains OPEN; the best
known lower bound is ≈ 0.361 n (Nivasch–Pach–Pinchasi–Zerbib 2013), while the
regular polygon shows ⌊n/2⌋ would be best possible.

WHAT THIS FILE PROVES (axiom-free, no `sorry`):

The combinatorial *engine* behind every Moser-type bound, isolated cleanly and
proved from scratch.  Fix a vertex `p`.  The other vertices fall into "distance
classes": two vertices are in the same class iff they are equidistant from `p`
(equivalently, they lie on a common circle centred at `p`).  Pigeonhole then
relates the number of distinct distances to the size of the largest class:

      (number of other vertices) ≤ (number of distinct distances) · (largest class).

From this single inequality we extract three facts that pin down *exactly* where
the difficulty of #982 lives:

  1. `distinctDistances_ge_half`  — if no circle centred at `p` carries 3 of the
     other vertices (every distance class has size ≤ 2), then `p` already sees
     ≥ ⌊n/2⌋ distinct distances.  So the conjecture follows the instant one finds
     such a "thin" vertex.  The bound is *tight*: the regular n-gon has all
     classes of size ≤ 2 and exactly ⌊n/2⌋ distinct distances from each vertex.

  2. `conjecture_of_exists_thin_vertex` — packaged for `maxDistinctDistances`:
     a single thin vertex makes the #982 conjecture hold for that polygon.

  3. `exists_three_equidistant_of_few_distances` — the contrapositive, and the
     exact link to Erdős Problem #97: if `p` sees fewer than ⌊n/2⌋ distances then
     some circle centred at `p` carries ≥ 3 other vertices.  Erdős conjectured
     (#97) that one can always avoid 3 equidistant vertices; that was *disproved*,
     which is precisely why #982 is hard — no purely combinatorial thin vertex is
     guaranteed.

None of these statements needs convex position: they are pure pigeonhole, and the
genuinely geometric content of #982 is exactly the (open) claim that a thin vertex
always exists.  That is the value of this file — it draws the line precisely.

The general `M`-uniform bound `card_le_distinct_mul` underlies Moser's
`f(n) ≥ ⌈n/3⌉` (a vertex with all classes ≤ 3) and every later refinement.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

namespace Erdos982ThinVertex

/-
## Part I: The abstract pigeonhole engine

Nothing here is geometric.  For any function `f : α → β` and any finite set `s`,
if every fibre of `f` over `s` has at most `M` elements, then `s` is no larger
than `M` times the number of distinct values `f` takes on `s`.
-/

variable {α β : Type*} [DecidableEq β]

/--
**Uniform fibre pigeonhole.**
If each value `b` in the image of `f` is attained by at most `M` elements of `s`,
then `s.card ≤ (number of distinct values) * M`.
-/
theorem card_le_image_mul {s : Finset α} (f : α → β) {M : ℕ}
    (hM : ∀ b ∈ s.image f, (s.filter (fun a => f a = b)).card ≤ M) :
    s.card ≤ (s.image f).card * M := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
        (f := f) (t := s.image f) (fun a ha => Finset.mem_image_of_mem f ha)]
  calc ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card
        ≤ ∑ _b ∈ s.image f, M := Finset.sum_le_sum hM
    _ = (s.image f).card * M := by rw [Finset.sum_const, smul_eq_mul]

/--
**Distinct-value lower bound (floor division form).**
A direct corollary: the number of distinct values is at least `s.card / M`.
-/
theorem image_card_ge_div {s : Finset α} (f : α → β) {M : ℕ}
    (hM : ∀ b ∈ s.image f, (s.filter (fun a => f a = b)).card ≤ M) :
    s.card / M ≤ (s.image f).card := by
  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact card_le_image_mul f hM)

/-
## Part II: Distinct distances from a vertex

We specialise the engine to `f = dist p`.  A "distance class" of `p` in `S` is a
fibre of `q ↦ dist p q`: the set of vertices at one fixed distance, i.e. on one
circle centred at `p`.
-/

/-- The Euclidean plane, ℝ² as an inner product space. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Number of distinct distances from `p` to the points of `S`. -/
noncomputable def distinctDistancesFrom (p : Plane) (S : Finset Plane) : ℕ :=
  (S.image (fun q => dist p q)).card

/-- Maximum, over all vertices `p ∈ S`, of the distinct distances from `p` to the
others.  This is the quantity the #982 conjecture lower-bounds by `⌊n/2⌋`. -/
noncomputable def maxDistinctDistances (S : Finset Plane) : ℕ :=
  S.sup (fun p => distinctDistancesFrom p (S.erase p))

/--
**Moser-type general bound.**
If every circle centred at `p` carries at most `M` of the other `n-1` vertices,
then `p` sees at least `(n-1)/M` distinct distances.  (`M = 3` is Moser's case.)
-/
theorem distinctDistances_ge_of_classes_le {p : Plane} {S : Finset Plane} {n : ℕ}
    (hp : p ∈ S) (hcard : S.card = n) {M : ℕ}
    (hM : ∀ d : ℝ, ((S.erase p).filter (fun q => dist p q = d)).card ≤ M) :
    (n - 1) / M ≤ distinctDistancesFrom p (S.erase p) := by
  have hcard' : (S.erase p).card = n - 1 := by
    rw [Finset.card_erase_of_mem hp, hcard]
  have := image_card_ge_div (s := S.erase p) (fun q => dist p q) (fun b _ => hM b)
  rwa [hcard'] at this

/--
**Thin vertex ⇒ ⌊n/2⌋ distinct distances (the tight case).**
If no circle centred at `p` carries 3 of the other vertices — every distance
class has size ≤ 2 — then `p` already determines at least `⌊n/2⌋` distinct
distances.  This is exactly the bound the regular polygon attains.
-/
theorem distinctDistances_ge_half {p : Plane} {S : Finset Plane} {n : ℕ}
    (hp : p ∈ S) (hcard : S.card = n)
    (h2 : ∀ d : ℝ, ((S.erase p).filter (fun q => dist p q = d)).card ≤ 2) :
    n / 2 ≤ distinctDistancesFrom p (S.erase p) := by
  have hcard' : (S.erase p).card = n - 1 := by
    rw [Finset.card_erase_of_mem hp, hcard]
  have hbound : (S.erase p).card ≤ distinctDistancesFrom p (S.erase p) * 2 :=
    card_le_image_mul (s := S.erase p) (fun q => dist p q) (fun b _ => h2 b)
  rw [hcard'] at hbound
  -- (n-1) ≤ 2·k  ⟹  ⌊n/2⌋ ≤ k, using parity (the "diameter is unique" gain)
  omega

/--
**A single thin vertex settles #982 for this polygon.**
If some vertex `p ∈ S` has all distance classes of size ≤ 2, then
`maxDistinctDistances S ≥ ⌊n/2⌋`, i.e. the Erdős #982 conjecture holds for `S`.
-/
theorem conjecture_of_exists_thin_vertex {S : Finset Plane} {n : ℕ} (hcard : S.card = n)
    (h : ∃ p ∈ S, ∀ d : ℝ, ((S.erase p).filter (fun q => dist p q = d)).card ≤ 2) :
    n / 2 ≤ maxDistinctDistances S := by
  obtain ⟨p, hp, h2⟩ := h
  calc n / 2 ≤ distinctDistancesFrom p (S.erase p) := distinctDistances_ge_half hp hcard h2
    _ ≤ maxDistinctDistances S :=
        Finset.le_sup (f := fun p => distinctDistancesFrom p (S.erase p)) hp

/--
**The obstruction, made explicit (link to Erdős #97).**
Contrapositive of the thin-vertex bound: if `p` sees *fewer* than `⌊n/2⌋`
distinct distances, then some circle centred at `p` carries **three** of the
other vertices.  Erdős #97 asked whether such equidistant triples can always be
avoided at some vertex; the answer is *no*, which is precisely what keeps #982 open.
-/
theorem exists_three_equidistant_of_few_distances {p : Plane} {S : Finset Plane} {n : ℕ}
    (hp : p ∈ S) (hcard : S.card = n)
    (hfew : distinctDistancesFrom p (S.erase p) < n / 2) :
    ∃ d : ℝ, 3 ≤ ((S.erase p).filter (fun q => dist p q = d)).card := by
  by_contra h
  push_neg at h
  have h2 : ∀ d : ℝ, ((S.erase p).filter (fun q => dist p q = d)).card ≤ 2 :=
    fun d => Nat.lt_succ_iff.mp (h d)
  have := distinctDistances_ge_half hp hcard h2
  omega

/-
## Part III: A floor toward the conjecture, with no geometry assumed

Every vertex of a polygon with ≥ 2 vertices sees at least one distance — so
`maxDistinctDistances S ≥ 1`.  This discharges the `triangle_case` of the parent
file (`n = 3` needs `≥ 1`) without invoking any axiom.
-/

/--
**Trivial but axiom-free floor.**
Any point set with at least two points has a vertex seeing ≥ 1 distinct distance.
-/
theorem maxDistinctDistances_pos {S : Finset Plane} (h : 2 ≤ S.card) :
    1 ≤ maxDistinctDistances S := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have herase : (S.erase p).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hp]; omega
  have h1 : 1 ≤ distinctDistancesFrom p (S.erase p) := by
    rw [distinctDistancesFrom, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
        Finset.image_eq_empty]
    exact herase.ne_empty
  exact le_trans h1 (Finset.le_sup (f := fun p => distinctDistancesFrom p (S.erase p)) hp)

/--
**Triangle case (parent `triangle_case`), axiom-free.**
Every triangle has a vertex with ≥ 1 distinct distance; the #982 bound `⌊3/2⌋ = 1`.
-/
theorem triangle_case (S : Finset Plane) (hcard : S.card = 3) :
    1 ≤ maxDistinctDistances S :=
  maxDistinctDistances_pos (by omega)

/-
## Part IV: Sanity check — the regular polygon side

We record the abstract optimality witnessed above: a thin vertex gives `⌊n/2⌋`,
and `⌊n/2⌋` is what the parent file's `regular_polygon_distances` axiom asserts is
achieved.  The equality `⌈(n-1)/2⌉ = ⌊n/2⌋` (proved by `omega`) is the arithmetic
reason the "diameter is unique" so the crude `(n-1)/2` is improved to `⌊n/2⌋`.
-/

/-- `⌈(n-1)/2⌉ = ⌊n/2⌋`: the unique-diameter arithmetic gain, for the record. -/
theorem ceil_half_pred_eq_floor_half (n : ℕ) (hn : 1 ≤ n) :
    (n - 1 + 1) / 2 = n / 2 := by
  omega

end Erdos982ThinVertex
