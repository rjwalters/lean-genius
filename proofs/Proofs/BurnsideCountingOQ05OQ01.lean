import Mathlib

/-
# Burnside Counting: Reflection-Fixed Colorings of an **Even** Cycle

This file is the even-`n` counterpart of `BurnsideCountingOQ05.lean`, which counted the
`k`-colorings of an `n`-cycle fixed by a reflection for **odd** `n = 2m+1`.

For a cycle with an **even** number of positions `n = 2m`, the dihedral group `D_n` has two
geometrically distinct conjugacy classes of reflections, and they fix different numbers of
colorings:

* **Vertex-axis reflections** pass through two opposite *vertices*. Modelled as negation
  `i ↦ -i` on `ZMod (2m)`, this involution fixes exactly the two positions `0` and `m`
  (the solutions of `2i = 0`). The remaining `2m - 2` positions split into `m - 1` orbit
  pairs `{j, -j}`, so there are `2 + (m-1) = m + 1` orbits and the fixed colorings number
  `k^(m+1) = k^(n/2 + 1)`.

* **Edge-axis reflections** pass through the midpoints of two opposite *edges*. Modelled as
  `i ↦ -1 - i` on `ZMod (2m)`, this involution has **no** fixed points (`2i + 1 = 0` has no
  solution modulo the even number `2m`). All `2m` positions split into `m` orbit pairs
  `{i, -1-i}`, so there are `m` orbits and the fixed colorings number `k^m = k^(n/2)`.

The contrast with the odd case (a single reflection type, `k^((n+1)/2)`) is the whole point:
for even cycles the reflection count is **not** a single power of `k` — it depends on which
of the two reflection types is used.

## Main results

* `card_vertexInvariant`   — `k^(m+1)` colorings of `ZMod (2m)` invariant under `i ↦ -i`.
* `card_edgeInvariant`     — `k^m`   colorings of `ZMod (2m)` invariant under `i ↦ -1-i`.
* `card_reflectionInvariant_even_vertex` — restated for any even `n` as `k^(n/2 + 1)`.
* `card_reflectionInvariant_even_edge`   — restated for any even `n` as `k^(n/2)`.

Each count is proved by an explicit bijection with the colorings of a fundamental domain,
exactly as in the odd case: a fixed coloring is reconstructed from its values on a set of
orbit representatives by *folding* every position to its representative.

This and `BurnsideCountingOQ05.lean` (odd case) together give the reflection contribution to
Burnside's lemma for the full dihedral necklace count. Absent from Mathlib.
-/

namespace BurnsideCountingOQ05OQ01

variable {k : ℕ}

/-- For `m ≠ 0` the modulus `2m` is also nonzero (needed for `ZMod.val` lemmas). -/
instance neZero_two_mul (m : ℕ) [NeZero m] : NeZero (2 * m) :=
  ⟨by have := NeZero.ne m; omega⟩

/-! ## Type I — vertex-axis reflection `i ↦ -i`

The fixed points of `i ↦ -i` on `ZMod (2m)` are `{0, m}`, so the fundamental domain is
`{0, 1, …, m}`, i.e. `Fin (m+1)`. The development mirrors the odd case verbatim, with
`2m+1` replaced by `2m`. -/

/-- Inclusion of the fundamental domain `{0,…,m}` into the cycle `ZMod (2m)`. -/
def incl1 (m : ℕ) (j : Fin (m + 1)) : ZMod (2 * m) := (j.val : ZMod (2 * m))

/-- Fold a position to its representative in `{0,…,m}` via `i ↦ min(i.val, 2m - i.val)`. -/
def fold1 (m : ℕ) [NeZero m] (i : ZMod (2 * m)) : Fin (m + 1) :=
  ⟨min i.val (2 * m - i.val), by have h := ZMod.val_lt i; omega⟩

theorem fold1_incl1 (m : ℕ) [NeZero m] (j : Fin (m + 1)) : fold1 m (incl1 m j) = j := by
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  have hj : j.val < 2 * m := by have := j.isLt; omega
  apply Fin.ext
  simp only [fold1, incl1, ZMod.val_natCast_of_lt hj]
  have := j.isLt
  omega

theorem fold1_neg (m : ℕ) [NeZero m] (i : ZMod (2 * m)) : fold1 m (-i) = fold1 m i := by
  apply Fin.ext
  simp only [fold1]
  rcases eq_or_ne i 0 with hi | hi
  · subst hi; simp
  · have hv := ZMod.val_lt i
    have hpos : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h0 | h0
      · exact absurd ((ZMod.val_eq_zero i).mp h0) hi
      · exact h0
    rw [ZMod.neg_val, if_neg hi]
    omega

theorem incl1_fold1 (m : ℕ) [NeZero m] (i : ZMod (2 * m)) :
    incl1 m (fold1 m i) = i ∨ incl1 m (fold1 m i) = -i := by
  have hv := ZMod.val_lt i
  rcases le_total i.val (2 * m - i.val) with h | h
  · left
    have hmin : min i.val (2 * m - i.val) = i.val := by omega
    simp only [incl1, fold1, hmin, ZMod.natCast_zmod_val]
  · right
    have hmin : min i.val (2 * m - i.val) = 2 * m - i.val := by omega
    simp only [incl1, fold1, hmin]
    have hle : i.val ≤ 2 * m := le_of_lt hv
    rw [Nat.cast_sub hle, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]

/-- A vertex-reflection-invariant coloring of `ZMod (2m)` is the same data as an arbitrary
coloring of the fundamental domain `Fin (m+1)`. -/
def vertexInvariantEquiv (m k : ℕ) [NeZero m] :
    {c : ZMod (2 * m) → Fin k // ∀ i, c (-i) = c i} ≃ (Fin (m + 1) → Fin k) where
  toFun c j := c.1 (incl1 m j)
  invFun g := ⟨fun i => g (fold1 m i), by
    intro i; show g (fold1 m (-i)) = g (fold1 m i); rw [fold1_neg]⟩
  left_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    funext i
    show c (incl1 m (fold1 m i)) = c i
    rcases incl1_fold1 m i with h | h
    · rw [h]
    · rw [h]; exact hc i
  right_inv := by
    intro g
    funext j
    show g (fold1 m (incl1 m j)) = g j
    rw [fold1_incl1]

/-- **Vertex-axis reflection count.** For `n = 2m`, exactly `k^(m+1)` colorings of the
`n`-cycle are invariant under the vertex reflection `i ↦ -i`. -/
theorem card_vertexInvariant (m k : ℕ) [NeZero m] :
    Fintype.card {c : ZMod (2 * m) → Fin k // ∀ i, c (-i) = c i} = k ^ (m + 1) := by
  rw [Fintype.card_congr (vertexInvariantEquiv m k), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-! ## Type II — edge-axis reflection `i ↦ -1 - i`

This reflection has no fixed points; the fundamental domain is `{0, 1, …, m-1}`, i.e.
`Fin m`. The orbit of `i` is `{i, -1-i}`, paired as `{j, 2m-1-j}`. The key computation is
that `(-1 - i).val = 2m - 1 - i.val`. -/

/-- The edge reflection `i ↦ -1-i` equals the cast of `2m - 1 - i.val`. -/
theorem edge_cast (m : ℕ) [NeZero m] (i : ZMod (2 * m)) :
    ((2 * m - 1 - i.val : ℕ) : ZMod (2 * m)) = -1 - i := by
  have hlt := ZMod.val_lt i
  have step : ((2 * m - 1 - i.val : ℕ) : ZMod (2 * m))
      = ((2 * m : ℕ) : ZMod (2 * m)) - 1 - ((i.val : ℕ) : ZMod (2 * m)) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  rw [step, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]

/-- The `ZMod.val` of the edge reflection. -/
theorem edge_val (m : ℕ) [NeZero m] (i : ZMod (2 * m)) :
    (-1 - i : ZMod (2 * m)).val = 2 * m - 1 - i.val := by
  rw [← edge_cast m i]
  have hlt := ZMod.val_lt i
  exact ZMod.val_natCast_of_lt (by omega)

/-- Inclusion of the fundamental domain `{0,…,m-1}` into the cycle `ZMod (2m)`. -/
def incl2 (m : ℕ) (j : Fin m) : ZMod (2 * m) := (j.val : ZMod (2 * m))

/-- Fold a position to its representative in `{0,…,m-1}` via `i ↦ min(i.val, 2m-1-i.val)`. -/
def fold2 (m : ℕ) [NeZero m] (i : ZMod (2 * m)) : Fin m :=
  ⟨min i.val (2 * m - 1 - i.val), by
    have h := ZMod.val_lt i
    have hm := Nat.pos_of_ne_zero (NeZero.ne m)
    omega⟩

theorem fold2_incl2 (m : ℕ) [NeZero m] (j : Fin m) : fold2 m (incl2 m j) = j := by
  have hj : j.val < 2 * m := by have := j.isLt; omega
  apply Fin.ext
  simp only [fold2, incl2, ZMod.val_natCast_of_lt hj]
  have := j.isLt
  omega

theorem fold2_edge (m : ℕ) [NeZero m] (i : ZMod (2 * m)) :
    fold2 m (-1 - i) = fold2 m i := by
  apply Fin.ext
  simp only [fold2, edge_val]
  have hlt := ZMod.val_lt i
  omega

theorem incl2_fold2 (m : ℕ) [NeZero m] (i : ZMod (2 * m)) :
    incl2 m (fold2 m i) = i ∨ incl2 m (fold2 m i) = -1 - i := by
  have hv := ZMod.val_lt i
  rcases le_total i.val (2 * m - 1 - i.val) with h | h
  · left
    have hmin : min i.val (2 * m - 1 - i.val) = i.val := by omega
    simp only [incl2, fold2, hmin, ZMod.natCast_zmod_val]
  · right
    have hmin : min i.val (2 * m - 1 - i.val) = 2 * m - 1 - i.val := by omega
    simp only [incl2, fold2, hmin]
    exact edge_cast m i

/-- An edge-reflection-invariant coloring of `ZMod (2m)` is the same data as an arbitrary
coloring of the fundamental domain `Fin m`. -/
def edgeInvariantEquiv (m k : ℕ) [NeZero m] :
    {c : ZMod (2 * m) → Fin k // ∀ i, c (-1 - i) = c i} ≃ (Fin m → Fin k) where
  toFun c j := c.1 (incl2 m j)
  invFun g := ⟨fun i => g (fold2 m i), by
    intro i; show g (fold2 m (-1 - i)) = g (fold2 m i); rw [fold2_edge]⟩
  left_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    funext i
    show c (incl2 m (fold2 m i)) = c i
    rcases incl2_fold2 m i with h | h
    · rw [h]
    · rw [h]; exact hc i
  right_inv := by
    intro g
    funext j
    show g (fold2 m (incl2 m j)) = g j
    rw [fold2_incl2]

/-- **Edge-axis reflection count.** For `n = 2m`, exactly `k^m` colorings of the `n`-cycle
are invariant under the edge reflection `i ↦ -1-i`. -/
theorem card_edgeInvariant (m k : ℕ) [NeZero m] :
    Fintype.card {c : ZMod (2 * m) → Fin k // ∀ i, c (-1 - i) = c i} = k ^ m := by
  rw [Fintype.card_congr (edgeInvariantEquiv m k), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-! ## Restatement for an arbitrary even `n` -/

/-- **Vertex reflection, even case.** For any even `n > 0`, the number of `k`-colorings of
the `n`-cycle fixed by a vertex-axis reflection `i ↦ -i` is `k^(n/2 + 1)`. -/
theorem card_reflectionInvariant_even_vertex (n k : ℕ) [NeZero n] (hn : Even n) :
    Fintype.card {c : ZMod n → Fin k // ∀ i, c (-i) = c i} = k ^ (n / 2 + 1) := by
  obtain ⟨m, hm⟩ := hn
  have hn2 : n = 2 * m := by omega
  subst hn2
  haveI : NeZero m := ⟨by have := NeZero.ne (2 * m); omega⟩
  rw [card_vertexInvariant]
  congr 1
  omega

/-- **Edge reflection, even case.** For any even `n > 0`, the number of `k`-colorings of the
`n`-cycle fixed by an edge-axis reflection `i ↦ -1-i` is `k^(n/2)`. -/
theorem card_reflectionInvariant_even_edge (n k : ℕ) [NeZero n] (hn : Even n) :
    Fintype.card {c : ZMod n → Fin k // ∀ i, c (-1 - i) = c i} = k ^ (n / 2) := by
  obtain ⟨m, hm⟩ := hn
  have hn2 : n = 2 * m := by omega
  subst hn2
  haveI : NeZero m := ⟨by have := NeZero.ne (2 * m); omega⟩
  rw [card_edgeInvariant]
  congr 1
  omega

/-- **The two reflection types differ.** For `n = 2m` with `m ≥ 1` and at least two colors,
the vertex-axis reflection fixes strictly more colorings than the edge-axis reflection:
`k^m < k^(m+1)`. This is the structural contrast with the odd case (one reflection type). -/
theorem vertex_gt_edge (m k : ℕ) [NeZero m] (hk : 2 ≤ k) :
    Fintype.card {c : ZMod (2 * m) → Fin k // ∀ i, c (-1 - i) = c i}
      < Fintype.card {c : ZMod (2 * m) → Fin k // ∀ i, c (-i) = c i} := by
  rw [card_vertexInvariant, card_edgeInvariant]
  have hpos : 0 < k ^ m := pow_pos (by omega) m
  calc k ^ m < k ^ m * k := (lt_mul_iff_one_lt_right hpos).mpr (by omega)
    _ = k ^ (m + 1) := (pow_succ k m).symm

end BurnsideCountingOQ05OQ01
