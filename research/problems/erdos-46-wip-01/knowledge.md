# Knowledge Base: erdos-46-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-20 (researcher-1) — develop the def-only stub (13 axiom-free lemmas)

**Mode**: FRESH (knowledge score 0). **Outcome**: progress — 13 axiom-free foundational
lemmas, **host-verified v4.31** (`lake env lean`, exit 0, `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on a spot-check of 4).

Erdős Problem 46 (Croot): every finite colouring of ℕ has a monochromatic `S` with
`∑_{n∈S} 1/n = 1`. `Erdos46Problem.lean` held only defs (`IsUnitFractionRepr`,
`IsRatFractionRepr`, `FiniteColouring`, `IsMonochromatic`, the three headline Props) plus
3 trivial lemmas. Filled the two `TODO` comments (singleton exclusion, ≥2 elements) and
added structural infrastructure:

- `not_isUnitFractionRepr_singleton` — `1/n = 1` fails for `n ≥ 2` (`div_lt_one`).
- `two_le_card_of_isUnitFractionRepr` — card ≠ 0 (empty sums 0) and ≠ 1 (singleton < 1),
  so `2 ≤ card` (via `card_eq_zero` / `card_eq_one` + `omega`).
- `term_le_half`, `sum_inv_nonneg`, `pos_of_mem_isUnitFractionRepr`,
  `isRatFractionRepr_pos`, `isRatFractionRepr_unique`, `isRatFractionRepr_one_iff`,
  `forall_two_le_of_subset`.
- `isRatFractionRepr_union` — reciprocal-sum representations add over **disjoint** unions
  (`Finset.sum_union`); the arithmetic backbone for assembling disjoint monochromatic
  solutions (the "infinitely many disjoint" strengthening).
- `isMonochromatic_empty` (needs `0 < r`), `isMonochromatic_singleton`.
- `erdosProblem46_of_infinitely_many` — the base statement reduces to the
  infinitely-many-disjoint version by instantiating the threshold `N = 0`.

### v4.31 gotchas
- `div_le_div_iff` unknown → use `one_div_le_one_div_of_le (0<a) (a≤b) : 1/b ≤ 1/a`.
- `Finset.not_mem_empty` unknown as a term here → discharge empty membership with
  `by simp at hn`.

### Still open
Croot's theorem itself (2003, existence of the monochromatic representation) is deep and
unformalized — needs the density/covering machinery from the paper. This session builds
only the elementary scaffolding around the statement.

## Session 2026-07-21 (researcher-1) — splitting identity + concrete witness + lengthening step

**Mode**: build on #39650 scaffolding. **Outcome**: progress — 5 axiom-free theorems in
`Erdos46Problem.lean` (theoremCount 16→21), host-verified v4.31 (`lake env lean`, exit 0,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on all 5).

Adds the elementary *construction* machinery the prior session's structural lemmas lacked:

- `inv_mul_succ (n≥1)` — telescoping `1/(n(n+1)) = 1/n − 1/(n+1)` (`field_simp; ring`).
- `split_unit_fraction (n≥1)` — the **Fibonacci–Sylvester splitting identity**
  `1/n = 1/(n+1) + 1/(n(n+1))`: one reciprocal splits into two strictly larger ones with
  equal sum. The engine for lengthening representations.
- `isUnitFractionRepr_two_three_six` — concrete witness `IsUnitFractionRepr {2,3,6}`
  (`1/2+1/3+1/6 = 1`; `decide` for the ≥2 side, `norm_num [Finset.sum_insert,…]` for the sum).
- `exists_isUnitFractionRepr` — the representation set is inhabited.
- `isUnitFractionRepr_replace` — **the induction step**: from any representation `S ∋ m`,
  if `m+1, m(m+1) ∉ S`, replacing `m` by `{m+1, m(m+1)}` gives another representation of 1.
  Proof: `sum_insert` ×2 + `add_sum_erase` (∑ over `S.erase m` = `1 − 1/m`) + the split
  identity, closed by `linarith`. This is the elementary path toward arbitrarily long /
  infinitely many disjoint monochromatic representations (`ErdosProblem46_infinitely_many`).

### v4.31 gotchas
- `split_unit_fraction`'s `1/(n+1)` elaborates in ℚ as `1/((n:ℚ)+1)` (cast-then-add), so
  after `Finset.sum_insert` the goal's `1/((m+1:ℕ):ℚ)` needs `push_cast` bridges
  (`((m+1:ℕ):ℚ) = (m:ℚ)+1`) via a `simp only [hcast1,hcast2]` before `linarith [hsplit]`.
- `Finset.add_sum_erase S f hm : f m + ∑_{S.erase m} f = ∑_S f` — rewrite `hsum` in it, then
  `linarith` to isolate the erase-sum.

### Still open (UNCHANGED)
Croot's theorem itself (existence of the monochromatic representation) remains deep and
unformalized — needs the density/covering machinery from the 2003 paper. This session
supplies only the elementary splitting/lengthening toolkit around the statement.
