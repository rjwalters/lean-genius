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

## Session 2026-07-20 (researcher-1) — multiplicative scaling engine

**Mode**: build on prior scaffolding (splitting/lengthening toolkit). **Outcome**: progress
— 2 axiom-free theorems, **host-verified v4.31** (`lake env lean`, exit 0; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on both new theorems, no sorry/native_decide).

Added the *multiplicative* counterpart of the existing additive `isRatFractionRepr_union`:

- `isRatFractionRepr_smul` — scaling every denominator by `t ≥ 1` (the injective map
  `n ↦ t·n`) sends a representation of `q` to a representation of `q/t`, with every new
  denominator `≥ 2t`. Proof: `Finset.sum_image` with pairwise-injectivity from
  `Nat.eq_of_mul_eq_mul_left`, then `1/(t·n) = (1/t)(1/n)` (`push_cast`, `mul_inv`) and
  `← Finset.mul_sum`, closed by `ring`.
- `exists_isRatFractionRepr_inv_min_ge` — `{2t, 3t, 6t}` represents `1/t` with min denom
  `≥ 2t` (scale the concrete `{2,3,6}`). The large-denominator regime is reachable for
  reciprocals of arbitrary size.

### The disjoint-chaining obstruction (analyzed)
The remaining blocker toward `ErdosProblem46_infinitely_many` is **collision-freeness**, not
arithmetic:
- Splitting the *largest* denominator (existing `exists_isUnitFractionRepr_card_ge` engine)
  leaves the small head `{2,3}` fixed, so consecutive reprs are never disjoint.
- Scaling a whole repr of 1 by a factor gives a repr of `1/t` (not 1); assembling several
  scaled sub-reprs of a fixed decomposition `1 = ∑ 1/mᵢ` back into a repr of 1 produces
  cross-copy denominator collisions (e.g. `2·{2,3,6} ∪ 3·{2,3,6}` shares `6`).
- A repr of 1 with all denominators `> N` would immediately yield infinitely many
  pairwise-disjoint reprs (chain `Nᵢ₊₁ = max Sᵢ`), but constructing one needs exact
  collision bookkeeping (a coprimality/valuation argument on the scale factors), still open.
