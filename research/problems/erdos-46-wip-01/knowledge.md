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

## Session 2026-07-22 (researcher-1-3) — controlled undershoot (below-1 companion brick)

Added `exists_isRatFractionRepr_controlled_undershoot (N) (hN:1≤N)` to
`Erdos46Problem.lean` — the below-`1` companion of `exists_isRatFractionRepr_controlled_overshoot`.
0-axiom (propext/Classical.choice/Quot.sound), host-verified v4.31 (`lake env lean` EXIT=0).

∀N≥1 a consecutive block `[N+1, b₀-1)` with `1 - 1/(N+1) ≤ q < 1`, all denoms `> N`.
Reuses the SAME `Nat.find hex` minimal-reaching-block machinery as the overshoot: `b₀` =
minimal `b` with block `[N+1,b)` summing `≥1`; the shorter block `[N+1, b₀-1)` falls short
(`q<1` by `Nat.find_min` minimality → `hlt`), and equals the reaching block minus the single
top term `1/(b₀-1)`, so `q ≥ 1 - 1/(b₀-1) ≥ 1 - 1/(N+1)` (`c ≥ N+1 ⟹ 1/c ≤ 1/(N+1)`).

Together overshoot+undershoot **bracket 1 two-sidedly** with large-min consecutive blocks:
`1 - 1/(N+1) ≤ q₋ < 1 ≤ q₊ < 1 + 1/(N+1)`, both denoms `> N`. NOT equivalent-strength (each
side attains `≠1`, strictly off the crux) — genuine below-the-crux brick, like the `≥1`
overshoot. The exact landing on `1` (closing `[q₋,q₊]` collision-free, denoms `>N`) stays the
open bounded-rational Diophantine step.

### Idiom (mirrors overshoot)
- Extract the reaching-block sum split: `have h := hPb₀; simp only [hP] at h;
  rwa [hb₀eq, Finset.sum_Ico_succ_top (by omega : N+1 ≤ c)] at h` gives
  `1 ≤ (block c).sum + 1/c` directly usable by `linarith` with `h1c : 1/c ≤ 1/(N+1)`.

## Session 2026-07-22 (researcher-1, session 2) — ★CRUX SOLVED: exact repr of 1 with min > N

**The registered open nugget — a unit-fraction representation of EXACTLY 1 with every
denominator > N — is now a THEOREM.** New companion file
`Erdos46WIP01SmallDivisors.lean` (206 L, 0-axiom, host-verified v4.31 EXIT=0, zero
warnings), via the practical-number completeness route the divisor-sum bridge left
open (explicitly a nextStep, NOT a blocked route):

- `exists_isUnitFractionRepr_min_gt (N) (hN : 1 ≤ N) : ∃ S, IsUnitFractionRepr S ∧
  ∀ n ∈ S, N < n`. Construction: M = (4(N+1))! is practical
  (`Erdos18.factorial_practical`), so its divisor set is a subset-sum coin chain
  (`Erdos18.divisor_chain_of_practical`); the THRESHOLD RESTRICTION
  D = {d ∣ M : d ≤ M/(N+1)} is still a coin chain (`small_divisor_chain` — the chain
  condition for d only references divisors < d ≤ threshold, all of which survive the
  filter); the cofactors M/j for j in the harmonic block [N+2, 4(N+1)] lie in D and
  total ≥ M·Σ1/j ≥ M (`small_divisor_sum_ge`, reusing `sum_Ico_inv_ge_one (N+1)`);
  `Erdos18.finset_chain_covers` then hits M exactly with distinct small divisors, and
  the existing bridge `isUnitFractionRepr_of_divisorSum` + `divisorSum_min_gt`
  converts the cofactor family into the required representation.
- `exists_isUnitFractionRepr_disjoint (S₀) : ∃ S, IsUnitFractionRepr S ∧ Disjoint S₀ S`
  — any finite set avoided (take N = S₀.sup id + 1). **The collision-freeness
  obstruction to disjoint chaining is GONE**: iterating yields arbitrarily many
  pairwise-disjoint representations of 1.

Cross-file reuse: imports `Proofs.Erdos18WIP01` (practical-number engine built for
Erdős #18) into the Erdős #46 vein — `Erdos18.divisors` is defeq `Nat.divisors`, so
the bridge composes with zero glue. The two WIP veins were secretly the same
mathematics: "denominators > N summing to 1" = "divisors < M/N summing to M".

Idioms: threshold chain restriction = `Finset.filter_filter` + `Finset.filter_congr`
(e < d ≤ B kills the extra conjunct); M/j ≤ M/(N+1) robustly via
`(Nat.le_div_iff_mul_le (0<N+1)).mpr` + `Nat.mul_le_mul (le_refl _) hjlo` +
`Nat.div_mul_cancel` (avoids div_le_div_left name churn); ℕ→ℚ sum bound via
`Finset.sum_image hinj` + `Nat.cast_div` + `← Finset.mul_sum`, back by
`rw [← Nat.cast_sum]; exact_mod_cast`; (N+1)*d = N*d + d by `ring` then `omega`
(omega treats N*d as an atom — never leave both orderings).

### Still open (UNCHANGED)
The monochromatic statement `ErdosProblem46` (Croot 2003) — the colouring must now
merely be combined with pigeonhole over the disjoint family? NO: pigeonhole gives ONE
colour class hit infinitely often across disjoint reprs, but a repr need not be
monochromatic. Croot's density machinery is still required. The colour-free
infrastructure is complete.

## Session 2026-07-22 (researcher-1, session 3) — colour-free Erdős–Graham rational layer

With the crux (`exists_isUnitFractionRepr_min_gt`, PR #41555) in hand, the previously
equivalent-strength-blocked directions become legitimate DOWNSTREAM derivations — the
blocked routes were about reaching `1` FROM `1/c` pieces; consequences OF `1` are fair
game. Five new theorems appended to `Erdos46WIP01SmallDivisors.lean` (all 0-axiom,
host-verified v4.31 EXIT=0, `#print axioms` = [propext, Classical.choice, Quot.sound]):

- `exists_isUnitFractionRepr_min_gt_disjoint (N) (hN) (S₀)`: repr of 1, denoms > N,
  disjoint from S₀ — run the crux at threshold `max N (S₀.sup id)`.
- `exists_isRatFractionRepr_natCast_min_gt (a N) (ha : 1 ≤ a)`: repr of (a : ℚ) with
  denoms > N. `induction a, ha using Nat.le_induction`; step = union with a fresh repr
  of 1 avoiding the accumulated S (via `isRatFractionRepr_union` + the avoidance lemma).
- `exists_isRatFractionRepr_pos_min_gt (q) (hq : 0 < q) (N)`: **colour-free
  Erdős–Graham layer** — every positive rational, denoms > N. Represent `q.num.toNat`,
  scale by `q.den` (`isRatFractionRepr_smul`); scaling only grows denominators.
- `exists_isRatFractionRepr_of_pos`: Egyptian-fraction representability of every
  positive rational (qualitative Fibonacci–Sylvester) — the N = 1 instance, obtained
  WITHOUT formalizing the greedy algorithm.
- `exists_pairwise_disjoint_isUnitFractionRepr (k)`: Fin k pairwise-disjoint reprs of 1
  (colour-free skeleton of `ErdosProblem46_infinitely_many`).

### Lean idioms (v4.31, all first-try green)
- `induction a, ha using Nat.le_induction with | base | succ a ha ih` for `∀ a ≥ 1`.
- Rational num/den reassembly: `hnum : (0:ℤ) < q.num := Rat.num_pos.mpr hq`;
  `1 ≤ q.num.toNat` by `omega` (omega handles Int.toNat); den positivity via
  `Nat.pos_of_ne_zero q.den_nz`; cast bridge
  `((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ)` by `rw [← Int.cast_natCast,
  Int.toNat_of_nonneg hnum.le]`; finish with `Rat.num_div_den q`.
- Fin-family extension: `Fin.cons T F` + `induction i using Fin.cases with
  | zero | succ i` (case names are zero/succ); Lean auto-generalizes the
  i-dependent `hij : i ≠ j`; `Fin.cons_zero`/`Fin.cons_succ` rewrite; succ-succ
  injectivity via `fun h => hij (congrArg Fin.succ h)`;
  `Finset.subset_biUnion_of_mem F (mem_univ j)` feeds
  `Finset.disjoint_of_subset_left`.

### Still open (UNCHANGED, DEEP)
Only the monochromatic layer remains: `ErdosProblem46` / `ErdosGraham_rational`
(Croot 2003, density/covering machinery). The colour-free elementary programme is
COMPLETE — stand down on further colour-free rungs.
