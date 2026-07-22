# Knowledge Base: erdos-326-wip-01

## Session 2026-07-21 (researcher-1) — two-subsequence non-convergence criterion

Added `hasNoGrowthLimit_of_two_subseq_limits` to `Erdos326WIP01.lean` (1 thm, 0 ax,
0 sorry, host-verified v4.31.0 fresh-parent-olean; `#print axioms` =
propext/Classical.choice/Quot.sound). The **reusable engine** for the OPEN oscillation
direction of #326: if the growth ratio along two strictly-monotone index subsequences
`φ, ψ` tends to distinct limits `L ≠ L'`, then `HasNoGrowthLimit b`.

- Proof: a growth limit `x` forces both subsequences to `x`
  (`hx.comp hφ.tendsto_atTop` — a subsequence of a convergent sequence shares its limit,
  `StrictMono.tendsto_atTop` cofinality), so `tendsto_nhds_unique` gives `L = x = L'`,
  contradicting `hLL'`.
- This generalizes the ad-hoc `hasNoGrowthLimit_oscillating` (whose odd/even subsequences
  hit `2` and `1`); any future sub-basis construction proving non-convergence consumes it.

### Idioms
- Subsequence-shares-limit: `hx.comp hφ.tendsto_atTop` where `hφ : StrictMono φ`
  (`StrictMono.tendsto_atTop : Tendsto φ atTop atTop` for `φ : ℕ → ℕ`).
- `tendsto_nhds_unique e1 e2 : x = y` (ℝ is T2, `atTop` NeBot).

### Remaining open (unchanged)
- Constructing, for an arbitrary order-2 basis `A`, a sub-basis `B ⊆ A` whose ratio
  oscillates (two subsequential limits) — the deep OPEN core of #326. The criterion above
  is the final step of any such construction; the construction itself is the hard part.

## Session 2026-07-21 (researcher-1) — `bₖ = O(k²)` as `growthRatio` boundedness (bridge)

Closed the standing "bridge `bₖ=O(k²)` to `growthRatio` boundedness" open item. Added
3 axiom-free theorems to `Erdos326WIP01.lean` (host-verified v4.31.0 via fresh-parent-olean;
`#print axioms` = propext/Classical.choice/Quot.sound on all three). Until now `growthRatio`
was only ever applied to *toy* sequences (`c·k²`, `oscillating`); these are the first results
tying it to the **actual order-2-basis enumeration** `bₖ = Nat.nth (· ∈ A) k`:

- `IsAddBasisOfOrder.two_growthRatio_le` — `∃ C N₀, ∀ k ≥ N₀, growthRatio (Nat.nth (·∈A)) k ≤ C`.
  Direct `growthRatio` restatement of `two_nth_le_mul_sq` (`bₖ ≤ C·k²`): unfold, `div_le_iff₀`
  on `(k:ℝ)^2>0` (threshold `max N₀ 1` guarantees `k≥1`), then `exact_mod_cast` the ℕ bound.
- `IsAddBasisOfOrder.two_growthRatio_mem_Icc` — eventually `growthRatio ∈ Icc 0 C` (pairs the
  above with `growthRatio_nonneg`).
- `IsAddBasisOfOrder.two_growthRatio_bddAbove` — `BddAbove (Set.range (growthRatio (Nat.nth (·∈A))))`.
  Removes the eventual-threshold: the finite prefix `k<N₀` is absorbed by the **nonnegative**
  bound `C + ∑_{j<N₀} growthRatio b j` (`Finset.single_le_sum` for `k<N₀`, `hC` for `k≥N₀`).
  This is `bₖ=O(k²)` as literal boundedness of the ratio sequence.

Still touches nothing of the non-convergence (oscillation) direction — the OPEN part of #326.

### Gotchas
- `le_or_lt` does NOT resolve as a bare identifier in v4.31 (unknown identifier) — use
  `Nat.lt_or_ge k N₀ : k < N₀ ∨ k ≥ N₀` (and swap case order) for the prefix/tail split.
- `div_le_iff` is deprecated → use `div_le_iff₀ (h : 0 < c) : a/c ≤ b ↔ a ≤ b*c`.
- Same fresh-parent-olean host-verify recipe (parent `Erdos326Problem.lean` Mathlib-only →
  `lake env lean -o .lake/build/lib/lean/Proofs/Erdos326Problem.olean` first).

### Remaining open (unchanged)
- The oscillation dichotomy — must every order-2 basis contain a sub-basis with `bₖ/k²`
  non-convergent — the OPEN part of #326 (structured blocker, deep). The boundedness above
  says the ratio lives in a compact `[0,C]` but says nothing about (non-)convergence within it.

## Session 2026-07-21 (researcher-1-6) — growth-limit predicates are non-vacuous (realizability)

Added 5 axiom-free theorems + 1 def to `Erdos326WIP01.lean` (host-verified v4.31.0
via fresh-parent-olean; `#print axioms` = propext/Classical.choice/Quot.sound on all
new results; theoremCount 20→25):

- `growthRatio_eq (b c k) (hk : k≠0) (hval : b k = c*k^2) : growthRatio b k = c` —
  the reusable "value pins the ratio" lemma (`div_eq_iff (pow_ne_zero 2 …)` + `push_cast; ring`).
- `hasGrowthLimit_quadratic (c) : HasGrowthLimit (fun k => c*k^2) c` — an exactly-quadratic
  enumeration converges (eventually constant `=ᶠ`, `tendsto_const_nhds.congr'`). Positive
  realizability of `HasGrowthLimit` (the Cassels-flavour convergent case, for a bare sequence).
- `oscillating k := (k%2+1)*k^2` — ratio `2` on odds, `1` on evens
  (`growthRatio_oscillating_odd/even`, both via `growthRatio_eq` after `rw [show …%2=… from by omega]`).
- `hasNoGrowthLimit_oscillating : HasNoGrowthLimit oscillating` — NON-vacuous `HasNoGrowthLimit`.
  Both index maps `2m+1`, `2m+2` tend to `atTop` (`tendsto_atTop_atTop.mpr fun b => ⟨b, …omega⟩`),
  compose with the hypothetical limit (`hx.comp`), collapse each to a constant via the odd/even
  ratio lemma, then `tendsto_nhds_unique` twice forces `x=2` AND `x=1` → `norm_num`.

This is exactly the `bₖ/k²`-non-convergence phenomenon Erdős #326 conjectures for a
*sub-basis* — realized here for a plain sequence (no basis constraint); the deep sub-basis
oscillation dichotomy is untouched.

### Gotchas
- A `∀ᶠ k, f k = g k` hypothesis must be *typed* as `f =ᶠ[atTop] g` (EventuallyEq) for
  `.symm`/`.congr'` dot-notation to resolve — the bare `∀ᶠ` (Filter.Eventually) head symbol
  blocks the field projection (`Invalid field notation … atTop.1 {x | …}`).
- `rw [show (2*m+1)%2 = 1 from by omega]` then the goal `(1+1)*…=2*…` closes by `rw`'s trailing
  `rfl` (Nat literal `1+1` reduces to `2`); a following `ring` errors "No goals".
- Same fresh-parent-olean host-verify recipe as prior sessions (parent Mathlib-only →
  `lake env lean -o .lake/build/lib/lean/Proofs/Erdos326Problem.olean` first).

### Remaining open (unchanged)
- Bridge `HasGrowthLimit` to explicit enumeration boundedness (`bₖ=O(k²)` as growthRatio boundedness).
- The oscillation dichotomy — must every order-2 basis contain a sub-basis with `bₖ/k²`
  non-convergent — the OPEN part of #326 (structured blocker, deep).

## Session 2026-07-20 (researcher-1) — squares are NOT an order-3 basis (order = exactly 4)

Added 3 axiom-free lemmas to `Erdos326WIP01.lean` (host-verified v4.31.0 via fresh-parent-olean;
`#print axioms` = propext/Classical.choice/Quot.sound; theoremCount 15→18):

- `mem_squares_mod_eight` — every square is `0/1/4 (mod 8)` (`∀ x:ZMod 8, x^2 ∈ {0,1,4}` by `decide`).
- `not_isAddBasisOfOrder_squares_three` — the squares are NOT an order-3 additive basis. Pick
  `n = 8N+7 ≥ N`; it must be a sum of `≤3` squares, but mod 8 each square is `0/1/4` and no `≤3`
  of those sum to `7`. `interval_cases m` (m∈{0,1,2,3}) + `Fin.sum_univ_*` + `rcases`×3 + `decide`.
- `not_isAddBasisOfOrder_squares_of_le_three` — via `mono_order`, no order `≤3`; combined with
  `isAddBasisOfOrder_squares_four` the basis order of the squares is EXACTLY 4 (sharp).

Only the EASY direction of Legendre's three-square theorem is used (necessary condition mod 8);
the full theorem (`n ≠ 4^a(8b+7) ⟺ sum of 3 squares`) is not needed and is deep.

### Gotchas
- `((8*N+7:ℕ):ZMod 8) = 7`: `push_cast` then `rw [show (8:ZMod 8)=0 from by decide]; ring`.
- Cast the sum with `Nat.cast_sum`; work with `(f i : ZMod 8)` throughout.
- Host-verify: parent `Erdos326Problem.lean` is Mathlib-only → `mkdir -p .lake/build/lib/lean/Proofs`
  then `lake env lean -o .../Proofs/Erdos326Problem.olean` before compiling the child (no Docker).

### Remaining open
- `b_k = O(k^2)` upper bound for order-2 bases; `HasGrowthLimit` ↔ enumeration boundedness.
- Full Legendre three-square (converse) — deep, check Mathlib.

## Session 2026-07-20 (researcher-1) — order-2 bases are quadratically dense (Key Observation 1)

**Mode**: continue. **Outcome**: progress — host-verified, axiom-free, no Docker.

Formalized the parent's *Key Observation 1* (`Erdos326Problem`: "any order-2 basis
must have density ≥ O(√n) ⟹ bₖ = O(k²)"), previously prose-only. Added to
`Erdos326WIP01.lean` (theoremCount 18→20):

- `IsAddBasisOfOrder.two_quadratic_density` — for an order-2 basis `A`, `∃ N`,
  `∀ n ≥ N`, `∃` finite `S ⊆ A` of elements `≤ n` with
  `|Finset.Icc N n| ≤ (|S| + 1)²`.
- `IsAddBasisOfOrder.two_quadratic_density'` — the counting-function form
  `n + 1 − N ≤ (|S| + 1)²` (i.e. `|S| ≥ √(n+1−N) − 1`).

Both `#print axioms` = `[propext, Classical.choice, Quot.sound]` (axiom-free).

**Proof idea.** Every `m ∈ [N,n]` is a sum of `≤ 2` elements of `A`, each `≤ m ≤ n`.
Pad to an ordered pair `(aₘ, bₘ)` with `aₘ + bₘ = m`, `aₘ, bₘ ∈ A ∪ {0}` (via
`choose!` on a per-`m` existence lemma; `interval_cases k` on the `≤ 2` summand
count). Since the sum recovers `m`, `m ↦ (aₘ, bₘ)` is injective on `[N,n]`
(`Finset.card_le_card_of_injOn`, `omega`), so `[N,n]` injects into `(S ∪ {0})²`
where `S = T.erase 0` collects the nonzero coordinates. Hence
`|Icc N n| ≤ T.card² = (|S|+1)²` (`Finset.card_erase_add_one`, `Finset.card_product`).

### Gotchas
- `Finset.card_le_card_of_injOn`'s `hf`/`InjOn` goals use **Set-coe** membership
  (`m ∈ ↑s`), so `rw [Finset.mem_coe, Finset.mem_Icc]` / `[Finset.mem_coe,
  Finset.mem_product]` — a bare `Finset.mem_Icc` rewrite fails.
- Host-verify: parent `Erdos326Problem.lean` is Mathlib-only → build its olean
  fresh (`lake env lean -o .lake/build/lib/lean/Proofs/Erdos326Problem.olean`)
  before compiling the child; the shipped pre-v4.31 olean is header-incompatible.

### Remaining open (unchanged)
- The oscillation dichotomy — must every order-2 basis contain a sub-basis with
  `bₖ/k²` non-convergent — the OPEN part of #326 (structured blocker). The density
  bound above controls `bₖ` from above but says nothing about non-convergence.
- `HasGrowthLimit`/`HasNoGrowthLimit` bridge to explicit enumeration boundedness.

## Session 2026-07-21 (researcher-1-4): b_k = O(k²) upper bound

Turned the √n density (Key Observation 1) into the standard **b_k = O(k²)**
growth upper bound for the increasing enumeration `b_k = Nat.nth (· ∈ A) k`:

- `IsAddBasisOfOrder.two_nth_le_quadratic` — `∃ N, ∀ k, Nat.nth (· ∈ A) k ≤ N + (k+1)²`.
- `IsAddBasisOfOrder.two_nth_le_mul_sq` — `∃ C N₀, ∀ k ≥ N₀, Nat.nth (· ∈ A) k ≤ C·k²`
  (with `C = N+4`, `N₀ = 1`).

Both 0-axiom (propext/Classical.choice/Quot.sound), host-verified v4.31.0.

**Mechanism.** Take `n := N + (k+1)²`. The density form `n+1−N ≤ (|S|+1)²`
(`two_quadratic_density'`) reads `(k+1)²+1 ≤ (|S|+1)²`, forcing `k < |S|`
(via `Nat.pow_le_pow_left` contrapositive + `omega`). Since `S ⊆ A` with all
elements `≤ n`, `S ⊆ (range (n+1)).filter (· ∈ A)`, so
`k < |S| ≤ Nat.count (· ∈ A) (n+1)` (`Nat.count_eq_card_filter_range`,
`Finset.card_le_card`). Then `Nat.nth_lt_of_lt_count` gives
`Nat.nth (· ∈ A) k < n+1`, i.e. `≤ n`. No infiniteness needed.

**Idioms.** `Nat.nth_lt_of_lt_count : k < count p n → nth p k < n` is the exact
count↔nth bridge (no `Infinite` hypothesis). `nlinarith [hk]` closes
`(k+1)² ≤ 4k²` and `N ≤ N·k²` for `k ≥ 1`; then `omega` (atoms `(k+1)²`, `k²`,
`N·k²`) + `ring` finish the `≤ (N+4)k²` calc.

The elementary density/growth-upper-bound layer is now **saturated**; only the
deep oscillation dichotomy remains open.

## Session 2026-07-21 (researcher-1) — tail-invariance + sub-quadratic ⟹ limit 0

Added 3 axiom-free theorems to `Erdos326WIP01.lean` (host-verified v4.31.0 via
fresh-parent-olean; `#print axioms` = propext/Classical.choice/Quot.sound on all three;
theoremCount → 34 `theorem`/`lemma` decls). Fleshes out the growth-limit *spectrum*
complementing the existing convergent (`hasGrowthLimit_quadratic`, limit `c`) and
non-convergent (`hasNoGrowthLimit_oscillating`) examples:

- `hasGrowthLimit_congr' {b b'} (h : b =ᶠ[atTop] b') : HasGrowthLimit b x ↔ HasGrowthLimit b' x`
  — the growth limit is a **tail invariant**. Proof: `b =ᶠ b'` ⟹ `growthRatio b =ᶠ growthRatio b'`
  (`filter_upwards … simp [growthRatio, hk]`), then `Tendsto.congr'` both ways. This is the
  prerequisite that modifying a basis on a finite prefix cannot change its `bₖ/k²` limit — needed
  by any future sub-basis construction.
- `hasGrowthLimit_zero_of_linear_bound (b C) (h : ∀ k, b k ≤ C*k) : HasGrowthLimit b 0`
  — a **sub-quadratically** enumerated sequence converges to 0. Proof: `growthRatio b k ≤ C/k`
  (gcongr on numerator `b k ≤ C·k`, then `mul_div_mul_right` to collapse `C·k/k² = C/k`), squeeze
  between `growthRatio_nonneg` and `tendsto_const_div_atTop_nhds_zero_nat`.
- `hasGrowthLimit_id_zero : HasGrowthLimit (fun k => k) 0` — concrete order-1 witness (identity
  enumeration bₖ=k, ℕ itself is an order-1 basis). Sits at the `0` end of the growth spectrum.

**Take-away for the OPEN direction:** genuine non-convergence à la #326 can only arise from
honestly quadratic growth — the ratio cannot oscillate/diverge while the numerator stays `o(k²)`.

### Idioms / gotchas
- `div_le_div_iff` is GONE (unknown identifier) in v4.31 — do the numerator comparison with `gcongr`
  and collapse the fraction with `mul_div_mul_right a b (hc : c ≠ 0) : a*c/(b*c) = a/b`
  (after `rw [pow_two]`) instead of a single cross-multiply lemma.
- `tendsto_const_div_atTop_nhds_zero_nat (C : ℝ) : Tendsto (fun n : ℕ => C/n) atTop (𝓝 0)` exists —
  the clean base for squeeze-to-zero of `k`-indexed ratios.
- Same fresh-parent-olean host-verify recipe: `lake env lean -o …/Proofs/Erdos326Problem.olean
  Proofs/Erdos326Problem.lean` first (parent is Mathlib-only), then `lake env lean Proofs/Erdos326WIP01.lean`.

### Remaining open (unchanged)
- The subset-basis oscillation dichotomy (deep, structured blocker: materially new mechanism required).

## Session 2026-07-22 (researcher-1-3) — squeeze criterion (convergent-direction engine)

Added 3 axiom-free decls to `Erdos326WIP01.lean` (host-verified v4.31.0 via
fresh-parent-olean; `#print axioms` = propext/Classical.choice/Quot.sound on all
three). The **convergent-direction companion** of the existing non-convergence
engine `hasNoGrowthLimit_of_two_subseq_limits`:

- `growthRatio_mono {a b k} (h : a k ≤ b k) : growthRatio a k ≤ growthRatio b k` —
  ratio monotone in the numerator (cast `a k ≤ b k` to ℝ, `unfold growthRatio; gcongr`
  handles division by the nonneg `k²`). Reusable pointwise comparison.
- `hasGrowthLimit_of_le_of_le {a b c x} (hab : ∀ᶠ k, a k ≤ b k) (hbc : ∀ᶠ k, b k ≤ c k)
  (ha : HasGrowthLimit a x) (hc : HasGrowthLimit c x) : HasGrowthLimit b x` — the
  squeeze. `filter_upwards` the two eventual `≤` through `growthRatio_mono`, then
  `tendsto_of_tendsto_of_tendsto_of_le_of_le' ha hc e1 e2` traps `growthRatio b`.
  Directly serves the OPEN direction: a sub-basis enumeration is pointwise squeezed
  by controlling sequences; same quadratic coefficient top and bottom ⟹ it converges.
- `hasGrowthLimit_of_between_quadratic (b c) (hlo : ∀ᶠ k, c*k² ≤ b k)
  (hhi : ∀ᶠ k, b k ≤ c*k²) : HasGrowthLimit b c` — concrete instance against the
  exactly-quadratic witnesses `hasGrowthLimit_quadratic c` on both sides.

### Idioms
- Growth-ratio numerator comparison: `exact_mod_cast h` (ℕ `≤` → ℝ `≤`), `unfold
  growthRatio; gcongr` — `gcongr` discharges `x/k² ≤ y/k²` from `x ≤ y` with nonneg denom.
- `tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh hgf hfh` is the eventual-`≤`
  squeeze (bounds converge to same limit, `∀ᶠ` inequalities) — cleaner than `squeeze_zero`
  when the common limit is a general `x` (not `0`).

### Remaining open (unchanged)
- The subset-basis oscillation dichotomy — deep structured blocker; both the
  non-convergence engine and this squeeze engine are the *final steps* of any such
  construction, the construction itself is the hard part.
