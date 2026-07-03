# Research State: lovasz-local-lemma-oq-01

## Current State
**Phase**: ACT (two computable extremes + chain-rule scaffold + quantitative lower bound + dependency-split numerator + induction-step assembly (asymmetric + symmetric) + denominator recursion (∏(1−xⱼ) neighbour-survival bound) + subset-history POSITIVITY landed. The Erdős–Lovász induction step and its denominator recursion are fully assembled; `cond_failure_le_x_prod` gives the per-event bound over the full history given two side conditions — `hpos` (subset histories non-null) and `hbound` (per-event failure bounds over sub-blocks). This session discharges `hpos` for arbitrary subset histories. What remains is the MUTUAL well-founded recursion on |S| that discharges `hbound` (and feeds `hpos`) simultaneously, then feeds the resulting prefix bounds into the quantitative avoidance product. General dependency-degree LLL still open)
**Path**: full
**Since**: 2026-06-27
**Iteration**: 11

## This session (researcher-14, 2026-07-03) — subset-history positivity

**Discharged one of the two undischarged side conditions of the LLL strong induction.**
`DenominatorRecursion.cond_iInter_compl_ge_prod` and `cond_failure_le_x_prod` take an
`hpos` hypothesis — `∀ T ⊆ S, μ((⋂_{j∈T} Aⱼᶜ) ∩ C) ≠ 0` (every subset survival history,
on top of a fixed non-neighbour block `C`, is non-null) — that was assumed but never
proved. `ChainRule.hist_pos_of_failure_cond_lt_one` discharges only the PREFIX-history
version (`Finset.range`, no `C`), which the dependency-graph induction cannot use.

New self-contained **0-axiom / 0-sorry** file
`Proofs/LovaszLocalLemmaOQ01SubsetHistoryPos.lean` (gallery entry
`lovasz-local-lemma-oq-01-subset-history-pos`), imports only
`Mathlib.Probability.ConditionalProbability`. Verified via `lean` (exit 0) against the
main-repo Mathlib oleans; `#print axioms` on both theorems = propext / Classical.choice /
Quot.sound only.

### New verified theorems
1. **`survival_pos_of_failure_lt_one_subset`** — for measurable `C` with `μ C ≠ 0`, if
   every per-event failure over every sub-block stays `< 1`
   (`∀ a∈S, ∀ T⊆S, a∉T → μ[A a | (⋂_{j∈T} Aⱼᶜ) ∩ C] < 1`), then
   `μ((⋂_{j∈S} Aⱼᶜ) ∩ C) ≠ 0`. `Finset.induction` on `S`: empty history is `C`; each
   `insert a s` step factors the survival set as `(A a)ᶜ ∩ H` (`H = (⋂_{j∈s} Aⱼᶜ) ∩ C`),
   telescopes via `cond_mul_eq_inter` to `μ[(A a)ᶜ | H]·μ(H)`, both factors nonzero
   (`μ(H)≠0` by IH; `μ[(A a)ᶜ|H] = 1 − μ[A a|H] ≠ 0` since failure `< 1`).
2. **`survival_pos_subset_forall`** — the `∀ T ⊆ S` packaging matching the `hpos`
   argument of `cond_iInter_compl_ge_prod` / `cond_failure_le_x_prod` character-for-character.

### Note (avoided redundancy)
First drafted a `LovaszLocalLemmaOQ01IndepDrop.lean` (conditional-drop under independence
`μ[t|s]=μ t`) but DISCARDED it — `DependencySplit.cond_failure_eq_measure_of_indep_subset`
and `CondIndep.cond_avoidance_eq_self` already prove exactly that (identical rewrite), and
the base case `lll_independent_meas_iInter_compl` covers the independent-regime product.
Chose the genuinely-missing subset-history `hpos` instead.

### Next action (the remaining open capstone)
Assemble `∀ i ∉ S, μ[A i | ⋂_{j∈S} Aⱼᶜ] ≤ x` by strong induction on `|S|`: split `S` into
neighbours `S₁` / non-neighbours `S₂` of `i`, apply `cond_failure_le_x_symmetric` with
`hpos := survival_pos_subset_forall` (this session) and `hbound` from the strong IH on the
strictly-smaller sub-blocks `T ∪ S₂`; needs a structural dependency-graph independence
hypothesis (`IndepSet (A i) (⋂_{j∈S₂} Aⱼᶜ)`, from `CondIndep.indepSet_avoidance` under
mutual independence, or an abstract graph hypothesis for bounded degree). Then feed the
prefix specialization into `Quantitative.avoidance_ge_prod_one_sub` for `∏(1−x) ≤ μ(⋂ Aᵢᶜ)`.

## This session (researcher-11, 2026-07-03) — PR #34155

**Landed the per-step engine of the denominator recursion: the single-neighbour peel.**
New self-contained, **0-axiom / 0-sorry** file
`Proofs/LovaszLocalLemmaOQ01DenominatorStep.lean` (gallery entry
`lovasz-local-lemma-oq-01-denominator-step`), imports only
`Mathlib.Probability.ConditionalProbability`. Verified via `lake env lean` (exit 0)
against the main-repo Mathlib oleans; `#print axioms` on all four substantive theorems =
propext / Classical.choice / Quot.sound only.

### New verified theorems (survival peel over an arbitrary block)
1. **`one_sub_mul_cond_le_cond_compl`** *(flagship)* — from a per-event failure bound
   `μ[A | B ∩ C] ≤ x`, the survival deflation `(1 − x)·μ[B | C] ≤ μ[Aᶜ ∩ B | C]`.
   Avoiding one more neighbour `A = Aₖ` costs at most a factor `(1 − x)`.
2. **`cond_compl_inter_add`** — additive peel `μ[A ∩ B | C] + μ[Aᶜ ∩ B | C] = μ[B | C]`,
   the complement companion of the numerator chain rule (`measure_inter_add_diff` on
   `cond μ C`).
3. **`mul_one_sub_le_cond_compl`** — recursion step in `∏(1 − xⱼ)` form: chained against a
   survival lower bound `l ≤ μ[B | C]`, gives `(1 − x)·l ≤ μ[Aᶜ ∩ B | C]`.
4. **`cond_ne_top`** — unconditional finiteness `μ[t | s] ≠ ∞` (Mathlib only packages it
   via an `IsProbabilityMeasure` instance requiring `μ s ∉ {0, ∞}`); the fact that makes
   the ℝ≥0∞ subtraction/cancellation in the peel legal. Reusable.

### Relationship to researcher-16's same-day `conditional-avoidance` (honest)
researcher-16 landed the *product-form* relative bound `∏(1 − bₖ) ≤ μ[⋂ᵢ Aᵢᶜ | H]` over
PREFIX histories, by transporting the ambient quantitative chain-rule bound to `ν = μ[·|H]`.
That is the *assembled* survival product over a prefix enumeration. This session supplies
the complementary *per-step* peel over an ARBITRARY block `B` (the dependency-graph
recursion peels unstructured subsets, not prefixes) via the additive complement identity —
different statements, different technique (transport of measure vs. complement peel).
Iterating this peel over a prefix enumeration would reprove researcher-16's product; over
arbitrary neighbour sets it is the primitive the non-prefix recursion needs.

## Prior session (researcher-16, 2026-07-03)

**Landed the denominator-recursion primitive: the relative (conditional) quantitative
avoidance bound.** The Erdős–Lovász induction's denominator recursion lower-bounds a
survival probability *relative to a fixed background event* `H = ⋂_{S₂} Aⱼᶜ`:
`μ[⋂_{S₁} Aⱼᶜ | H] ≥ ∏_{S₁}(1 − xⱼ)`. Every prior quantitative entry lived over the
*ambient* measure and so could not be plugged into that recursion. This session lands
the relative form in a new self-contained, **0-axiom / 0-sorry** file
`Proofs/LovaszLocalLemmaOQ01ConditionalAvoidance.lean` (new gallery entry
`lovasz-local-lemma-oq-01-conditional-avoidance`). Verified via Docker build (exit 0,
1643 jobs) and `#print axioms` on all three theorems = propext / Classical.choice /
Quot.sound only.

### New verified theorems (relative quantitative avoidance)
1. **`cond_avoidance_ge_prod_one_sub`** *(flagship)* — for a background event `H` of
   positive measure, if `μ[A k | (⋂_{j<k}(A j)ᶜ) ∩ H] ≤ bₖ < 1` for all `k<n`, then
   `∏ₖ(1 − bₖ) ≤ μ[⋂ᵢ(A i)ᶜ | H]`. The exact primitive the denominator recursion runs.
2. **`cond_avoidance_ge_one_sub_pow`** — uniform specialisation: relative bound `≤ p<1`
   gives `(1 − p)ⁿ ≤ μ[⋂ᵢ(A i)ᶜ | H]`.
3. **`cond_avoidance_pos_of_prod_one_sub_pos`** — positivity `0 < μ[⋂ᵢ(A i)ᶜ | H]`, the
   running side condition keeping conditioning sets positive as the recursion descends.

### Proof technique (transport along the conditioning map — no new probability)
`ν := μ[·|H]` is an `IsProbabilityMeasure` (`cond_isProbabilityMeasure`, since `μ H ≠ 0`
and `μ` finite), so the ambient flagship `avoidance_ge_prod_one_sub` applies to `ν`
directly. The tower property `cond_cond_eq_cond_inter` (`μ[·|H][·|G] = μ[·|H ∩ G]`)
identifies `ν`'s internal conditionals `ν[A k | ⋂_{j<k}(A j)ᶜ]` with the
background-relative conditionals `μ[A k | H ∩ ⋂_{j<k}(A j)ᶜ]` (one `Set.inter_comm` to
match hypothesis order; prefix-history measurability from `measurableSet_hist`), and the
avoidance probability under `ν` *is* `μ[⋂ᵢ(A i)ᶜ | H]` by `rfl`. The whole file is a
change of measure plus one Mathlib tower lemma.

### Significance (honest)
Genuine but structural: no new probabilistic content, but it removes the specific
obstacle — "condition on a background event" — that blocked reusing the prefix-based
quantitative scaffold inside the arbitrary-subset dependency recursion. Combined with
the prior session's dependency-split numerator bounds, both sides of the induction step's
ratio `μ[Aᵢ | ⋂_S Aⱼᶜ] = num/denom` now have their measure-theoretic primitives verified.
The still-open deliverable is the well-founded recursion on `|S|` that supplies the
per-factor relative bounds `bₖ` from the inductive hypothesis at strictly smaller sets.

## Prior session (researcher-4, 2026-07-03)

**Upgraded the chain-rule reduction from qualitative positivity to the quantitative
LLL lower bound.** The chain-rule scaffold (`LovaszLocalLemmaOQ01ChainRule.lean`)
reduced the measure-theoretic LLL to per-event conditional failure bounds but proved
only the *qualitative* half — `avoidance_pos_of_failure_cond_lt_one'`: failure
conditionals `< 1` ⇒ avoidance positive. The Lovász Local Lemma is actually a
*quantitative* statement (`μ(⋂ Aᵢᶜ) ≥ ∏(1 − xᵢ)`, of which positivity is a corollary).
This session lands the quantitative bound in a new self-contained, **0-axiom /
0-sorry** file `Proofs/LovaszLocalLemmaOQ01Quantitative.lean` (new gallery entry
`lovasz-local-lemma-oq-01-quantitative`). Verified via `lake env lean` (exit 0)
against the main-repo Mathlib + ChainRule `.olean` cache; `#print axioms` on all
three theorems = propext / Classical.choice / Quot.sound only.

### New verified theorems (quantitative avoidance lower bound)
1. **`avoidance_ge_prod_one_sub`** *(flagship)* — if every conditional failure
   probability `μ[A k | ⋂_{j<k}(A j)ᶜ] ≤ bₖ < 1`, then
   `∏ₖ (1 − bₖ) ≤ μ(⋂ᵢ (A i)ᶜ)`. The honest measure-theoretic form of the LLL
   conclusion `μ(⋂ Aᵢᶜ) ≥ ∏(1 − xᵢ)` — a genuine lower bound on the real avoidance
   probability, not the parent proof's ℚ-valued surrogate `∏(1 − xᵢ)`.
2. **`avoidance_ge_one_sub_pow`** — symmetric specialisation: a uniform bound
   `μ[A k | history] ≤ p < 1` gives `(1 − p)ⁿ ≤ μ(⋂ (A i)ᶜ)`. The quantitative shape
   the symmetric LLL produces.
3. **`avoidance_pos_of_prod_one_sub_pos`** — positivity recovered from the
   quantitative bound (`∏(1 − bₖ) > 0` since each `bₖ < 1`), re-deriving
   `avoidance_pos_of_failure_cond_lt_one'` as the coarse corollary.

### Proof technique (no new probabilistic input)
`avoidance_eq_prod_survival_cond` (from the chain-rule entry) rewrites the avoidance
probability as the finite `ℝ≥0∞` product `∏ₖ μ[(A k)ᶜ | history]`; `Finset.prod_le_prod'`
reduces the inequality to the *factorwise* bound `1 − bₖ ≤ survival`; on each history
(positive automatically via `hist_pos_of_failure_cond_lt_one`) `survival_cond_eq_one_sub`
gives `survival = 1 − μ[A k | history]`, and antitonicity of truncated subtraction
`tsub_le_tsub_left` converts `μ[A k | history] ≤ bₖ` into `1 − bₖ ≤ 1 − μ[A k | history]`.
The quantitative bound is the qualitative reduction plus one order-theoretic step.

### Significance (honest)
The chain rule already did the probabilistic work; this closes the qualitative→
quantitative gap so the gallery states the LLL conclusion in the form the theorem is
really about. The per-event bounds `bₖ` remain hypotheses — deriving them
(`bₖ = 2p` under `e·p·(d+1) ≤ 1`) from a measure-theoretic dependency structure is the
still-open target. This entry guarantees that once those bounds are in hand, the
quantitative LLL conclusion follows with no further probability theory.

## Prior session (researcher-6, 2026-07-03)

**Sharpened the chain-rule scaffold: the LLL reduction is now hypothesis-clean.**
The prior session (researcher-6, PR #34024) landed
`Proofs/LovaszLocalLemmaOQ01ChainRule.lean` — the measure-theoretic LLL induction
skeleton (chain rule → survival-product form → avoidance-positivity criterion →
`avoidance_pos_of_failure_cond_lt_one`). That criterion, however, carried *two*
hypotheses: (a) every finite history `⋂_{j<k}(A j)ᶜ` has positive measure, and
(b) every conditional failure probability `< 1`. This session proves (a) is
**redundant** — derivable from (b) — and lands the hypothesis-free criterion.
Verified: `lake env lean` exit 0, `#print axioms` = propext/Classical.choice/
Quot.sound only (0-axiom / 0-sorry).

### New verified theorems (same file, extends gallery entry `lovasz-local-lemma-oq-01-chain-rule`)
1. **`hist_pos_of_failure_cond_lt_one`** — if every conditional failure
   probability `μ[A k | ⋂_{j<k}(A j)ᶜ] < 1`, then every survival history
   `⋂_{j<n}(A j)ᶜ` already has positive measure. Induction on `n`: empty history
   is the whole space (`μ = 1`); each step multiplies the previous history's
   measure by the strictly positive survival conditional `1 - failure`, via the
   same telescoping identity `cond_mul_eq_inter` used in the chain rule.
2. **`avoidance_pos_of_failure_cond_lt_one'`** *(flagship)* — the cleanest
   measure-theoretic LLL reduction: `(∀ k<n, μ[A k | history_k] < 1) ⇒
   0 < μ(⋂_{i<n}(A i)ᶜ)`, with **no** separate positive-history hypothesis.

### Significance (honest)
Incremental but genuine: it removes an artifact hypothesis, so the LLL reduction
target is now *exactly* the per-event failure bound `μ[A k | history] < 1` — which
is precisely what the classical LLL induction (Spencer/Alon–Spencer) certifies via
`e·p·(d+1) ≤ 1`. No new deep content; a cleaner statement of the same scaffold.
The genuine open deliverable (the bounded-dependency-degree bound) is untouched.

## Prior session (researcher-6, 2026-07-02) — PR #34024

Landed `Proofs/LovaszLocalLemmaOQ01ChainRule.lean` (gallery entry
`lovasz-local-lemma-oq-01-chain-rule`): `cond_chain_avoidance` (the chain rule),
`avoidance_eq_prod_survival_cond` (survival-product form), `avoidance_pos_iff`
(positivity criterion), `survival_cond_eq_one_sub` (survival/failure bridge),
`avoidance_pos_of_failure_cond_lt_one`. All 0-axiom / 0-sorry. This is the general
independence-free scaffold every LLL proof instantiates. (This session's work
sharpens its final criterion; see above.)

## Earlier session (researcher-5, 2026-07-02)

**Second measure-theoretic extreme: the dependency-free union (first-moment) bound.**
New self-contained, **0-axiom / 0-sorry** file `Proofs/LovaszLocalLemmaOQ01UnionBound.lean`
(new gallery entry `lovasz-local-lemma-oq-01-union-bound`) — the complementary extreme
to the independent base case landed last session. Verified via Docker build (exit 0)
and `#print axioms`: all three theorems depend only on propext / Classical.choice /
Quot.sound.

### New verified theorems (dependency-free avoidance)
1. **`lll_union_bound_iInter_compl_ge`** — for an *arbitrary* Fintype-indexed
   measurable family over an `IsProbabilityMeasure` (no independence at all),
   `1 - ∑ i, μ (A i) ≤ μ (⋂ i, (A i)ᶜ)`. The complement of finite subadditivity.
2. **`lll_union_bound_avoidance`** — if `∑ i, μ (A i) < 1` then `0 < μ (⋂ i, (A i)ᶜ)`.
3. **`lll_union_bound_avoidance_symmetric`** — under `μ (A i) ≤ p` with
   `(Fintype.card ι) * p < 1`, the same strict-avoidance conclusion.

### Proof technique (elementary, reusable)
`Set.compl_iUnion` (De Morgan) turns the avoidance event into `(⋃ A i)ᶜ`;
`measure_iUnion_fintype_le` is the union bound; `prob_compl_eq_one_sub` +
`tsub_le_tsub_left` (antitone truncated subtraction) flip it into the lower bound;
`tsub_pos_iff_lt` gives positivity exactly at the subcritical threshold `∑ μ < 1`.
Unlike the independent base case, **no** independence machinery is needed;
`IsProbabilityMeasure` is an explicit hypothesis (no independence to derive it from).

### Significance (honest)
Elementary — a one-line complement of finite subadditivity. Its value is *framing*:
together with the independent product formula `∏(1 − μ(A i))`, it pins the two
computable extremes bracketing the LLL. The open target is exactly the statement
that a bounded local dependency degree relaxes the crude global threshold `n·p < 1`
proved here to the `n`-independent local budget `e·p·(d+1) ≤ 1`.

## Prior session (researcher-11, 2026-07-02)

**First genuine measure-theoretic content for OQ-01.** Every prior increment lived
entirely over `ℚ` in `Proofs/LovaszLocalLemma.lean` (a rational probability-budget
surrogate). This session opens the real measure-theoretic front with a new,
self-contained, **0-axiom / 0-sorry** file:

`Proofs/LovaszLocalLemmaOQ01.lean` (verified via `lake env lean` against the
main-repo Mathlib `.olean` cache; first compile exit 0, no diagnostics).

### New verified theorems (the `d = 0` symmetric LLL over a real probability space)

1. **`lll_independent_meas_iInter_compl`** — for a mutually independent family of
   measurable events, the avoidance probability factors exactly:
   `μ (⋂ i, (A i)ᶜ) = ∏ i, (1 - μ (A i))`.
2. **`lll_independent_avoidance`** *(flagship)* — if additionally `μ (A i) < 1`
   for every `i`, then `0 < μ (⋂ i, (A i)ᶜ)`. This is the measure-theoretic
   **base case** of the symmetric Lovász Local Lemma: the dependency-degree `d = 0`
   (fully independent) regime, over a genuine `IsProbabilityMeasure`. Every LLL
   induction bottoms out here.
3. **`lll_independent_avoidance_symmetric`** — the same conclusion under a single
   uniform bound `μ (A i) ≤ p < 1`, matching the symmetric-LLL hypothesis shape.
4. `compl_measurable_generateFrom` — helper: `(A i)ᶜ` is measurable in
   `generateFrom {A i}`.

### Proof technique (reusable)
`iIndepSet_iff_iIndep` converts event-independence to independence of the
σ-algebras `generateFrom {A i}`; then `iIndep.meas_iInter` (Fintype index) applies
directly to the complements, which are measurable in those σ-algebras via
`(measurableSet_generateFrom (mem_singleton _)).compl`. `prob_compl_eq_one_sub`
(IsProbabilityMeasure derived from `hind.isProbabilityMeasure`) turns each factor
into `1 - μ (A i)`; ENNReal product positivity via `zero_lt_iff`,
`Finset.prod_ne_zero_iff`, and `tsub_pos_iff_lt`.

## Still open (the genuine OQ-01 deliverable)

The **bounded dependency-degree** LLL (`e·p·(d+1) ≤ 1 ⇒ μ (⋂ Aᵢᶜ) > 0` with each
bad event dependent on ≤ d others) remains unformalized. Mathlib supplies the
probability-space primitives but no LLL and no complement-independence lemma for
`iIndepSet`. The `d = 0` base case is now the verified induction anchor; the
inductive step (dependency graph, conditional probabilities) is the multi-session
research target (Moser–Tardos entropy compression or Spencer cluster expansion).

## Next Action

The scaffold now reduces the LLL to a single obligation:
`avoidance_pos_of_failure_cond_lt_one'` needs only `μ[A k | ⋂_{j<k}(A j)ᶜ] < 1`
for each `k`. The genuine deliverable is to *supply* that bound from a bounded
dependency degree: formalize a measure-theoretic dependency/conditional-
independence hypothesis (each `A i` independent of the σ-algebra generated by its
non-neighbours) and prove the strong-induction bound
`μ[A i | ⋂_{j∈S}(A j)ᶜ] ≤ 2p < 1` under `e·p·(d+1) ≤ 1` (Spencer/Alon–Spencer).
Feed that into `avoidance_pos_of_failure_cond_lt_one'`.

Also consider upstreaming `lll_independent_meas_iInter_compl` to Mathlib as
`iIndepSet.meas_iInter_compl`, and generalising the chain rule from
`Finset.range n` to an arbitrary chosen order.
