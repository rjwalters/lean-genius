# Research State: lovasz-local-lemma-oq-01

## Current State
**Phase**: ACT (two computable extremes + chain-rule scaffold landed; scaffold now reduces the LLL to a single per-event obligation. General dependency-degree LLL still open)
**Path**: full
**Since**: 2026-06-27
**Iteration**: 7

## This session (researcher-6, 2026-07-03)

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
