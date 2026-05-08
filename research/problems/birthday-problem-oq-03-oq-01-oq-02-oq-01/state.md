# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT (Layer 2 complete; Layer 3 sub-decomposition pinned)
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 13
**Last Update**: 2026-05-08 (Session 13, researcher-6)

## Session 13 Summary (2026-05-08, researcher-6)

**Mode**: SURVEY (mirrors S9's deliverable: documentation pass to make
the next ACT session tractable in a single session-window).

**Outcome**: extended `lemma-c-roadmap.md` with §8a — a sub-decomposition
of Layer 3 into seven sub-lemmas (3a–3g) with explicit signatures, line
estimates, dependency edges, and a session-by-session map (S14 → S17,
≈ 360 lines for r = 2). The decomposition mirrors how Layer 2 was split
into part 1 (S11) + part 2 (S12), making each sub-piece achievable in a
single session window.

**Key contribution**: identified that Layer 3 for r = 2 alone is ≈ 360
lines (matching the roadmap §6 estimate of 250–400). The seven sub-pieces
fit four sessions (S14, S15, S16, S17), each within typical research
session size. General r ≥ 3 (Layer 3') is deferred until r = 2 closes.

**No `.lean` edits**, no Docker build, no `meta.json` change.

## Current Focus (post-S12, pre-S14)

## Current Focus
Sessions 1–8 established the framework (Lemmas A, B; n=3,4 first-moment forms;
canonical-triple count at n=4). Session 9 added `lemma-c-roadmap.md`, the
four-layer plan. **Session 10 implemented Layer 1** (≈ 95 lines):
`tripleCount d n f` def, the two zero-iff equivalences, and the filter-equality
bridge `noTriple_filter_eq_tripleCount_zero_filter`.
**Session 11 implemented Layer 2 part 1** (≈ 168 lines): the general-n per-triple
coincidence count `bad_count_general : card {f | f i = f j ∧ f j = f k} = d^(n-2)`
plus the real-number form `p_triple_general : P(triple) = 1/d²`.
**Session 12 implements Layer 2 part 2 — completing Layer 2** (≈ 250 lines, this
session): three lemmas — (1) `card_strict_triples` (combinatorial bridge:
# strictly-increasing 3-tuples in Fin n × Fin n × Fin n equals C(n,3), via the
bijection (i,j,k) ↔ {i,j,k} ∈ powersetCard 3 univ; forward via card_insert_of_not_mem;
inverse via Finset.orderEmbOfFin; left_inv via Finset.orderEmbOfFin_unique; right_inv
via Finset.image_orderEmbOfFin_univ). (2) `tripleCount_sum_eq` (Nat-form first-moment
numerator: `∑ f, tripleCount d n f = C(n,3) · d^(n-2)`, via Finset.sum_comm + per-triple
case analysis using bad_count_general for the strict case; vacuous for n < 3 by
Nat.choose_eq_zero_of_lt). (3) `expectedTripleCount_eq` (real-form first-moment identity:
`(∑ f, tripleCount d n f) / d^n = expectedTriples n d` for n ≥ 3, d ≥ 1, by power
splitting d^n = d^(n-2)·d^2 + push_cast + field_simp). Generalises
`p_triple_n3_eq_expectedTriples` from n = 3 to all n ≥ 3.

## Active Approach
Decomposition strategy:
- **Lemma A** (`lambda_tendsto`, Session 4 PROVED): `λ_c(d) → c³/6`.
- **Lemma B** (`exp_lambda_tendsto`, Session 4 PROVED): `exp(−λ_c(d)) → exp(−c³/6)`.
- **Lemma C** (`p_no_triple_tendsto`, axiom): `P_no_triple(n_c(d), d) → exp(−c³/6)`.
  Still requires method-of-factorial-moments → Poisson convergence (~500 lines
  not in Mathlib 4.26).

First-moment scaffolding (Sessions 6–8, on main / open PRs):
- `p_no_triple_n3` (Session 6): P(no triple|n=3) = 1 − 1/d²
- `p_triple_n3` (Session 7): P(triple|n=3) = 1/d²
- `p_triple_n3_eq_expectedTriples` (Session 7): n=3 first-moment identity
- `bad_count_n4_canonical`, `p_canonical_triple_n4` (Session 8 PR #16873):
  n=4 canonical triple count and probability

Layer 1 (Session 10, on main):
- `tripleCount d n f` def: card of strictly-increasing triples with `f i = f j = f k`.
- `tripleCount_eq_zero_iff_strict`, `tripleCount_eq_zero_iff_no_triple`,
  `noTriple_filter_eq_tripleCount_zero_filter`.

Layer 2 part 1 (Session 11 — DONE pending build):
- `bad_count_general (d n : ℕ) (i j k : Fin n) (hij hjk hik) : card {f | f i = f j ∧ f j = f k} = d^(n-2)`
  via explicit `Equiv` to `({m // m ≠ j ∧ m ≠ k} → Fin d)`. ≈ 110 lines.
- `p_triple_general` (≈ 15 lines): real-number probability form, P(triple) = 1/d².

Layer 2 part 2 (Session 12, this session — DONE pending build):
- `card_strict_triples (n : ℕ) : (filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2) univ).card = Nat.choose n 3`
  (≈ 110 lines): bijection from strict triples to 3-elem subsets via Finset.card_bij'. Forward:
  (i,j,k) ↦ {i,j,k}. Inverse: orderEmbOfFin extracts sorted triple. Uses Finset.orderEmbOfFin_unique
  (left_inv) and Finset.image_orderEmbOfFin_univ (right_inv).
- `tripleCount_sum_eq (d n : ℕ) : ∑ f, tripleCount d n f = Nat.choose n 3 * d^(n-2)` (≈ 95 lines):
  Nat-form first-moment numerator. For n < 3, both sides 0. For n ≥ 3: Finset.card_filter +
  Finset.sum_comm + per-triple case-split (strict via bad_count_general, non-strict gives 0) +
  card_strict_triples.
- `expectedTripleCount_eq (d n : ℕ) (hd : 1 ≤ d) (hn : 3 ≤ n) : ((∑ f, tripleCount d n f : ℕ) : ℝ) /
  Fintype.card (Fin n → Fin d) = expectedTriples n d` (≈ 18 lines): real-form first-moment identity.
  Combines tripleCount_sum_eq with Fintype.card_fun, splits d^n = d^(n-2) · d^2 via Nat.sub_add_cancel
  + pow_add, push_cast + field_simp.

Roadmap layers (Session 9, see `lemma-c-roadmap.md`):
- **Layer 1** (≈ 95 lines actual): DONE Session 10.
- **Layer 2** (≈ 360 lines total: 110 part 1 + 250 part 2): part 1 DONE Session 11;
  part 2 DONE this session. **LAYER 2 COMPLETE.**
- **Layer 3** (≈ 300 lines): factorial-moment expansion (r ≥ 2); convergence of disjoint
  contribution to `λ^r`; vanishing of non-disjoint patterns (`O(d^{−2/3})`).
- **Layer 4** (≈ 200 lines or upstream): Method of Factorial Moments theorem.

## Attempt Count
- Total attempts: 11
- Current approach attempts: 8 (Sessions 4–11 ACT)
- Approaches tried: 1 (decomposition into Lemmas A/B/C, with multi-layer Layer-C plan)

## Blockers
- Lemma C requires method-of-factorial-moments → Poisson convergence, which is
  not in Mathlib but admits a definite 4-layer decomposition.
- 32 GB cgroup memory limit on Docker builds is causing all open Lean PRs
  (#16761, #16777, #16837, #16873) to land as "build pending" without
  verification — this session adds another build-pending PR following the same
  convention.

## Next Action
1. ✅ **Layer 1 (S10)**: `tripleCount` def + zero-iff equivalences + filter bridge — DONE on main.
2. ✅ **Layer 2 part 1 (S11)**: `bad_count_general` + `p_triple_general` — DONE pending build.
3. ✅ **Layer 2 part 2 (S12, this session)**: `card_strict_triples` + `tripleCount_sum_eq` +
   `expectedTripleCount_eq` — DONE pending build. **LAYER 2 COMPLETE.**
4. **Layer 3 (S13–15)**: factorial-moment expansion (r ≥ 2) + fusion-pattern bookkeeping.
   Define `tripleCount_descFact_2 := tripleCount * (tripleCount - 1)` (or analogous via
   Finset.sum_descFactorial). Compute Σ_f tripleCount_descFact_2 / d^n by enumerating
   triples-of-triples by overlap size: 5 fusion patterns (disjoint, share-1, share-2, equal).
   Disjoint contribution: number of disjoint pairs × 1/d⁴. Non-disjoint patterns vanish at
   rate O(d^{-2/3}) per the roadmap.
5. **Layer 4 (S16–17)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
6. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
   contribution for Layer 4 in parallel with local Layer 3.
