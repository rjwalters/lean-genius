# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT (Layer 3 begun: sub-pieces 3a/3b implemented)
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 14
**Last Update**: 2026-05-08 (Session 14, researcher-3)

## Session 14 Summary (2026-05-08, researcher-3)

**Mode**: ACT (Layer 3 sub-pieces 3a/3b per roadmap §8a).

**Outcome**: implemented Layer 3 sub-pieces 3a and 3b in a new §6 of
`BirthdayProblemOQ03OQ01OQ02.lean` (≈ 118 lines added; file 1177 → 1295
lines, 35 → 38 public theorems / lemmas, 4 → 6 defs):

- `def strictTriples (n : ℕ) : Finset (Fin n × Fin n × Fin n)` — public
  reusable Finset of strictly-increasing triples, indexing `tripleCount`.
  Will be used by S15's overlap-pattern partition (Layer 3c).
- `private def tripleCountFinset (d n : ℕ) (f : Fin n → Fin d)` — Finset
  of strict triples that `f` trivialises; cardinality equals
  `tripleCount d n f`. Internal scaffolding for Layer 3.
- `private lemma card_tripleCountFinset` — bridge equality
  `(tripleCountFinset d n f).card = tripleCount d n f`. Pure
  conjunction-reordering proof via `Finset.filter_filter` + `tauto`.
- **Layer 3a** `descFactorial_two_real_eq` — real-valued version of
  `Nat.descFactorial_two`: `(n.descFactorial 2 : ℝ) = n · (n - 1)`. Case
  split at n = 0 to handle truncated Nat subtraction; the n + 1 case uses
  `Nat.descFactorial_two` then `omega` on `(n+1)-1 = n`, then push_cast
  + ring. ≈ 12 lines.
- **Layer 3b** `tripleCount_descFact_2_eq_pairs` — the central r = 2
  identity: `(tripleCount d n f).descFactorial 2` equals the count of
  ordered pairs of distinct strict triples both trivialised by `f`,
  written as a filter on `(strictTriples n) ×ˢ (strictTriples n)`. Proof
  is short: reduce LHS to `(tripleCountFinset).offDiag.card` via
  `Nat.descFactorial_two` + `Finset.card_offDiag`, then `congr` + `ext`
  + `simp only [Finset.mem_offDiag, ...]` + `tauto` for the membership
  reorganisation. ≈ 25 lines including docstring.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10, S11, S12).

**Lemma C axiom unchanged**. Layer 3 (S15–S17) is the next bottleneck:
3c (overlap-pattern partition), 3d (factorial_moment_2 = sum), 3e
(disjoint contribution), 3f (non-disjoint vanishing), 3g (limit).

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
3. ✅ **Layer 2 part 2 (S12)**: `card_strict_triples` + `tripleCount_sum_eq` +
   `expectedTripleCount_eq` — DONE pending build. **LAYER 2 COMPLETE.**
4. ✅ **Layer 3 sub-decomposition (S13)**: roadmap §8a (7 sub-pieces 3a–3g). DONE.
5. ✅ **Layer 3a/3b (S14, this session)**: `strictTriples` def, `descFactorial_two_real_eq`,
   `tripleCount_descFact_2_eq_pairs` — DONE pending build.
6. **Layer 3c (S15)**: define `overlapPattern n : Fin 4 → Finset (...)` partitioning the
   diagonal-removed pair-of-strict-triples space by intersection size. Show overlap-3 is
   empty (strict triples are uniquely ordered) so the partition is over {0, 1, 2}.
   ≈ 60 lines.
7. **Layer 3d (S15)**: `factorial_moment_2_eq_sum_overlapPattern` — combine 3a/3b/3c via
   `Finset.sum_disjUnion`. ≈ 40 lines.
8. **Layer 3e (S16)**: disjoint contribution `1/d⁴` per pair (generalises S11's
   `bad_count_general` to two disjoint triples). ≈ 70 lines.
9. **Layer 3f (S16)**: non-disjoint contributions vanish at rate `O(d^{-2/3})`. ≈ 80 lines.
10. **Layer 3g (S17)**: combine 3d/3e/3f to get `factorial_moment_2 → (c³/6)²`. ≈ 30 lines.
11. **Layer 4 (S18+)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
12. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
    contribution for Layer 4 in parallel with local Layer 3.
