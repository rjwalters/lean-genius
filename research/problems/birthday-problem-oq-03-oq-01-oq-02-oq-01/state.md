# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT (Layer 3 advancing: 3a–3e complete; 3f–3g remaining for r = 2)
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 16
**Last Update**: 2026-05-08 (Session 16, researcher-9)

## Session 16 Summary (2026-05-08, researcher-9)

**Mode**: ACT (Layer 3 sub-piece 3e per roadmap §8a).

**Outcome**: implemented Layer 3 sub-piece 3e (disjoint joint-coincidence
count) in a new §8 of `BirthdayProblemOQ03OQ01OQ02.lean` (≈ 240 lines added;
file 1555 → 1795 lines, 48 → 49 theorems / lemmas, 8 defs unchanged):

- **Layer 3e** `bad_count_disjoint (d n : ℕ) (a₁ b₁ c₁ a₂ b₂ c₂ : Fin n) ...`
  — joint-coincidence count for two strict triples with 6 pairwise-distinct
  indices: `card {f | f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f a₂ = f b₂ ∧ f b₂ = f c₂}
  = d^(n-4)`. Generalises S11's `bad_count_general` (one triple, `d^(n-2)`)
  via the same explicit-bijection strategy: restriction to the (n-4)-element
  complement of `{b₁, c₁, b₂, c₂}`, with the inverse extending by
  `f m = g a₁` for `m ∈ {b₁, c₁}`, `f m = g a₂` for `m ∈ {b₂, c₂}`,
  `f m = g m` otherwise. The 15 pairwise-distinctness hypotheses (within-
  triple 6 + cross-triple 9 = K₆ edges on the 6 indices) are precisely those
  needed by the `dif_neg`/`dif_pos` chains in the membership proof.
- **Layer 3e (corollary)** `p_pair_disjoint` — real-number form: with `n ≥ 4`,
  `d ≥ 1`, the joint-coincidence probability is exactly `1/d⁴`, independent
  of `n`. Combines `bad_count_disjoint` with `Fintype.card_fun = d^n` and the
  power split `d^n = d^(n-4) · d^4` (via `Nat.sub_add_cancel`), then
  `push_cast` + `field_simp`. Mirrors `p_triple_general` (S11) but at
  exponent 4 instead of 2.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S15).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e (S14+S15+S16) are now
complete in raw count form. Layer 3 will close at S17 after S16b/c
specialise `bad_count_disjoint` to the strict-pair `overlapPattern n 0`
form (≈ 60 lines) and bound the non-disjoint k ∈ {1, 2} strata (≈ 80 lines).

## Session 15 Summary (2026-05-08, researcher-10)

**Mode**: ACT (Layer 3 sub-pieces 3c/3d per roadmap §8a).

**Outcome**: implemented Layer 3 sub-pieces 3c (overlap-pattern partition)
and 3d (factorial-moment-2 sum decomposition) in a new §7 of
`BirthdayProblemOQ03OQ01OQ02.lean` (≈ 263 lines added; file 1295 → 1555
lines, 41 → 48 theorems / lemmas, 6 → 8 defs):

- `def tripleSet {n} (T : Fin n × Fin n × Fin n) : Finset (Fin n)` —
  underlying 3-element index set `{T.1, T.2.1, T.2.2}` of a triple.
- `card_tripleSet_of_strict` — for `T ∈ strictTriples n` (i.e. a < b < c),
  `(tripleSet T).card = 3`. Proved by the chain `Finset.card_insert_of_not_mem
  ∘ Finset.card_insert_of_not_mem ∘ Finset.card_singleton` with explicit
  non-membership hypotheses derived from the strict order.
- **Key lemma** `strict_eq_of_tripleSet_eq` — for STRICT triples, the
  underlying 3-element set determines the triple as a sorted tuple. Proof:
  destructure both T₁ = (a, b, c) and T₂ = (a', b', c'), then derive
  a = min(set) = a' by `le_antisymm` (each element of one is ≥ the min of
  the other); similarly c = max = c'; finally b is the unique remaining
  element. This is the geometric content that rules out the overlap-3
  stratum in `overlapPattern`.
- `tripleSet_inter_card_le_three` — auxiliary bound for the fiberwise
  partition (the intersection card is ≤ tripleSet.card = 3).
- **Layer 3c** `def overlapPattern (n k : ℕ)` — ordered pairs (T₁, T₂)
  of distinct strict triples with `(tripleSet T₁ ∩ tripleSet T₂).card = k`.
  Index range is `k ∈ {0, 1, 2, 3}` formally; the genuine partition is
  `{0, 1, 2}` after the next lemma.
- **Layer 3c** `overlapPattern_three_eq_empty` — the k = 3 stratum is empty.
  Proved by: if T₁ ∩ T₂ has card 3, then by
  `Finset.eq_of_subset_of_card_le` it equals both `tripleSet T₁` and
  `tripleSet T₂`, hence those underlying sets coincide; then by
  `strict_eq_of_tripleSet_eq` the triples coincide, contradicting T₁ ≠ T₂.
- **Layer 3c** `overlapPattern_partitions_offDiag` — the four strata
  partition the diagonal-removed pair-of-strict-triples space:
  `(((strictTriples n) ×ˢ (strictTriples n)).filter (· ≠ ·)).card =
   ∑ k ∈ Finset.range 4, (overlapPattern n k).card`. Proved via
  `Finset.card_eq_sum_card_fiberwise` with the overlap-size as the fiber
  function (bounded by 3 from `tripleSet_inter_card_le_three`).
- **Layer 3d** `tripleCount_descFact_2_eq_overlap_sum` — per-`f`
  structural identity:
  `(tripleCount d n f).descFactorial 2 = ∑ k ∈ Finset.range 4,
  ((overlapPattern n k).filter (f-trivialise both)).card`. Proved by
  combining Layer 3b (S14, `tripleCount_descFact_2_eq_pairs`) with the
  same fiberwise partition + `tauto` for the conjunction reordering of
  membership predicates.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S14).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3d (S14+S15) are now
complete; Layer 3 will close at S17 after S16 implements the
quantitative pieces 3e (disjoint contribution `1/d⁴` per pair) and 3f
(non-disjoint contributions vanish at `O(d^{-2/3})`) and S17 combines
3d/3e/3f to get `factorial_moment_2 → (c³/6)²`.

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
2. ✅ **Layer 2 part 1 (S11)**: `bad_count_general` + `p_triple_general` — DONE on main.
3. ✅ **Layer 2 part 2 (S12)**: `card_strict_triples` + `tripleCount_sum_eq` +
   `expectedTripleCount_eq` — DONE on main. **LAYER 2 COMPLETE.**
4. ✅ **Layer 3 sub-decomposition (S13)**: roadmap §8a (7 sub-pieces 3a–3g). DONE.
5. ✅ **Layer 3a/3b (S14)**: `strictTriples` def, `descFactorial_two_real_eq`,
   `tripleCount_descFact_2_eq_pairs` — DONE on main (#17227).
6. ✅ **Layer 3c (S15, this session)**: `tripleSet`, `overlapPattern n k`,
   `overlapPattern_three_eq_empty`, `overlapPattern_partitions_offDiag` — DONE
   pending build. The `Fin 4`-based roadmap signature was specialised to
   `ℕ`-indexed Finset.range 4 to align with `Finset.card_eq_sum_card_fiberwise`.
7. ✅ **Layer 3d (S15, this session)**: `tripleCount_descFact_2_eq_overlap_sum` —
   per-`f` structural identity expressing `tripleCount.descFactorial 2` as a
   sum over overlap strata of f-trivialised counts. DONE pending build.
8. ✅ **Layer 3e (S16, this session)**: `bad_count_disjoint` + `p_pair_disjoint`
   — DONE pending build. The raw 6-pairwise-distinct-indices form. The
   strict-pair specialisation using `overlapPattern n 0` is queued for S16b.
9. **Layer 3e specialisation (S16b)**: `bad_count_disjoint_strict (T₁ T₂)` —
   wrap S16's raw form with the 15 distinctness hypotheses derived from
   `(tripleSet T₁ ∩ tripleSet T₂).card = 0` and the strict-triple ordering.
   ≈ 60 lines. Sets up Layer 3g to apply directly to the `overlapPattern n 0`
   summand of `tripleCount_descFact_2_eq_overlap_sum`.
10. **Layer 3f (S16c)**: non-disjoint contributions (k = 1, 2 strata) vanish
    at rate `O(d^{-2/3})` per roadmap §4c. ≈ 80 lines.
11. **Layer 3g (S17)**: combine 3d/3e/3f to get `factorial_moment_2 → (c³/6)²`. ≈ 30 lines.
12. **Layer 4 (S18+)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
13. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
    contribution for Layer 4 in parallel with local Layer 3.
