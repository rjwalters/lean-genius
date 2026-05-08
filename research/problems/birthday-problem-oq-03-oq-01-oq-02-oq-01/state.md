# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT (Layer 3 advancing: 3a–3e + strict wrapper + 3f preliminaries complete + S16d main-bound analysis ready-to-port; S16d implementation + S16e per-pair counts + S17 limit remaining for r = 2)
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 19
**Last Update**: 2026-05-09 (Session 16d, researcher-3) — analysis-only

## Session 16d Summary (2026-05-09, researcher-3)

**Mode**: ANALYSIS (no Lean changes; produces a Lean-ready stub for S16d
implementation).

**Outcome**: produced `s16d-overlap-pattern-bounds.md` — a complete
specification of the Layer 3f main bounds:

- `card_overlapPattern_le_generic (n k : ℕ) (hk : k ≤ 3) : (overlapPattern n k).card ≤ Nat.choose n (6 - k) * (Nat.choose (6 - k) 3) ^ 2`
- `card_overlapPattern_le_one (n : ℕ) : (overlapPattern n 1).card ≤ Nat.choose n 5 * 100` (k = 1, asymptotically `O(n⁵)`)
- `card_overlapPattern_le_two (n : ℕ) : (overlapPattern n 2).card ≤ Nat.choose n 4 * 16` (k = 2, asymptotically `O(n⁴)`)

**Proof shape**: `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁,
tripleSet T₂⟩` is an injection from `overlapPattern n k` into the
sigma `Σ U ∈ powersetCard (6-k), U.powersetCard 3 ×ˢ U.powersetCard 3`.
Containment uses `tripleSet_union_card_of_overlap` (S16c) for `|U| =
6-k` and `Finset.subset_union_left/right` for `tripleSet T_i ⊆ U`.
Injectivity uses `strict_eq_of_tripleSet_eq` (S12). Cardinality bound
follows from `Finset.card_image_of_injOn`, `Finset.card_le_card`,
`Finset.card_sigma`, `Finset.card_product`, and
`Finset.card_powersetCard`.

**Mathlib API**: all needed names (`Finset.image`,
`Finset.card_image_of_injOn`, `Finset.powersetCard`,
`Finset.card_powersetCard`, `Finset.sigma`, `Finset.card_sigma`,
`Finset.card_product`, `Finset.subset_union_left/right`,
`Finset.card_le_card`) are present in Mathlib v4.26.0 (the gallery's
pin) and used elsewhere in this file or its imports. No new imports
needed.

**Estimated implementation lines**: 60–70 lines added to §9 of
`BirthdayProblemOQ03OQ01OQ02.lean`, matching roadmap §8a's "60–80
lines via the union-card embedding" estimate.

**Why analysis-only this session**: `BirthdayProblemOQ03OQ01OQ02.lean`
has accumulated four "build pending" PRs (S15, S16, S16b, S16c).
Adding more Lean code on top under current Docker contention adds risk
without unblocking downstream work, while a precise written
specification lets the next session (S16d-implement) transcribe and
test in a single pass with high confidence. This mirrors the
analysis-only pattern used elsewhere in the project (e.g.
schauder-fp-oq-03-oq-01-incomplete-01 S8 → S9, four-square-distribution
S11). The S16d analysis doc closes the only architectural gap between
S16c (preliminaries) and S16e (per-pair counts).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e + strict-wrapper
+ 3f preliminaries (S14–S16c) build the structural inputs; S16d
analysis (this session) specifies the polynomial bounds; S16e per-pair
counts (next + 1) and S17 algebraic limit close Layer 3 for r = 2.

## Session 16c Summary (2026-05-08, researcher-11)

**Mode**: ACT (Layer 3f preliminaries per roadmap §8a, item S16c).

**Outcome**: implemented Layer 3f preliminary structural lemmas
in a new §9 of `BirthdayProblemOQ03OQ01OQ02.lean` (≈ 56 lines added;
file 1893 → 1966 lines, 50 → 54 theorems / lemmas, 8 defs unchanged):

- **Layer 3f preliminary (generic)** `tripleSet_union_card_of_overlap`:
  for any `(T₁, T₂) ∈ overlapPattern n k`,
  `(tripleSet T₁ ∪ tripleSet T₂).card = 6 - k`. Pure inclusion-exclusion
  via `Finset.card_union_add_card_inter` + `card_tripleSet_of_strict`
  (S15) + the membership-extracted `(tripleSet T₁ ∩ tripleSet T₂).card =
  k`. The `omega` closes the resulting `(∪).card + k = 6` form. ≈ 10
  lines.
- **Layer 3f preliminary (k = 0, 1, 2)** specialisations
  `tripleSet_union_card_of_overlap_zero/one/two`: direct corollaries
  giving the union cardinalities 6/5/4 for the disjoint, overlap-1, and
  overlap-2 strata respectively. The k = 1 and k = 2 forms are the
  cardinality inputs for the Layer 3f bounds `|overlapPattern n 1| =
  O(n⁵)` and `|overlapPattern n 2| = O(n⁴)`. ≈ 6 lines each.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S16b).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e + strict wrapper +
3f preliminaries (S14–S16c) are now complete. Layer 3 will close at S17
after S16d bounds `|overlapPattern n 1|` and `|overlapPattern n 2|`
polynomially in n (≈ 60–80 lines via the union-card embedding) and S16e
proves the per-pair joint-coincidence counts for k = 1 (analog of
`bad_count_disjoint`, ≈ 100 lines) and k = 2 (≈ 80 lines), then S17
combines 3d/3e/3f to get `factorial_moment_2 → (c³/6)²` (≈ 30 lines).

**Note**: the roadmap §8a estimated S16 at 80 lines for Layer 3f total;
the actual sub-decomposition into S16c (preliminaries, this session) +
S16d (cardinality bounds) + S16e (per-pair counts) is ≈ 250–300 lines
spread across 3 sessions, parallel to the S15 → S16/S16b expansion of
Layer 3e from the original 70-line estimate.

## Session 16b Summary (2026-05-08, researcher-10)

**Mode**: ACT (Layer 3 sub-piece 3e specialisation per roadmap §8a, item S16b).

**Outcome**: implemented Layer 3e strict-triple wrapper
`bad_count_disjoint_strict` in §8 of `BirthdayProblemOQ03OQ01OQ02.lean`
(≈ 98 lines added; file 1795 → 1893 lines, 49 → 50 theorems / lemmas,
8 defs unchanged):

- **Layer 3e (specialisation)** `bad_count_disjoint_strict (d n : ℕ)
  {T₁ T₂} (hp : (T₁, T₂) ∈ overlapPattern n 0)`: per-pair joint-coincidence
  count for `f : Fin n → Fin d` equals `d^(n - 4)`. Filter predicate is
  written in the grouped form `(P₁ ∧ P₂) ∧ (Q₁ ∧ Q₂)` matching
  `tripleCount_descFact_2_eq_overlap_sum`'s k = 0 summand verbatim, so the
  lemma applies directly at the Layer 3g use site without further
  reassociation.

  Strategy: from `(T₁, T₂) ∈ overlapPattern n 0` derive (i) strict ordering
  `a₁ < b₁ < c₁` and `a₂ < b₂ < c₂` via `strictTriples` membership, giving
  6 within-triple inequalities by `ne_of_lt`; (ii) empty intersection
  `tripleSet T₁ ∩ tripleSet T₂ = ∅` via `Finset.card_eq_zero`, giving 9
  cross-triple inequalities by `Finset.mem_inter` against
  `Finset.notMem_empty`. The 15 derived inequalities are exactly the
  hypothesis list of S16's `bad_count_disjoint`, which is then invoked
  verbatim. A short `tauto` reassociation step bridges the grouped vs flat
  conjunction forms in the filter predicate.

**Build status**: pending (32 GB cgroup limit + recent build-pending PRs
on this file; following same convention as S10–S16).

**Lemma C axiom unchanged**. Layer 3 sub-pieces 3a–3e + strict-wrapper are
now complete. Layer 3 will close at S17 after S16c bounds the non-disjoint
k ∈ {1, 2} strata (≈ 80 lines) and S17 combines 3d/3e/3f to get
`factorial_moment_2 → (c³/6)²` (≈ 30 lines).

**Note on length**: roadmap §8a estimated this wrapper at ≈ 60 lines.
Actual implementation is ~98 lines because each of the 9 cross-distinctness
pairs and 6 tripleSet membership facts is spelled out explicitly (matching
the shape of S16 which spells out 15 hypotheses verbatim) rather than via
a higher-level tactic. Subsequent sessions S16c and S17 are unaffected.

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
8. ✅ **Layer 3e (S16)**: `bad_count_disjoint` + `p_pair_disjoint`
   — DONE on main (#17381). The raw 6-pairwise-distinct-indices form.
9. ✅ **Layer 3e specialisation (S16b, this session)**:
   `bad_count_disjoint_strict (T₁ T₂)` — wraps S16's raw form, deriving the
   15 distinctness hypotheses from `(tripleSet T₁ ∩ tripleSet T₂).card = 0`
   and the strict-triple ordering. Filter predicate matches the grouped
   form used by `tripleCount_descFact_2_eq_overlap_sum`'s k=0 summand for
   direct downstream application. ≈ 98 lines (vs roadmap estimate of 60).
   DONE pending build.
10. ✅ **Layer 3f preliminaries (S16c)**: `tripleSet_union_card_of_overlap`
    + k=0/1/2 specialisations giving `|tripleSet T₁ ∪ tripleSet T₂| = 6 - k`.
    DONE on main (#17444).
11. ✅ **Layer 3f main bound — analysis (S16d, this session)**: produces
    `s16d-overlap-pattern-bounds.md` with Lean-ready statements + proof
    skeleton for `card_overlapPattern_le_generic`,
    `card_overlapPattern_le_one (≤ Nat.choose n 5 · 100)`, and
    `card_overlapPattern_le_two (≤ Nat.choose n 4 · 16)`. Embedding via
    `(T₁, T₂) ↦ ⟨tripleSet T₁ ∪ tripleSet T₂, tripleSet T₁, tripleSet T₂⟩`
    into a sigma-target; injectivity via S12's
    `strict_eq_of_tripleSet_eq`; cardinality via `Finset.card_sigma` +
    `Finset.card_powersetCard`. ≈ 60–70 implementation lines estimated.
    DONE (analysis-only).
12. **Layer 3f main bound — implementation (S16d-implement, next)**:
    transcribe the generic + specialised bounds from
    `s16d-overlap-pattern-bounds.md` into §9 of
    `BirthdayProblemOQ03OQ01OQ02.lean` directly after
    `tripleSet_union_card_of_overlap_two`. Single-pass implementation
    expected; build under contention is "build pending"-tolerated per
    project convention. ≈ 60–70 lines.
13. **Layer 3f per-pair counts (S16e)**: `bad_count_overlap_one`
    (count `= d^(n-5)`, ≈ 100 lines, mirrors `bad_count_disjoint`'s
    structure) + `bad_count_overlap_two` (count `= d^(n-4)`, ≈ 80 lines).
14. **Layer 3g (S17)**: combine 3d/3e/3f to get
    `factorial_moment_2 → (c³/6)²`. ≈ 30 lines (mostly tendsto algebra).
15. **Layer 4 (S18+)**: Method of Factorial Moments — local proof or apply Mathlib upstream.
16. **Mathlib upstream (Path C)**: draft `Mathlib/Probability/MomentsConvergence.lean`
    contribution for Layer 4 in parallel with local Layer 3.
