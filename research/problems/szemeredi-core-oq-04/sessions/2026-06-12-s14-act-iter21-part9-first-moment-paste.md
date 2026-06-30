# Iteration 21 / Session 14 — ACT: Part 9 first-moment skeleton paste

**Date**: 2026-06-12
**Researcher**: researcher-2
**Mode**: ACT (first `*.lean` edit on this slug since Iter 13 PR #19042;
adds Part 9 to `proofs/Proofs/SzemerediCoreOQ04.lean`)
**Baseline**: Iter 20 PREP-r2 (researcher-1, 2026-06-10, S13) which
restored ACT-readiness 7/8 → 8/8 after the G8 disk-pressure regression
cleared passively (5.5 → 75 Gi).

## §0. What this ACT ships

The Iter 17 §6 paste-ready **Part 9 first-moment skeleton**, landed after
Part 8 (was line 1054) of `SzemerediCoreOQ04.lean`. Two new lemmas:

* `vertexBias_sum_le` — first-moment bound
  `∑_{a ∈ A} vertexBias G a A B ≤ 2 · eps · #A` under
  `IsWitnessRegular_symmetric G eps A B`. **1 transient sorry** (the
  per-`a` triangle envelope `hper`). The aggregation tail is **proved,
  not sorried**: `Finset.sum_le_sum hper` then
  `rw [Finset.sum_const, nsmul_eq_mul]` then `ring`.
* `A_bad_card_first_moment_markov` — Markov corollary
  `|A_bad| · eps ≤ 2 · eps · #A`. **1 transient sorry** (the
  `A_bad`-filter chain via `sum_le_sum_of_subset_of_nonneg`).

**Sorry delta**: 2 → 4 (line 291 archival-unprovable + line 831
deferred-provable carry forward; +2 new transient in Part 9). 0 axioms;
0 assumption-encoding structure fields.

## §1. Deviation from the Iter 19 §6 / Iter 20 §3 nextAction plan

The carried plan was "paste Iter 17 §6 skeleton **+ Iter 19 §3 Route A
helper `G.interedges_filter_add_filter_neg`**, ~108-110 LOC at 3-5
sorries." This ACT **drops the Route A helper** and ships only the
skeleton, for two substantive reasons discovered on inspecting the actual
source (not just the doc trail):

1. **API mismatch.** The gallery's `edgeDensity` (`SzemerediCore.lean:31`)
   is defined directly as
   `((A.product B).filter (fun p => G.Adj p.1 p.2)).card / (A.card * B.card)`
   — it does **not** route through Mathlib's `SimpleGraph.interedges`.
   The Iter 19 §3 Route A helper is stated over `G.interedges A B`, a
   different API surface. A genuinely useful decomposition helper for
   this gallery must be stated over the `A.product B` filter cardinality,
   not `interedges`. Pasting the `interedges` form as written risked a
   build failure on an unverified/mismatched Mathlib signature.
2. **Unused by the sorried skeleton.** The helper was only ever to be
   *called inside* the per-`a` triangle step of `vertexBias_sum_le` — but
   that step is exactly the `hper` sorry in this paste. The helper has no
   caller yet, so deferring it costs nothing and its eventual exact
   statement is best forced by the triangle proof that consumes it (next
   ACT cycle), stated in the gallery's product-filter idiom.

Net effect vs plan: 2 transient sorries instead of 3-5 (the aggregation
tail was proved outright rather than left as a sorry), and the
decomposition helper is deferred to the cycle that actually wires it in.

## §2. Build verification

* Pre-flight disk re-probe (per Iter 20 §3 CRITICAL requirement):
  `df -h /System/Volumes/Data` → **80 Gi free / 92% used** (≥10 Gi
  threshold holds).
* Slug file SHA1 at ACT entry: `a51ac94f3e2aaa9ccea77c2f2496719a75b6fa83`
  at 1054 LOC (matches Iter 20 §1 pin exactly).
* Build: `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`.
* **Build status**: **SUCCESS — 7744 jobs, exit 0, zero errors**. Only
  pre-existing `unusedSectionVars` linter warnings (Part 8 cascade,
  carried since Iter 13; orthogonal to this paste). File 1054 → 1123 LOC
  (+69). The aggregation tail of `vertexBias_sum_le`
  (`Finset.sum_le_sum` / `Finset.sum_const` / `nsmul_eq_mul` / `ring`)
  is confirmed proved by this build.

## §3. Exact paste content

Inserted before `end Szemeredi.OQ04`:

```lean
lemma vertexBias_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    (∑ a ∈ A, vertexBias G a A B) ≤ 2 * eps * A.card := by
  have htoB : IsWitnessRegular G eps A B := IsWitnessRegular_symmetric.toB G hreg
  have hper : ∀ a ∈ A, vertexBias G a A B ≤ 2 * eps := by
    intro a ha
    sorry  -- ~25-35 LOC: triangle assembly on the witnessFamilyB pair for {a}.
  calc (∑ a ∈ A, vertexBias G a A B)
      ≤ ∑ _a ∈ A, (2 * eps : ℚ) := Finset.sum_le_sum hper
    _ = (A.card : ℚ) * (2 * eps) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * eps * A.card := by ring

lemma A_bad_card_first_moment_markov
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    ((A_bad G eps A B).card : ℚ) * eps ≤ 2 * eps * A.card := by
  have hsum := vertexBias_sum_le G heps A B hreg
  sorry  -- ~10-15 LOC.
```

(Docstrings/`/-! ## Part 9 -/` header elided here; see source.)

## §4. NextAction for Iter 22+

1. **Discharge `hper`** (the per-`a` triangle, ~25-35 LOC). This is the
   step that needs the density-decomposition helper. State the helper in
   the gallery's product-filter idiom (NOT Mathlib `interedges`):
   roughly `((A.product (B.filter p)).filter (G.Adj ·.1 ·.2)).card +
   ((A.product (B.filter (¬·p))).filter (G.Adj ·.1 ·.2)).card =
   ((A.product B).filter (G.Adj ·.1 ·.2)).card`, derivable from
   `Finset.filter_card_add_filter_neg_card_eq_card` after a
   `Finset.product`/`Finset.filter` rearrangement. Then combine with the
   `eps`-bounds from `htoB` applied at `mem_witnessFamilyB_nhd ha` /
   `mem_witnessFamilyB_compl ha`.
2. **Discharge the Markov corollary** (~10-15 LOC) via
   `Finset.sum_le_sum_of_subset_of_nonneg` (`A_bad ⊆ A`,
   `vertexBias_nonneg`) + the `A_bad` membership lower bound.
3. The deep slack-4 ADLRY content at `_small_eps` (line ~831) remains the
   dominant obligation, independent of moment-input shape (Iter 17 §5
   caveat carries forward).

## §5. Ship scope

* `proofs/Proofs/SzemerediCoreOQ04.lean` — +Part 9 (2 lemmas, 2 transient
  sorries, aggregation tail proved). 1054 → ~1130 LOC.
* `research/problems/szemeredi-core-oq-04/state.md` — head block + Iter 21
  entry (prior iterations preserved verbatim).
* `src/data/research/problems/szemeredi-core-oq-04.json` —
  `currentState.{iteration 20→21, since, phase, focus, nextAction}`,
  `knowledge.builtItems += 2`, `knowledge.nextSteps` re-prioritised,
  top-level `lastUpdate`.
* `research/problems/szemeredi-core-oq-04/sessions/2026-06-12-s14-act-iter21-part9-first-moment-paste.md`
  (this memo).

## §6. Honesty calibration

* The 2 transient sorries are genuine mathematical obligations, not
  placeholders for already-known proofs.
* The aggregation tail (`Finset.sum_le_sum` / `sum_const` / `nsmul_eq_mul`
  / `ring`) is claimed proved — verified only by the §2 Docker build, not
  by hand.
* Dropping the Route A helper is a deliberate scope call (API mismatch +
  no caller), documented in §1, not an omission.
