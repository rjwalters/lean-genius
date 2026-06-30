# Research State: geometric-series-oq-01-oq-02

## Current State

**Phase**: ORIENT — S1 feasibility survey (researcher-6, 2026-06-14). OQ resolved
on paper: the general Cesàro (C,1) regularity theorem reduces to Mathlib's
existing `Filter.Tendsto.cesaro`. Formalizable core pinned to real Mathlib API;
milestones split. No Lean written this session (verification blackout — Docker
down); ACT deferred until build host returns.

**Path**: full
**Since**: 2026-06-14 (S1 ORIENT, researcher-6)
**Last Updated**: 2026-06-14 (Iteration 1, S1 ORIENT, researcher-6)
**Iteration**: 1

## Problem statement

OQ-02 of the follow-up chain rooted at the gallery entry `geometric-series-oq-01`
("Geometric Series at the Boundary: |r| = 1"):

> The general Cesàro summability theorem states that if `∑ aₙ` converges to `s`,
> then its Cesàro mean also converges (to `s`).

This is the **regularity** (a.k.a. consistency) property of (C,1) summation:
ordinary convergence of a series implies Cesàro summability to the **same** sum.
The parent entry `geometric-series-oq-01` already proves the *concrete* Grandi
instance by hand (`grandiCesaro_tendsto : Tendsto grandiCesaro atTop (𝓝 (1/2))`,
via an explicit `|σₙ − 1/2| ≤ 1/(2n)` bound). OQ-02 asks for the **general**
theorem that subsumes such bespoke computations.

## Mathematical resolution (paper)

Let `a : ℕ → ℝ`, partial sums `S N := ∑ i ∈ range N, a i`.

- **Series converges to `s`**  ⟺  `Tendsto S atTop (𝓝 s)`.
- **(C,1)-summable to `σ`**  ⟺  the Cesàro means
  `M N := (N⁻¹ : ℝ) * ∑ k ∈ range N, S k`  satisfy  `Tendsto M atTop (𝓝 σ)`.

**Regularity theorem.** `Tendsto S atTop (𝓝 s)  →  Tendsto M atTop (𝓝 s)`.

**Proof.** Apply Mathlib's `Filter.Tendsto.cesaro` to the sequence `u := S`,
`l := s`. Its conclusion is verbatim
`Tendsto (fun N => (N⁻¹ : ℝ) * ∑ i ∈ range N, S i) atTop (𝓝 s)`,
i.e. `Tendsto M atTop (𝓝 s)`. ∎

So the OQ is a **near-immediate corollary** of existing Mathlib infrastructure —
the only original content is (i) packaging the `CesaroSummable` predicate and the
series→partial-sum bridge, and (ii) wiring the converse-failure illustration.

### Pinned Mathlib API (verified against master 2026-06-14)

`Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean`:

```
/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℕ → E} {l : E} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i ∈ range n, u i) atTop (𝓝 l)

theorem Filter.Tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ range n, u i) atTop (𝓝 l)
```

## Milestones

| ID | Statement | Mathlib hook | Est. LOC | Gate |
|----|-----------|--------------|----------|------|
| **M1** | Regularity: `Tendsto S atTop (𝓝 s) → Tendsto (cesaroMean S) atTop (𝓝 s)`, where `cesaroMean S N = (N⁻¹:ℝ) * ∑ k ∈ range N, S k`. Includes `CesaroSummable` def + series-converges⇒(C,1)-summable corollary. | `Filter.Tendsto.cesaro` (direct) | 15–40 | buildable now (Docker) |
| **M2** | Converse fails: Grandi's series `(fun n => (-1)^n)` is (C,1)-summable to `1/2` (reuse parent `grandiCesaro_tendsto`) yet `¬ Summable` / partial sums divergent (reuse parent `not_summable_grandi`). Demonstrates (C,1) **strictly** extends convergence. | parent `geometric-series-oq-01` lemmas | 20–50 | buildable now (Docker) |

Both milestones are Docker-gated only for *verification*; neither needs missing
Mathlib infrastructure.

## Infrastructure Assessment: Cesàro summability

**Needed**: a named `CesaroSummable` predicate + the regularity bridge from
series convergence (partial-sum `Tendsto`) to the (C,1) mean.
**Mathlib status**: `Filter.Tendsto.cesaro` provides the sequence-average limit
transfer; Mathlib has **no** named series-level `CesaroSummable` predicate.
**Size estimate**: < 80 LOC total (M1 + M2).
**Decision**: BUILD (when Docker returns). No fundamental gap.

## Blockers

- **Verification blackout**: Docker host down this session → cannot run
  `docker-build.sh`. ORIENT (paper + API pinning) complete; ACT deferred.

## Next Action (ACT, when Docker returns)

1. Create `proofs/Proofs/GeometricSeriesOQ01OQ02.lean` importing
   `Mathlib` + `Proofs.GeometricSeriesOQ01`.
2. Define `cesaroMean (S : ℕ → ℝ) (N : ℕ) : ℝ := (N⁻¹ : ℝ) * ∑ k ∈ range N, S k`
   and `CesaroSummable (a : ℕ → ℝ) (σ : ℝ) : Prop`.
3. M1: prove regularity by `exact h.cesaro` after unfolding `cesaroMean`.
4. M2: instantiate Grandi via parent lemmas; state strictness (C,1) ⊋ convergence.
5. Add gallery entry `src/data/proofs/geometric-series-oq-01-oq-02/`
   (meta.json + annotations.json) and build-verify.

## Iteration log

* **S1** (2026-06-14, researcher-6, ORIENT): paper resolution + Mathlib API
  pin (`Filter.Tendsto.cesaro`) + milestone split. No Lean written
  (Docker down). Doc-only ORIENT PR.
