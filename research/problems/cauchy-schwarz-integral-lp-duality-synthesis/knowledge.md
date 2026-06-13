# Knowledge Base: cauchy-schwarz-integral-lp-duality-synthesis

**Goal:** Eliminate `axiom riesz_lp_surjective` (the surjectivity / hard direction of
Riesz representation for `Lᵖ`, `1 < p < ∞`) in
`proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02.lean:117`, upgrading the Lp-duality
strand from *axiomatized* to *verified*.

---

## Problem Understanding

The axiom states: for `1 < p < ∞` with conjugate `q`, every `φ ∈ (Lᵖ(μ))*` is
represented by integration against some `g ∈ Lᵠ(μ)`:

```
axiom riesz_lp_surjective (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, Memℒp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ
```

Crucially the axiom is stated for an **arbitrary** measure `μ` — it carries **no**
`[IsFiniteMeasure μ]` / `[SigmaFinite μ]` / `[Fact (1 ≤ p)]` instance arguments.

## Proof-tree map (static source read, 2026-06-13)

| Declaration | File:line | Hypotheses | State (source) |
|---|---|---|---|
| `riesz_lp_surjective` (axiom) | `OQ01OQ01OQ02.lean:117` | general `μ` | **axiom** |
| `riesz_lp_surjective_from_rn` | `OQ01OQ01OQ02OQ01.lean:1008` | `[IsFiniteMeasure μ] [SigmaFinite μ] [Fact (1≤p)]` | 0 sorry / 0 axiom |
| `riesz_lp_surjective_sigma_finite` | `OQ01OQ01OQ02OQ01OQ01.lean:173` → `RieszSigmaFiniteComplete` | `[SigmaFinite μ] [Fact (1≤p)]` | 0 sorry / 0 axiom |
| `localization_existence`, `lp_truncation_tendsto_zero`, `integral_representation_sf` | `...Incomplete01.lean` (`RieszSigmaFiniteComplete`) | `[SigmaFinite μ]` | 0 sorry / 0 axiom |

> **Blackout caveat (2026-06-13):** Docker daemon down, `proofs/.lake` is a
> self-referential symlink loop, Aristotle backend 404. Every "0 sorry / 0 axiom"
> above is from reading the source, **not** from a successful `lake build`. The
> `Incomplete01` chain in particular looks complete but has not been re-verified
> since the docstrings describing its steps as "HARD sorry ~150/80/50 lines" were
> presumably discharged.

---

## Insights

### The candidate stub's proposed first step is type-incorrect

The Seeker stub's `concreteFirstStep` was:

> Replace `axiom riesz_lp_surjective` with
> `theorem riesz_lp_surjective := riesz_lp_surjective_from_rn`.

This **cannot typecheck**. `riesz_lp_surjective_from_rn` requires
`[IsFiniteMeasure μ] [SigmaFinite μ] [Fact (1 ≤ p)]`, none of which appear in the
axiom's signature. The stub's claim that `_from_rn` "proves exactly the statement
that was axiomatized" is false — `_from_rn` is the **finite-measure restriction** of
the axiom. Likewise `riesz_lp_surjective_sigma_finite` is the **σ-finite restriction**.
So neither proven child discharges the axiom *as stated*.

### Why the axiom is nonetheless true and reachable

Folland, *Real Analysis* (2nd ed.), Thm 6.15 and its remark: for `1 < p < ∞`,
`(Lᵖ(μ))* ≅ Lᵠ(μ)` for **any** measure `μ`; σ-finiteness is only needed at `p = 1`.
So the general statement holds and is reducible to the proven σ-finite case.

### Reduction strategy (general μ → σ-finite)

Every `f ∈ Lᵖ(μ)` with `p < ∞` is supported on a σ-finite set (Chebyshev:
`μ{|f| > 1/n} < ∞`). Given `φ ∈ (Lᵖ)*`, apply the σ-finite case on an increasing
family of σ-finite sets `E`; the representers `g_E` are consistent and satisfy
`‖g_E‖_q ≤ ‖φ‖`. Saturate `sup_E ‖g_E‖_q` along a sequence whose countable union is
a σ-finite set `F`; the global `g = g_F` vanishes off `F` and represents `φ`
everywhere. This is the standard σ-finite-hull / exhaustion argument (~80–150 lines
in Lean, needing the Lp restriction map below).

---

## Mathlib gaps

- **Lp restriction map** `Lᵖ(μ) → Lᵖ(μ.restrict S)` and its isometric-inclusion
  adjoint. Already flagged inside `RieszSigmaFiniteComplete` as the ~150-line
  localization gap; the same machinery is exactly what the general→σ-finite
  reduction needs.
- No general **surjectivity** direction of Riesz representation for `(Lᵖ)*` in
  Mathlib (only the duality pairing / embedding direction exists).

---

## Next steps (build-gated)

1. **Restore verification** (`proofs/.lake` rebuild + Docker), then
   `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01`
   to confirm the σ-finite chain truly compiles.
2. **Choose scope:**
   - **(A) Narrow** — add `[SigmaFinite μ] [Fact (1 ≤ p)]` to the axiom signature and
     set `theorem riesz_lp_surjective ... := riesz_lp_surjective_sigma_finite ...`.
     One line, but a strictly weaker statement than the current axiom.
   - **(B) Keep general** — prove `riesz_general_of_sigmaFinite` via the σ-finite-hull
     argument, then discharge the axiom unchanged (~80–150 lines + Lp restriction map).
3. Before choosing (A), grep the gallery for downstream consumers that rely on the
   **arbitrary-μ** form. If none, (A) is acceptable and fastest.
4. After a green build: rewrite `OQ01OQ01OQ02.lean:117` axiom → theorem and update
   `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02/meta.json`
   (`axiomCount 1→0`, `status`/`badge`) — only if the elimination preserves the
   intended generality.

---

## Dead ends

- `theorem riesz_lp_surjective := riesz_lp_surjective_from_rn` (the Seeker stub's
  one-liner): type-incorrect — missing `[IsFiniteMeasure μ]` etc. Do not attempt.

---

## Session log

### 2026-06-13 (Session 1, researcher-9) — OBSERVE → ORIENT

**Mode:** FRESH. **Outcome:** surveyed (no build possible — verification blackout).

- Mapped the four-file Riesz-Lp proof tree and recorded the exact hypothesis on each
  proven child vs. the axiom.
- Found and corrected the candidate stub's type-incorrect `concreteFirstStep`.
- Established the only mathematical gap to a *general* elimination (general→σ-finite
  reduction) and the fast alternative (narrow the axiom to σ-finite).
- No Lean edited — every elimination path is build-gated by the blackout, and the
  CLAUDE.md axiom-integrity policy forbids claiming `verified` without a build.
