# Session 2026-05-16 (S1) — OBSERVE Bootstrap

**Agent:** researcher-12
**Mode:** FRESH (claim-random)
**Outcome:** scouted; research directory seeded (4 NEW files, 0 Lean / 0 meta.json edits)
**Duration:** ~30 min

---

## 1. Claim Trail

```
.lean/scripts/pick-problem.sh                          → fourier-series-oq-02-oq-01-oq-02 (Tier B, sig 6, tract 5)
.lean/scripts/research-claim.sh ${SLUG} --agent researcher-12
                                                        → Claimed; TTL 60min; expires 2026-05-16T10:44:13Z
```

Pool entry tags: `seeker-selected`, `harmonic-analysis`, `fourier-series`, `l2-spaces`.
Pool notes: `AVAILABLE`.

---

## 2. Initial Discovery

| Check | Result |
|-------|--------|
| `research/problems/${SLUG}/` | **does not exist** |
| `src/data/proofs/${SLUG}/` | **does not exist** (no gallery entry) |
| `src/data/research/problems/${SLUG}.json` | **does not exist** |
| `gh pr list --state all --search "${SLUG}"` | `[]` (no PRs ever) |
| Knowledge score | **EMPTY** (0 insights / 0 builtItems / 0 mathlibGaps / 0 nextSteps) |
| Parent `fourier-series-oq-02-oq-01` gallery | Exists; ℂ-valued Hölder RL via L²; ~83 LOC; 0 sorries / 0 axioms; lists this slug as `openQuestions[0]`: "Does the proof generalize to vector-valued functions (f : AddCircle T → E for Banach E) using MemLp for Bochner integrals?" |

This matches the feedback-memory pattern
`feedback_researcher_claim_random_lands_on_rich_tier_slug_with_no_research_dir_gallery_only_doc_only_s1_observe_bootstrap`,
except **this slug additionally has no gallery** — the seeker generated it from the parent's
`openQuestions` field, but no formalization has ever been attempted.

**Decision:** 4-file doc-only S1 OBSERVE bootstrap; 0 Lean / 0 meta.json edits.

## 2.5 Host Infrastructure Snapshot

| Check | Value | Status |
|-------|-------|--------|
| `df -h /System/Volumes/Data` available | 6.9 Gi (100% used) | **CRITICAL** |
| `timeout 30 docker ps -q` | (hung, no output, no error) | **DAEMON HUNG** |
| `timeout 30 docker info --format '{{.ServerVersion}}'` | (hung) | **DAEMON HUNG** |

Bootstrap is PREP-safe at this infra state (no Lean build, no meta.json edit).
S3+ ACT cycles will require host recovery.

---

## 3. Mathlib Audit (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0)

### Already E-valued in Mathlib
- `Mathlib/Analysis/Fourier/AddCircle.lean:297` —
  ```lean
  variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  def fourierCoeff (f : AddCircle T → E) (n : ℤ) : E := ∫ t, fourier (-n) t • f t ∂haarAddCircle
  ```
  Already general E. Bochner integral.

### Mathlib's ℂ-only Parseval pipeline
- `Mathlib/Analysis/Fourier/AddCircle.lean:408` `hasSum_fourier_series_L2 (f : Lp ℂ 2 haarAddCircle)`
  uses `HilbertBasis.hasSum_repr fourierBasis f`. Intrinsically ℂ-valued via `fourierBasis`.
- `:415` `hasSum_sq_fourierCoeff (f : Lp ℂ 2 haarAddCircle)` — Parseval (Σ ‖ĉ_n‖² = ‖f‖²).
- `:430` `tsum_sq_fourierCoeff` — tsum form.

### Local gallery (ℂ-only)
- `proofs/Proofs/FourierSeries.lean:417` `fourierCoeff_tendsto_zero (f : Lp ℂ 2 ...)`
  — RL for ℂ-valued L²; proof uses Parseval-summability + `‖ĉ_n‖² → 0 ⇒ ĉ_n → 0`.

---

## 4. Branch Decision

Two natural branches for "generalize to E-valued":

| Branch | E typeclass | Method | Status |
|--------|-------------|--------|--------|
| **Hilbert E** | `[InnerProductSpace ℂ E] [CompleteSpace E]` + separability | Componentwise reduction (Option C in knowledge.md §3.6) | **PRIMARY** for first ACT cycle |
| **Banach E** | `[NormedSpace ℂ E] [CompleteSpace E]` (no inner product) | L¹ density of trig polynomials | Secondary; defer to separate slug |

**Why Hilbert first:**
- Parent's proof uses Parseval; cleanest port preserves that backbone.
- Banach E requires fundamentally different argument (L¹ density), so it's a separate
  slug-worth of work, not a within-slug variant.

**Why Option C over Options A/B/D:**
- Option A (tensor product `(Lp ℂ 2) ⊗ E`): heavy machinery, deep Mathlib internals.
- Option B (bypass HilbertBasis, hand-roll Parseval for E): probably 200-300 LOC of
  inner-product-distributes-over-Bochner-integral lemmas.
- Option D (norm-shortcut via `fourierCoeff ‖f‖`): **does not work** — see §3.5 in knowledge.md.
- Option C: reduces to parent's ℂ-theorem applied per coordinate, plus basis Pythagoras +
  DCT-swap. Most leverage on existing infrastructure.

---

## 5. Key Insight (R2 Mitigation Sketch)

The DCT-swap step in Option C — "Σ_k |fourierCoeff f_k n|² → 0 as |n| → ∞" — requires a
uniform-in-n bound to apply Dominated Convergence Theorem.

**Bound:** For each `n`,
```
  Σ_k |fourierCoeff f_k n|²
≤ Σ_k ‖f_k‖²₂              (Parseval applied to f_k separately, ℂ-version)
= Σ_k ∫ |⟨f(x), e_k⟩|² dμ(x)
= ∫ Σ_k |⟨f(x), e_k⟩|² dμ(x)      (Tonelli, non-negative integrands)
= ∫ ‖f(x)‖²_E dμ(x)             (basis Pythagoras in E)
= ‖f‖²_{L²(μ; E)}                (finite by hypothesis)
```

This is uniform in `n` and finite, satisfies DCT hypothesis. Each summand `|fourierCoeff f_k n|² → 0`
as `|n| → ∞` (parent ℂ-RL applied to `f_k`). Therefore the sum `→ 0`, i.e.
`‖fourierCoeff f n‖² → 0`, hence `fourierCoeff f n → 0`.

**Remaining S2 work:** verify Mathlib provides
- `HilbertBasis.tsum_inner_sq_eq_norm_sq` or similar (E-Pythagoras step),
- `MeasureTheory.lintegral_tsum` or `tsum_lintegral_le` (Tonelli swap),
- the parent's `fourierCoeff_tendsto_zero` (already verified, file:417).

---

## 6. Bearer Pins (Verified This Cycle)

```
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Fourier/AddCircle.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.size'
  → 26635
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean?ref=2df2f0150c… --jq '.size'
  → 14732
```

B1, B2 verified. B3 (`InnerProductSpace/l2Space.lean`) and B4 (`MeasureTheory/Integral/Bochner/Basic.lean`)
deferred to S2 ORIENT pin-recheck.

---

## 7. Files Modified This Cycle

**4 NEW files** in `research/problems/fourier-series-oq-02-oq-01-oq-02/`:
- `problem.md` — formal statement (Hilbert-E + Banach-E variants), prior art, acceptance criteria.
- `knowledge.md` — 10-section knowledge survey: branch decision, Mathlib audit, infrastructure
  assessment, 8-phase plan, bearer pins, R1-R8 risk inventory.
- `state.md` — Phase OBSERVE; next-action S2 ORIENT; B1 INFRA blocker (Docker daemon hung).
- `sessions/2026-05-16-s1-observe-bootstrap.md` — this file.

**0 Lean edits. 0 meta.json edits. 0 problem-JSON edits.**

---

## 8. Pool / JSON Drift (Not Fixed This PR)

| Item | Current state | Action |
|------|---------------|--------|
| `.lean/state/candidate-pool.json` entry `status` | `available` | Will release lock at end-of-cycle; pool sync via lock removal (gitignored). |
| `src/data/research/problems/<slug>.json` | does not exist | Defer to first ACT cycle (S3+) once knowledge accumulation justifies; per existing pattern. |

These are NOT drift — they reflect correct state of an EMPTY-tier slug at OBSERVE phase.

---

## 9. Next-Cycle Cue (S2 ORIENT, doc-only PREP)

1. Pin-recheck B3, B4 at fresh Mathlib pin.
2. Confirm exact signatures of `HilbertBasis.tsum_inner_sq_eq_norm_sq` (or local equivalent),
   `MeasureTheory.lintegral_tsum`, and the `f_k(x) := ⟨f(x), e_k⟩` measurability lemma.
3. Draft ~80 LOC paste-ready skeleton for S3 ACT-a:
   - `def fourierCoeff_component`
   - `lemma fourierCoeff_eq_tsum_component`
   - `theorem riemannLebesgue_holder_vec_via_L2` with 2-4 placed sorries on Pythagoras + DCT swap.
4. Update bearer-pin table in `knowledge.md` §6 with B3, B4 sizes + line numbers.

**Forecast:** S2 PREP ~30-40 min, doc-only; pin-recheck table grows from 4 to 6 entries.

---

## 10. Lessons (for memory)

- **Seeker-generated slug + no gallery + no PRs ever = doc-only bootstrap.** Pattern matches
  the existing memory `_claim_random_lands_on_rich_tier_slug_with_no_research_dir_gallery_only_doc_only_s1_observe_bootstrap`,
  but distinct in lacking the gallery entirely (memory pattern assumed gallery exists with
  ≥1 axiom). New variation worth noting.
- **`fourierCoeff` already E-valued in Mathlib.** The "generalize" framing in the seeker's
  pool notes is misleading — half the generalization is already done; what's missing is the
  Parseval-RL pipeline for E.
- **Norm-shortcut Option D is a trap.** Anyone glancing at the problem might think
  `‖ĉ_n[f]‖ → 0` reduces to `‖f‖ : T → ℝ`'s RL, but the obvious triangle inequality
  `‖ĉ_n[f]‖ ≤ ‖f‖₁` is just a uniform bound, not decay. Documented in §3.5 of knowledge.md
  to prevent future researchers from going down this path.
