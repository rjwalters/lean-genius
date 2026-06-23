# S2 — Mathlib audit of `cornersTheoremBound`; commit to Approach A; spin off Approach B

**Slug**: `szemeredi-theorem-oq-01`
**Phase**: ORIENT → DECISION (commit-to-Approach-A)
**Author**: researcher-1
**Date**: 2026-05-30
**Base**: `origin/main`
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**Predecessor**: S1 OBSERVE → ORIENT survey (researcher-?, 2026-05-30, same day; see `knowledge.md` Session 1)

## 1. Audit target

S1 OBSERVE flagged the slug's path-forward decision as gated by **open question 1**:

> Does `Mathlib.Combinatorics.Additive.Corner.Roth` give a tower-type
> bound or already a polynomial / quasi-polynomial bound? (Mathlib audit
> needed before Approach B is committed to.)

The slug's decision tree (`state.md` "Next Action") branches:

- **If `cornersTheoremBound` already gives explicit `O(N / log log N)` constants** → commit to Approach B (Salem-Spencer quantitative, ~50-150 LOC).
- **If `cornersTheoremBound` is tower-type / opaque** → commit to Approach A (axiomatize Kelley-Meka, ~30 LOC); spin off Approach B into a sibling problem `szemeredi-theorem-oq-01-incomplete-01`.

This S2 audit resolves the open question and commits to one branch.

## 2. Method

Fetched `Mathlib/Combinatorics/Additive/Corner/Roth.lean` at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via:

```
curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Combinatorics/Additive/Corner/Roth.lean"
```

Inspected the definition and docstring of `cornersTheoremBound`.

## 3. Finding

The Mathlib file is **explicit** about the bound's quantitative nature. Quoting `Mathlib/Combinatorics/Additive/Corner/Roth.lean` (verbatim, lines reported at fetch time; pin SHA above):

```lean
/-- An explicit form for the constant in the corners theorem.

Note that this depends on `SzemerediRegularity.bound`, which is a tower-type exponential.
This means `cornersTheoremBound` is in practice absolutely tiny. -/
noncomputable def cornersTheoremBound (ε : ℝ) : ℕ :=
  ⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1
```

**The Mathlib authors themselves flag this as tower-type.** The full chain:

```
cornersTheoremBound (ε)
  = ⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1
       └── triangleRemovalBound depends on SzemerediRegularity.bound
            └── SzemerediRegularity.bound is a tower-type exponential
```

The downstream Roth theorem (`roth_3ap_theorem` and `roth_3ap_theorem_nat`) is stated using `cornersTheoremBound`:

```lean
theorem roth_3ap_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G)
    (A : Finset G) (hAε : ε * card G ≤ #A) : ¬ ThreeAPFree (A : Set G) := by ...
```

So the *form* of the Roth bound in Mathlib at this pin is:

> For every `ε > 0`, every finite abelian group `G` with `card G ≥ cornersTheoremBound ε`, and every `A ⊆ G` with `#A ≥ ε * card G`, the set `A` is not 3AP-free.

This is **density form**, not **explicit-constant form**. To extract `O(N / log log N)` (or any specific quantitative bound on `r_3(N)`) one would have to *invert* the dependence — given a target bound on `r_3(N) / N`, solve for the smallest `ε` for which the conclusion fires, then bound `cornersTheoremBound ε` from above. Doing this for the **tower-type** `cornersTheoremBound` would not yield `O(N / log log N)`; it would yield a vastly weaker `O(N / log* N)`-style "tower-tower" bound that is not the Roth-quantitative form Approach B targets.

## 4. Decision

**Commit to Approach A** (axiomatize Kelley-Meka). Per the S1 OBSERVE Section 3 estimates:

- Approach A: ~30 LOC, axiomatize the Kelley-Meka statement `r_3(N) ≤ N · exp(-c (log N)^{1/12})` directly. Status: `axiomatized`, badge `axiom`. Provides a citeable hook with no new mathematical content. **This is the right call** given the Mathlib gap (no Bohr-set, no sifted-Fourier, no `U^3`-uniformity infrastructure).
- Approach B: spin off into sibling `szemeredi-theorem-oq-01-incomplete-01`. **Cannot deliver `O(N / log log N)` from `cornersTheoremBound` as written** (tower-type). The spin-off would either need to (a) wait for upstream Mathlib to deliver a sharper Roth bound (requires Kelley-Meka itself, circular) or (b) document the Mathlib gap as a research blocker and stay at SURVEY for the foreseeable future.

The slug's `state.md` "Next Action" branch is fully resolved by this audit:
*opt-A taken; opt-B spun off.*

## 5. What this PR ships

**Doc-only. No Lean code.**

- `sessions/2026-05-30-s2-mathlib-audit-cornersTheoremBound.md` (new, this file): the audit memo with the verbatim Mathlib docstring evidence.
- `knowledge.md`: append new Session 2 entry recording the audit finding and the decision to commit to Approach A. Open question 1 resolved (tower-type). Approach B downgraded to "blocked on Mathlib infrastructure; spin off recommended".
- `state.md`: Phase ORIENT → DECISION-RECORDED; Iteration 2 → 3; Active Approach narrowed to **A only** (Approach B moved to a spin-off note); Next Action rewritten to point at the Approach A axiomatize step (~30 LOC, single `axiom` declaration in a new file `proofs/Proofs/SzemerediTheoremOQ01.lean`).

The actual Approach A axiomatize is **deferred to a separate session** — this PR ships the audit + decision only. Rationale:
- Researcher session has already shipped one solid Lean ACT (`stdLatticeN_coords` for `minkowski-theorem-oq-02-oq-03`, PR #21239) earlier in the same loop. Adding a second Lean deliverable in the same session would risk over-committing context to one researcher iteration.
- The audit is a self-contained, dispatchable deliverable that unblocks the next claimant to ship Approach A in ~30 LOC.

## 6. Spin-off recommendation (Approach B)

Recommend the next seeker / curator iteration extract a sibling slug:

- **ID**: `szemeredi-theorem-oq-01-incomplete-01`
- **Title**: "Salem-Spencer quantitative Roth: extract explicit `O(N / log log N)` from Mathlib's tower-type `cornersTheoremBound`"
- **Status at extract**: BLOCKED — Mathlib's `cornersTheoremBound` is tower-type per its own docstring; deriving `O(N / log log N)` from it is mathematically inverted (one needs the sharper bound first to set the inversion).
- **Path forward**: track upstream Mathlib PRs that strengthen `cornersTheoremBound`. If/when Bohr-set or `U^3`-uniformity infrastructure lands upstream, re-evaluate viability.
- **Honest framing**: this is a **deferred** slug, not a quick win. Listed as a "blocked on upstream infra" candidate.

## 7. Files touched (this PR)

| File | Change |
|---|---|
| `research/problems/szemeredi-theorem-oq-01/sessions/2026-05-30-s2-mathlib-audit-cornersTheoremBound.md` | new (this file) |
| `research/problems/szemeredi-theorem-oq-01/knowledge.md` | append Session 2 entry (audit + decision) |
| `research/problems/szemeredi-theorem-oq-01/state.md` | Phase / Iteration / Active Approach / Next Action refresh |
| `src/data/research/problems/szemeredi-theorem-oq-01.json` | currentState.phase / iteration / focus / nextAction refresh; knowledge.builtItems append; lastUpdate bump |

**Not touched**: `problem.md` (problem statement stable; the *direction* changes but the statement does not), `proofs/` (no Lean changes), gallery `src/data/proofs/...` (no gallery surface for this slug yet), sibling slugs, `lake-manifest.json`.

## 8. Honest status

- **Mathematical content shipped**: 0 — pure audit + decision.
- **Slug advancement**: Phase ORIENT → DECISION-RECORDED. The next iteration ships Approach A (~30 LOC axiomatize). Total estimated remaining work to `axiomatized` graduation: ~30 LOC Lean + gallery entry (~50 lines JSON) = small.
- **Mathlib pin drift risk**: low. Mathlib's `cornersTheoremBound` has been tower-type since its introduction; the next non-trivial upstream change would require Kelley-Meka-level work, which is years away in Mathlib.
- **No build attempted**: doc-only PR.
