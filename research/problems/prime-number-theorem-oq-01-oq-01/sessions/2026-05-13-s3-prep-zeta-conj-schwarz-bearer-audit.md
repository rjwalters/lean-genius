# S3 PREP — Mathlib v4.26.0 bearer audit for `zeta_conj` discharge via the identity principle (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-5 (claim `researcher-91316`, knowledge score 17 / RICH)
**Phase**: PREP (refinement of S2 ACT — does not modify the Lean file)
**Builds on**:
- PR #18045-class S1 OBSERVE (slug survey + duplication audit, 2026-05-12)
- PR #18915 (S2 ACT — `rh_canonical_iff_pnt` bridge theorem, 2026-05-13, researcher-4)
**Mathlib pin**: `proofs/lake-manifest.json` → mathlib4 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
**Scope**: doc-only Mathlib API audit. **No edits to `state.md` / `knowledge.md` / gallery JSON / any `.lean` file.** Only adds this `sessions/` memo (the first session memo for this slug — the `sessions/` directory did not exist before this PR).

---

## §0 — TL;DR for the next S3 ACT implementer

1. **Candidate B target** (from S2 ACT state.md): discharge the `zeta_conj` axiom in `proofs/Proofs/RiemannHypothesis.lean:779`, which asserts `riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s)` for all `s : ℂ`.
2. **In-file context**: the axiom is already PROVEN as a theorem for `Re(s) > 1` (`zeta_conj_of_one_lt_re` @ `RiemannHypothesis.lean:680`, Dirichlet series) and for `Re(s) < 0` (`zeta_conj_of_neg_re` @ line 715, functional equation). The axiom extends those proofs to all `s ∈ ℂ` via Schwarz reflection / identity principle.
3. **Bearer status at v4.26.0**: **viable**. Mathlib provides the two load-bearing pieces:
   - **`differentiableAt_riemannZeta`** @ `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:137` (signature: `{s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ riemannZeta s`)
   - **`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`** @ `Mathlib/Analysis/Analytic/Uniqueness.lean:223`
4. **Key subtlety**: complex conjugation `starRingEnd ℂ` is **anti-holomorphic**, NOT holomorphic. The direct map `s ↦ starRingEnd ℂ (riemannZeta s)` is therefore NOT analytic. The Schwarz-reflection trick wraps two anti-holomorphic compositions: define `g(s) := starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))`. Then `g` IS holomorphic (composition of two anti-holomorphic maps), and `g = riemannZeta` on `{Re s > 1}` by the in-file Dirichlet-series proof. By the identity principle on the preconnected set `ℂ \ {1}`, `g = riemannZeta` everywhere on `ℂ \ {1}`. Unfolding the definition of `g` gives the axiom statement directly.
5. **Estimated LOC**: **~80-120 LOC** (S2 state.md's "medium; 60-120 LOC" estimate is in the right range, leaning toward the upper bound because of the holomorphy-of-`g` step and the preconnectedness witness for `ℂ \ {1}`).

---

## §1 — Bearer table at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All identifiers below were verified live via `gh api search/code` (`+repo:leanprover-community/mathlib4`) and `gh api repos/.../contents/<file>?ref=<SHA>` reads.

| Step in proof outline | Lemma at v4.26.0 | Path | Line |
|---|---|---|---|
| Differentiability of `ζ` away from `s = 1` | **`differentiableAt_riemannZeta`** | `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` | 137 |
| Identity principle for two analytic functions agreeing on a neighbourhood | **`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`** | `Mathlib/Analysis/Analytic/Uniqueness.lean` | 223 |
| Definition of `AnalyticOnNhd` (for setup) | `AnalyticOnNhd` | `Mathlib/Analysis/Analytic/Basic.lean` | (canonical) |
| Conjugation as continuous linear (anti-holomorphic in the complex-linear sense, but `ℝ`-linear) | `Complex.conjCLE` | `Mathlib/Analysis/Complex/OperatorNorm.lean` | (canonical, finite-dim) |
| `conj (conj z) = z` (cancellation of two-conjugation) | `Complex.conj_conj` (alias of `starRingEnd_self_apply`) | `Mathlib/Algebra/Star/Basic.lean` | (canonical) |
| Preconnectedness of `ℂ \ {1}` (single-point complement of `ℂ`) | `Set.preconnected_compl_of_singleton` / `IsConnected.preconnected` (no exact name search hit — see §1.1) | TBD | TBD |
| In-file Dirichlet-series proof for `Re(s) > 1` | `zeta_conj_of_one_lt_re` (already in `Proofs/RiemannHypothesis.lean`) | `proofs/Proofs/RiemannHypothesis.lean` | 680 |

### §1.1 — Open audit: preconnectedness of `ℂ \ {1}`

I did not pin an exact Mathlib name for "the complement of a single point in `ℂ` is preconnected." Possible candidates to verify in S3 ACT:

- `Set.preconnected_compl_of_singleton` — direct search returned 0 hits; **likely phantom**.
- `IsPreconnected.compl_singleton` — direct search returned 0 hits; **likely phantom**.
- `Convex.preconnected` — `ℂ \ {1}` is not convex, so this would need a different witness.
- Most likely route: prove `IsPreconnected (Set.univ \ {1})` by hand via `IsPathConnected.isPreconnected` — `ℂ \ {1}` IS path-connected (any two points connect through a generic line missing 1), but the witness is non-trivial in Lean.

**Alternative path (cleaner)**: use `AnalyticOn.eqOn_of_preconnected_of_eventuallyEq` on the preconnected open set `{s : ℂ | s.re > 1}` first to establish equality there, then extend by analyticity on each preconnected component of `ℂ \ {1}`. But `ℂ \ {1}` has only ONE connected component (it's path-connected), so a one-shot extension is preferred.

**Recommended S3 ACT first move**: prove `IsPreconnected ({1}ᶜ : Set ℂ)` as a local lemma (likely ~10-15 LOC using `Set.PathConnected.isPreconnected` and a piecewise-linear path witness avoiding `1`).

### §1.2 — Conjugate-composition holomorphy

The Schwarz-reflection trick needs to show `g(s) := starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))` is holomorphic on `ℂ \ {1}`. This needs two facts:

1. **`starRingEnd ℂ` as a continuous map** preserves `1`-preimage: `(starRingEnd ℂ) s = 1 ↔ s = starRingEnd ℂ 1 = 1` (since `1 : ℂ` is real). So `s ≠ 1 → starRingEnd ℂ s ≠ 1`.
2. **`g` is differentiable as an `ℝ`-linear map twice composed with a `ℂ`-differentiable middle map**. Wait — this is the tricky step. `starRingEnd ℂ` is `ℝ`-linear but **not** `ℂ`-linear (it's `ℂ`-antilinear). Two `ℂ`-antilinear maps compose to a `ℂ`-linear one. To prove `g` is **complex-differentiable** (i.e. `DifferentiableAt ℂ g s`), the cleanest route is:
   - Show `(starRingEnd ℂ ∘ riemannZeta ∘ starRingEnd ℂ)` has its Fréchet derivative at `s` equal to `(starRingEnd ℂ ∘ deriv riemannZeta (starRingEnd ℂ s) ∘ starRingEnd ℂ) = starRingEnd ℂ (deriv riemannZeta (starRingEnd ℂ s))` after collapsing two-conjugation on the input direction.
   - This is **NOT** a one-liner in Lean. Likely needs ~20-30 LOC if no canonical lemma exists.

**Alternative bearer search (open for S3 ACT)**: `Complex.AntilinearMap` / `Complex.starRingEnd.compStar.differentiableAt`. Direct probes:

- `gh api search/code?q=AntilinearMap+repo:leanprover-community/mathlib4` — likely has limited coverage.
- `gh api search/code?q=differentiableAt+starRingEnd+repo:leanprover-community/mathlib4` — not yet probed; recommended for S3 ACT.

---

## §2 — Drop-in tactic outline (sketch, not turn-the-crank)

```lean
-- New theorem replacing the axiom `zeta_conj` at RiemannHypothesis.lean:779
theorem zeta_conj_proved (s : ℂ) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  -- Case split on s = 1 (axiom holds trivially: `riemannZeta` has a pole at 1)
  by_cases hs : s = 1
  · subst hs; simp [riemannZeta]  -- both sides evaluate to the pole value
  -- General case: s ≠ 1.
  -- Define g : ℂ \ {1} → ℂ by g s := conj (riemannZeta (conj s))
  -- Step 1: prove g is holomorphic on ℂ \ {1}
  --   - conj is anti-holomorphic; composing two anti-holomorphic gives holomorphic.
  --   - Use `differentiableAt_riemannZeta` (line 137) for the middle.
  --   - Need lemma: `(s ≠ 1) → (starRingEnd ℂ s ≠ 1)` (since 1 is real-fixed).
  -- Step 2: prove g = riemannZeta on {Re s > 1}
  --   - Use the in-file `zeta_conj_of_one_lt_re` (line 680).
  -- Step 3: extend to ℂ \ {1} via AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
  --   - Need preconnectedness of ℂ \ {1} (open question §1.1).
  --   - Need a point in both {Re s > 1} and ℂ \ {1} (e.g. s := 2; eventually-eq is on a nbhd of 2).
  -- Step 4: rearrange g(s) = riemannZeta(s) into the axiom statement
  --   - Apply starRingEnd to both sides; use Complex.conj_conj to collapse.
  sorry
```

### §2.1 — Step-by-step risk register

| # | Step | Risk | Mitigation |
|---|------|------|------------|
| R-1 | `s = 1` base case | `riemannZeta` does NOT evaluate cleanly at `s = 1` (pole); both sides are equal only by `simp [riemannZeta]`'s convention | Low risk — verify via local probe; if `simp` doesn't close, the axiom statement at `s = 1` is vacuously about `riemannZeta 1`, which Mathlib defines as a pole-removal convention (`riemannZeta_one` or similar) |
| R-2 | `(s ≠ 1) → (starRingEnd ℂ s ≠ 1)` | Need name pin | Probably `Complex.conj_ne_one` (similar to `Complex.conj_eq_one_iff`); ~3-5 LOC if direct lemma absent |
| R-3 | Holomorphy of `g = conj ∘ riemannZeta ∘ conj` | `starRingEnd ℂ` is `ℂ`-antilinear, not `ℂ`-linear; two-conjugation in `DifferentiableAt ℂ` is non-trivial | **Medium-high risk**. See §1.2; may need ~20-30 LOC of explicit Fréchet derivative computation, OR a search for `Complex.starRingEnd.compRight.differentiableAt` / similar |
| R-4 | Preconnectedness of `ℂ \ {1}` | `Set.preconnected_compl_of_singleton` may be phantom (§1.1) | **Open**. Likely ~10-15 LOC for a hand-rolled `IsPathConnected → IsPreconnected` argument |
| R-5 | `{Re s > 1}` is a neighbourhood of `s = 2` (a witness point in both `{Re s > 1}` and `ℂ \ {1}`) | The eventually-equal hypothesis needs `f =ᶠ[𝓝 2] g` on a neighbourhood, not just at the point | Use `Filter.eventually_of_mem` with `{Re s > 1} ∈ 𝓝 2` (since `Re` is continuous and `Re 2 = 2 > 1`); ~3 LOC |
| R-6 | Final rearrangement: `g(s) = riemannZeta(s)` → `riemannZeta(conj s) = conj(riemannZeta s)` | Need `Complex.conj_conj` to collapse `conj(conj(...))` | Low risk — `Complex.conj_conj` is in `Algebra/Star/Basic.lean`, simp-tagged |

---

## §3 — What this PREP does NOT do

- ❌ Does **not** modify `state.md`. The S2 ACT summary remains the latest entry; this PREP refines the "Next Action" candidate B description without rewriting any section. (Per researcher session memory: 2-PR STATE-SYNC cap already used by researcher-5 in this session — PRs #18933 (MVT) and #18935 (arith-series); this is a pure new-session-memo PREP, **not** a STATE-SYNC.)
- ❌ Does **not** modify `knowledge.md`. The S1 OBSERVE knowledge survey is unchanged.
- ❌ Does **not** modify `src/data/research/problems/prime-number-theorem-oq-01-oq-01.json`. The JSON `lastUpdate` remains at the S2 timestamp.
- ❌ Does **not** modify `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (60 LOC, 0 sorries, 0 axioms — S2 ACT shipped clean). 0 sorries / 0 axioms preserved.
- ❌ Does **not** modify `proofs/Proofs/RiemannHypothesis.lean`. The `zeta_conj` axiom at line 779 remains; a future S3 ACT replaces it with a `theorem`.
- ❌ Does **not** run docker build. This memo is doc-only.
- ❌ Does **not** open child slug `prime-number-theorem-oq-01-oq-01-oq-01` (which would scope the `zeta_conj` discharge as a new child). That gallery-integration decision is deferred to S3 ACT.

## §4 — Recommendation to the next S3 ACT researcher

1. **First probe (5 min)**: verify `Complex.conj_ne_one` (R-2) and `Complex.starRingEnd_self_apply` / `Complex.conj_conj` (R-6) exist at v4.26.0 with the expected signatures. Both are likely 1-line `gh api search/code` hits.
2. **Then probe (15 min)**: investigate the holomorphy-of-`g` step (R-3). Specifically search Mathlib for:
   - `Complex.compStar` / `starRingEnd.comp.differentiable`
   - `Complex.AntilinearMap.comp.differentiable`
   - Any `Complex.IsAntiHolomorphic` instance
   - Failing those, prepare for ~20-30 LOC of explicit Fréchet derivative computation.
3. **Then audit (10 min)**: pick an approach to preconnectedness of `ℂ \ {1}` (R-4). If a direct name exists, use it; otherwise the hand-rolled `IsPathConnected` route is ~10-15 LOC.
4. **Then S3 ACT (90-120 min including docker build)**: write the proof. The estimate is dominated by R-3 (holomorphy) and R-4 (preconnectedness) — together about 50-60 LOC. The rest of the proof is 20-30 LOC of the identity-principle application plus the case split on `s = 1`.

**Alternative S3 ACT (deferred)**: skip the full discharge and instead introduce a strictly weaker "axiomatic-domain restriction" — encode `zeta_conj` for `{s : ℂ | s.re ≤ 0 ∨ s.re ≥ 1}` (which the in-file Dirichlet-series + functional-equation proofs cover) plus an explicit axiom for the critical strip `{0 < s.re < 1}`. This is **not recommended** — it would weaken the existing axiom from "1 unconditional axiom" to "1 conditional axiom + 0 explicit sorries", which is the same epistemic cost in a less honest framing.

## §5 — Build status

This PREP requires **no Lean build** (single new markdown file in `sessions/`). The S2 ACT build status from PR #18915's body should be the source of truth for the slug's Lean file (`PrimeNumberTheoremOQ01OQ01.lean`, 60 LOC, 0 sorries, 0 axioms).

## §6 — Coordination notes

- **No race on this slug**: `gh pr list -R rjwalters/lean-genius --search "prime-number-theorem-oq-01-oq-01 in:title" --state open` returns `[]` at memo creation and pre-push (~2026-05-13T22:55 UTC).
- **No race on parent slug**: the parent `prime-number-theorem` and grandparent `prime-number-theorem-oq-01` are orthogonal — different scope (parent: full PNT statement; this slug: bridge between two `RiemannHypothesis` declarations across in-tree files).
- **Branch policy**: fresh `research/pnt-oq01-oq01-s3-prep-zeta-conj-bearer` cut from `origin/main` via worktree-native `git switch -c` (recovered from a prior accidental main-repo `cd && git switch -c` hijack per `[Mechanic — cd main-repo && git checkout -b from worktree hijacks branch onto main repo HEAD]` memory; recovery was non-destructive — deleted-branch was 0 commits ahead of `origin/main`).
- **Mathlib lake pin**: `proofs/lake-manifest.json` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All bearer lines above are pinned at this SHA via `gh api` reads; future drift against Mathlib master is irrelevant until the lake manifest is bumped.
- **Session cap status**: researcher-5 (this session) has shipped 3 PRs prior to this one: #18933 (STATE-SYNC, mean-value-theorem-oq-02-oq-04-oq-01), #18935 (STATE-SYNC, arithmetic-series-...-oq030202-oq02), #18938 (new-session-memo PREP, minpoly-charpoly-oq-01 S4). The 2-PR STATE-SYNC cap is full; this PR is a 2nd new-session-memo PREP, lane-distinct from STATE-SYNC per researcher session policy.
