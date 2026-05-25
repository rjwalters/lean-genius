# Research State: ehrhart-cube-proven-oq-03

## Current State

**Phase**: S7 STATE-SYNC — slug COMPLETED (hypersimplex track, Option A); both reference identities proven, build verified, meta verified+original.
**Path**: full
**Since**: 2026-05-25T08:20Z (researcher-1, S7 STATE-SYNC — pool registry catch-up post-build-verify)
**Last Updated**: 2026-05-25T08:20Z (Session 9 STATE-SYNC researcher-1; iteration 7 → 8)
**Iteration**: 8

**Sorries**: 0 (`hypersimplex_palindrome_k_d_minus_1` proven at S4 ACT 2026-05-14 PR #18923; `hypersimplex_count_k_one` proven at S6 ACT 2026-05-16 PR #19639 via Option A from S5b §3).
**Axioms**: 0 (no `axiom` declarations, no structure-encoded assumptions).
**Build**: VERIFIED GREEN. S6 ACT proof body confirmed compiling post Docker recovery; mechanic flipped `meta.status: formalized → verified` and `meta.badge: formalized → original` in PR #19751 (merged 2026-05-16 same day as S6 ACT). Meta lineCount catch-up in PR #20524.
**File**: `proofs/Proofs/EhrhartCubeProvenOQ03.lean` 210 LOC, 6 theorems, 2 definitions.
**Meta**: `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` → `status: verified`, `badge: original`, `sorries: 0`, `axiomCount: 0`.

## S7 STATE-SYNC (researcher-1, 2026-05-25, doc-only)

Pool registry catch-up. The pool entry `ehrhart-cube-proven-oq-03` ("Barvinok's algorithm for lattice point counting in fixed dimension") was still status `available` despite the on-main slug having shipped axiom-free at S6 ACT and the gallery meta being `verified/original` since PR #19751. The seeker was re-selecting a slot whose deliverable is already merged.

**What S7 does:** flip pool `status: available → completed` and JSON `phase: S6_ACT → COMPLETED`, `status: in-progress → completed`. Clears the four legacy blockers (Docker hung at S6 author time; bearer audit Mathlib Ehrhart absence; slot drift from Barvinok plan to hypersimplex scaffold; status-flip deferral) — all now superseded by post-S6 reality.

**What S7 does NOT do:** no `.lean` edit, no `meta.json` edit, no new sibling slug creation, no scope-decision flip. The Barvinok-track Option B (spin off as `oq-05`/`-06`) remains an *independent* scope decision for seeker/curator/human triage — it is not a blocker on **this** slug, which delivered the hypersimplex track in full.

**Pool entry name vs slug reality (audit note).** The pool's `name` field still reads "Barvinok's algorithm…", which is a stale seeker artefact from the original S1 plan that S2 PREP (researcher-10, 2026-05-13) found to be incompatible with the on-main hypersimplex slot. Renaming the pool entry to match `meta.json` ("Ehrhart Polynomial of the Hypersimplex: First-Principles Scaffold") is a separate seeker/curator territory edit — left out of this PR to keep S7 scope narrow (registry-state-sync only, no metadata renames). Future seekers picking from this pool will see the slug as `completed` regardless of `name`.

### S7 STATE-SYNC files modified (this PR)

* `research/problems/ehrhart-cube-proven-oq-03/state.md` — this section + header refresh (phase, since, last updated, iteration, sorries, build, meta).
* `src/data/research/problems/ehrhart-cube-proven-oq-03.json` — `currentState.{phase: COMPLETED, since, iteration: 8, focus, nextAction, attemptCounts.total: 8}`, `status: in-progress → completed`, `currentState.blockers: []`, `lastUpdate`.
* `.lean/state/candidate-pool.json` — via `claim-problem.sh update ehrhart-cube-proven-oq-03 completed` (auto: pool entry `status: available → completed`).

## S6 ACT (researcher-8, 2026-05-16, this PR)

Transcribed Option A from S5b PREP §3 (researcher-12, PR #19236) into `proofs/Proofs/EhrhartCubeProvenOQ03.lean` lines 75–77, replacing the `sorry` body of `hypersimplex_count_k_one` with a ~32-LOC proof. Approach: lift the subtype-coded weak compositions over `Fin (n+1)` to subtype-coded weak compositions over `ℕ` via an `Equiv` (the upper-bound `< n + 1` is non-binding when ∑ = n, by `Finset.single_le_sum`), compose with `Sym.equivNatSumOfFintype` and `Sym.card_sym_eq_choose` (stars-and-bars), then close via `Nat.choose_symm_of_eq_add (by omega)`. The `Fintype.card_of_subtype` rewrite bridges the filter cardinality and the Subtype cardinality.

**S5b §4 caveats pre-handled.** The S5b PREP §4 hazard log heightened risk on caveat #4 (`right_inv` `rfl` vs `ext i; rfl`). This PR pre-stages the safe substitute (`right_inv := by intro ⟨P, hP⟩; ext i; rfl`) mirroring the `left_inv` pattern; Bugs A and B from S5b §2 are applied verbatim (`Fintype.card_of_subtype` over `card_subtype`, no outer `.symm`). The `H` argument to `Fintype.card_of_subtype` uses explicit `simp [Finset.mem_filter, Finset.mem_univ]` (Option B-style robustness) over Option A's bare `simp`, costing 0 net LOC.

**Bearer pin re-verification.** All 4 critical bearers re-fetched via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c2…` at S6 author time:

| Bearer | Path | Line | Verdict at pin |
|---|---|---|---|
| `Sym.equivNatSumOfFintype` | `Mathlib/Data/Finsupp/Multiset.lean` | 260 | ✅ noncomputable def, signature `Sym α n ≃ {P : α → ℕ // ∑ i, P i = n}` |
| `Sym.card_sym_eq_choose` | `Mathlib/Data/Sym/Card.lean` | 113 | ✅ `card (Sym α k) = (card α + k - 1).choose k` |
| `Fintype.card_of_subtype` | `Mathlib/Data/Fintype/Card.lean` | 47 | ✅ `card { x // p x } = #s` (the corrected S5b §2 Bug A target) |
| `Nat.choose_symm_of_eq_add` | `Mathlib/Data/Nat/Choose/Basic.lean` | 199 | ✅ `n = a + b → choose n a = choose n b` |

No drift since S5b PREP recorded.

**Status quo flip deferred.** Per CLAUDE.md axiom-integrity policy, do NOT flip `meta.status: formalized` → `verified` until Docker build confirms compilation. This S6 ACT PR keeps status `formalized` with sorries 0; auditor/mechanic flips to `verified` once build is green.

**Out of scope (this PR).** No `meta.status` / `meta.badge` flip (build pending). No knowledge.md edit (the existing §S3 PREP bearer table + §S5/S5b refinements describe the shipped proof; appending a §S6 ACT walkthrough is the session memo's job, not knowledge.md's). No re-title of JSON `title` from Barvinok to hypersimplex (still in Option A vs B scope-decision territory). No Barvinok-track `oq-05` spinoff.

## S6 picker (post-S5b, this STATE-SYNC bump)

S5 PREP (#19179, merged 2026-05-15T22:56Z): drafted ~25-LOC §3 proof skeleton for `hypersimplex_count_k_one` using `Sym.equivNatSumOfFintype` from `Mathlib/Data/Finsupp/Multiset.lean`, with 6 caveats.

S5b PREP (#19236, merged 2026-05-15T18:04Z): pre-flight pin-verification found **2 elaboration bugs** in S5 §3 skeleton; corrections filed (see `sessions/2026-05-15-s5b-preflight-bearer-corrections.md`, 483 LOC).

**Next picker**: S6 ACT — transcribe corrected S5+S5b skeleton into `proofs/Proofs/EhrhartCubeProvenOQ03.lean` (replace line-75 `sorry`), build-verify via `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ03`. Pre-requisite: host disk capacity ≥ 10 Gi avail + Docker daemon responsive (current 2026-05-16T09:24Z: 100% / 6.9 Gi avail / `docker info` hung past 8 s — BLOCKED on infrastructure, not bearer or logic).

## S5b PREP (researcher-12, 2026-05-15, doc-only, PR #19236)

Pre-flight pin-verification of #19179 §3 skeleton against lake pin `2df2f0150c…` surfaced 2 elaboration bugs; corrections filed. Skeleton now bearer-CLEAN with corrected references.

## S5 PREP (researcher-3, 2026-05-15, doc-only, PR #19179)

Identified `Sym.equivNatSumOfFintype` at `Mathlib/Data/Finsupp/Multiset.lean` as minimum-LOC bearer for `hypersimplex_count_k_one`. Drafted ~25-LOC §3 proof skeleton with 6 caveats.

## S4 ACT (researcher-3, 2026-05-14, PR #18923 → merged; Lean + build-verify)

Discharged `hypersimplex_palindrome_k_d_minus_1` via involution `φ x i = ⟨n − x i, _⟩`, sum-of-complements identity, then `Finset.card_equiv`. Build clean on first Docker iter (7743 jobs). File 119 → 169 LOC; sorries 2 → 1.

## Session 2 — S2 PREP: Mathlib bearer audit + slot-drift discovery (researcher-10, 2026-05-13)

**Mode.** ANALYSIS-ONLY (no `.lean` edits; pure doc / JSON sync).

**Outcome.** The S1 OBSERVE plan (Session 1, 2026-05-12) is built on
**verifiably false premises** about Mathlib's Ehrhart-theory content,
and the slug's on-disk state has **drifted** from the JSON metadata.
Both must be corrected before any S2 ACT (Lean) iteration.

### Finding 1 — Mathlib has no Ehrhart theory

The S1 OBSERVE state.md claims:

> Mathlib v4.26.0 has Ehrhart theory in
> `Mathlib.Combinatorics.Polytope.Ehrhart` and rational-function /
> power-series infrastructure (`RatFunc`, `MvPowerSeries`, `MvPolynomial.aeval`).

This is **false** at the lake-pinned Mathlib SHA `2df2f0150c27`
(`proofs/lake-manifest.json`). Bearer audit via the GitHub Search API
returns:

| Query | Count |
|---|---|
| `Ehrhart` (any file, any path) | **0** |
| `Polytope` (any file, any path) | **0** |
| `LatticePolytope` (anywhere) | **0** |
| `hStar` / `h_star` / `Eulerian` (filename:Eulerian) | **0** |
| `Mathlib.Combinatorics.Polytope.Ehrhart` (direct fetch) | 404 |

Only the algebra dependencies are real:

| Module | Status | Size |
|---|---|---|
| `Mathlib.FieldTheory.RatFunc.Basic` | ✓ exists | 45 125 B |
| `Mathlib.Algebra.MvPolynomial.Basic` | ✓ exists | 41 370 B |
| `Mathlib.RingTheory.MvPowerSeries.Basic` | ✓ exists (path differs from S1 plan, which said `Mathlib.RingTheory.PowerSeries.Basic`) | n/a |

The S1 OBSERVE plan's "S2.1 Docker probe" would have flagged the
missing `Mathlib.Combinatorics.Polytope.Ehrhart` import on first
invocation. The bearer audit catches it without Docker (relevant given
the project-wide `proofs/.lake` self-referential-symlink trap in this
worktree).

**Implication.** Any retargeted S2 ACT toward Barvinok / generating
functions must build the Ehrhart support from scratch over Mathlib's
algebraic substrate (`RatFunc` / `MvPowerSeries` / `MvPolynomial`) —
there is no pre-existing Ehrhart toolkit to specialise.

### Finding 2 — Slug slot is already taken

`proofs/Proofs/EhrhartCubeProvenOQ03.lean` is **already on main**:

* Path `proofs/Proofs/EhrhartCubeProvenOQ03.lean` — 119 LOC, 6
  theorems, 2 definitions, 2 sorries, 0 axioms.
* Subject: **Hypersimplex** Δ(d, k) lattice-point counting (the slice
  of [0, 1]^d by the affine hyperplane Σ x_i = k), NOT Barvinok.
* `namespace EhrhartCubeProvenOQ03`.
* First committed in PR #18293 (`research(ehrhart-cube-proven-oq-03):
  S1 OBSERVE — hypersimplex Δ(d,k) Lean scaffold (build pending)`).
* `src/data/proofs/ehrhart-cube-proven-oq-03/` gallery directory
  exists with `meta.json` (title "Ehrhart Polynomial of the
  Hypersimplex: First-Principles Scaffold", `status: formalized`,
  `sorries: 2`, `badge: formalized`) + `annotations.json` + `index.ts`.

### Finding 3 — JSON `leanFiles` is empty despite on-main file

`src/data/research/problems/ehrhart-cube-proven-oq-03.json` reports
`leanFiles: []`. Reality: the hypersimplex file exists with 119 LOC.

### Finding 4 — Title / scope drift

| Field | JSON value | meta.json value (on-main) |
|---|---|---|
| `title` | "Barvinok's algorithm for lattice point counting in fixed dimension" | "Ehrhart Polynomial of the Hypersimplex: First-Principles Scaffold" |
| `tags` includes | `barvinok`, `algorithms` | `hypersimplex`, `open-problem` |

The Session 1 (2026-05-12) iteration **retargeted the slug from
hypersimplex to Barvinok without touching the on-main scaffold** or
the gallery entry. The slot now holds two incompatible plans.

## Recommended Continuation Paths

Two clean options, surfaced for seeker / curator / human triage —
this PR does **not** decide between them:

### Option A — Continue the hypersimplex track (low-risk)

Treat the slug as `ehrhart-cube-proven-oq-03` ⇔ hypersimplex Δ(d, k)
(matches on-main scaffold + gallery + meta.json). S3 next:

1. Discharge `hypersimplex_count_k_one`: Δ(d, 1) lattice count
   = C(n + d − 1, d − 1) via the multiset-stars-and-bars bijection.
2. Discharge `hypersimplex_palindrome_k_d_minus_1`: Δ(d, k) count
   = Δ(d, d − k) count via the involution x ↦ n − x.

Both proofs are tractable in Mathlib v4.26.0 (use `Fintype.card`,
`Finset.bij`, `Finset.sum`); ~70 LOC each. Pure combinatorics, no
algebraic-geometry preliminaries.

### Option B — Retarget to a new sibling slug `oq-05` (Barvinok)

Spin off the Barvinok-1994 plan as **`ehrhart-cube-proven-oq-05`**
(or `-oq-06`; current siblings end at -04). That slug starts with the
correct Mathlib substrate awareness from this audit and does not
collide with the hypersimplex slot. The Session 1 S1 OBSERVE
documentation (problem.md + knowledge.md + Barvinok plan) becomes the
new slug's bootstrap; `ehrhart-cube-proven-oq-03` reverts to its
on-main hypersimplex identity.

## Decision: deferred

This PR ships **bearer-audit findings + JSON drift fixes only**.
Scope decision (Option A vs B) deferred to seeker / curator / human
triage.

## Files modified (this PR)

* `research/problems/ehrhart-cube-proven-oq-03/state.md` — this file.
* `research/problems/ehrhart-cube-proven-oq-03/knowledge.md` — append
  bearer-audit section.
* `src/data/research/problems/ehrhart-cube-proven-oq-03.json` — phase
  S1_OBSERVE → S2_PREP, iteration 1 → 2, `lastUpdate`, `knownResults`
  (remove false Mathlib claim), `currentState.{focus,nextAction}`,
  `knowledge.{progressSummary,insights,mathlibGaps,nextSteps}`,
  `references.mathlib` (correct paths), `references.urls` (remove dead
  Mathlib doc URL), `leanFiles` (add on-main hypersimplex entry).

## Out of scope (this PR)

* No `.lean` edits. The on-main hypersimplex scaffold is untouched.
* No retitle of the JSON `title` field — that is the scope-decision
  question deferred to Option A / B triage.
* No gallery `meta.json` edits — those describe the on-main scaffold
  accurately and would be modified by Option B only.
* No new sibling slug creation — seeker / curator can spin off
  `oq-05` if Option B is chosen.

## Decision Log

* **2026-05-13 S2 (researcher-10)**: Decision to ship S2 as a
  doc-only PREP rather than S2 ACT. Reason: the S1 ACT plan
  ("S2.1 probe + S2.2 implement Barvinok scaffold") is built on the
  false `Mathlib.Combinatorics.Polytope.Ehrhart` premise AND would
  collide with the already-committed hypersimplex scaffold; both
  must be triaged first.
* **2026-05-13 S2 (researcher-10)**: Decision NOT to decide between
  Option A (continue hypersimplex) and Option B (spin off `oq-05`).
  Reason: scope decisions of this magnitude (rewriting the slug
  subject) should be made by the seeker / curator / human, not by a
  research iteration.
* **2026-05-13 S3 (researcher-4)**: Same deferral. The S3 PREP
  iteration adds the hypersimplex-track bearer audit (complementary
  to S2's Barvinok-track audit) but stops short of any `.lean` edit.

## Session 3 — S3 PREP: hypersimplex-track Mathlib bearer audit + refined proof sketches (researcher-4, 2026-05-13)

**Mode.** ANALYSIS-ONLY (no `.lean` edits, no `meta.json` edits, no
new sibling slug; pure doc / JSON sync). Complementary to Session 2:
S2 PREP audited the **Barvinok-track** bearer (and ruled it
insufficient). This S3 PREP audits the **hypersimplex-track**
bearer — the lemmas the on-main scaffold's two sorries actually
need — which S2 left at strategy level only ("tractable in Mathlib
v4.26.0", §Recommended Continuation Paths line 106).

**Decision not taken.** This iteration does **not** decide between
Option A (continue hypersimplex) and Option B (spin off Barvinok as
oq-05); that triage remains with seeker / curator / human per S2's
Decision Log (§Decision Log line 156–160 above). The audit value is
**option-symmetric**: if Option A is later chosen, S4 ACT becomes
turn-the-crank for the palindrome sorry; if Option B is later chosen,
the audit data is parked in `knowledge.md` for when hypersimplex
work resumes under whatever new slug owns it.

### Rationale

The on-main `EhrhartCubeProvenOQ03.lean` docstring (lines 70–88 and
83–88) sketches both sorries at the *strategy* level —
`Sym.card_sym_eq_choose` for `hypersimplex_count_k_one`, involution
`x ↦ n − x` for `hypersimplex_palindrome_k_d_minus_1` — but does
not cite Mathlib at the *lemma* level. The adjacent-slug
anti-pattern of "S2 ACT discovers cited lemma is absent" (cf. S1
OQ-03's wrong claim about `Mathlib.Combinatorics.Polytope.Ehrhart`
which S2 corrected) is preventable here at zero cost.

### Bearer audit (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

All entries verified via the GitHub Contents API at the lake-pinned
SHA (`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c27...`).

| Sorry / role | Sketch-cited lemma | Path | Line | Signature |
|---|---|---|---|---|
| `hypersimplex_count_k_one` (primary) | `Sym.card_sym_eq_choose` | `Mathlib/Data/Sym/Card.lean` | 113 | `card (Sym α k) = (card α + k − 1).choose k` (∀ `α : Type*`, `[Fintype α]`, `[Fintype (Sym α k)]`) |
| `hypersimplex_count_k_one` (helper) | `Sym.card_sym_fin_eq_multichoose` | `Mathlib/Data/Sym/Card.lean` | 94 | `∀ n k, card (Sym (Fin n) k) = multichoose n k` |
| `hypersimplex_palindrome_k_d_minus_1` (primary, upgrade) | `Finset.card_nbij'` | `Mathlib/Data/Finset/Card.lean` | 366 | `(i : α → β) (j : β → α) (hi : Set.MapsTo i s t) (hj : Set.MapsTo j t s) (left_inv …) (right_inv …) ⇒ #s = #t` |
| `hypersimplex_palindrome_k_d_minus_1` (alt, docstring sketch) | `Finset.card_image_of_injective` | `Mathlib/Data/Finset/Card.lean` | 242 | `[DecidableEq β] (s : Finset α) (Injective f) ⇒ #(s.image f) = #s` |
| Aux (both sorries) | `Finset.sum_add_distrib` | `Mathlib/Algebra/BigOperators/*` | n/a | `∑ a ∈ s, (f a + g a) = ∑ a ∈ s, f a + ∑ a ∈ s, g a` (81 in-repo hits at pinned SHA; widely-used canonical lemma) |
| Aux (palindrome) | `Nat.sub_add_cancel` | `Mathlib/Data/Nat/Defs.lean` (or `Mathlib/Order/Sub`) | n/a | `n ≤ m ⇒ m − n + n = m` |
| Aux (k = 1, final coeff swap) | `Nat.choose_symm` | `Mathlib/Data/Nat/Choose/Basic.lean` | n/a | `k ≤ n ⇒ n.choose k = n.choose (n − k)` |

**Verdict.** All sketch-cited primary lemmas are present at the
lake-pinned SHA. The hypersimplex track is **bearer-clean** in
Mathlib v4.26.0 — opposite of the Barvinok track which S2 found
bearer-absent.

### Refined proof outline — `hypersimplex_palindrome_k_d_minus_1` (~30–50 LOC, lowest-risk start)

**Primary lemma.** `Finset.card_nbij'` (`Mathlib/Data/Finset/Card.lean:366`).

**Construction.** Define the self-map of `Fin d → Fin (n + 1)`:

```lean
let φ : (Fin d → Fin (n + 1)) → (Fin d → Fin (n + 1)) :=
  fun x i => ⟨n - (x i : ℕ), by have := (x i).isLt; omega⟩
```

The bound `n − (x i : ℕ) < n + 1` follows from `(x i).isLt :
(x i : ℕ) < n + 1` by `omega`.

**Sum-of-complements identity** (the key fact for both `Set.MapsTo`
directions):

```
∀ x, (∑ i, (φ x i : ℕ)) + (∑ i, (x i : ℕ)) = d * n
```

Proof skeleton:
1. `Finset.sum_add_distrib` ⇒ `∑ ((n − x_i) + x_i) = ∑ (n − x_i) + ∑ x_i`.
2. Pointwise `(n − x_i) + x_i = n` from `Nat.sub_add_cancel (Nat.lt_succ_iff.mp (x i).isLt)`.
3. `∑ n = #(Finset.univ : Finset (Fin d)) • n = d * n` via `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `smul_eq_mul`.

**`Finset.card_nbij' φ φ` field proofs.**

* `MapsTo` LHS → RHS (i.e. `∀ x ∈ filter (∑ = n·(d − 1)), φ x ∈ filter (∑ = n·1)`): combine the sum-of-complements identity with `hx : ∑ x_i = n·(d − 1)` to get `∑ φ x_i + n·(d − 1) = d·n`; then `omega` (after splitting `d·n = n + n·(d − 1)` via the helper `Nat.mul_sub_one : n * (d − 1) = n * d − n` for `d ≥ 1`).
* `MapsTo` RHS → LHS: symmetric.
* `LeftInvOn` (`φ ∘ φ = id` on LHS): `φ (φ x) i = ⟨n − (n − (x i : ℕ)), _⟩`; `(x i : ℕ) ≤ n` gives `n − (n − x_i) = x_i` by `omega`; `Fin.ext` closes.
* `RightInvOn`: same proof body.

**Estimated body.** ≤ 60 LOC (including `set` for φ, the sum-of-
complements helper, and the four `card_nbij'` field proofs).

**Known hazards.**
1. The `d·n = n + n·(d − 1)` step. `omega` may stall on `n * (d − 1)` (non-linear). Backup: explicit `Nat.mul_sub_one` (bearer-confirmed in Mathlib's `Nat.Defs` / `Nat.Basic` family — verify on first build).
2. Membership unfolding. `Finset.mem_filter` + `Finset.mem_univ` need to unfold to `(_ ∧ Σ = …)`; the standard `simp only` invocation is `simp only [Finset.mem_filter, Finset.mem_univ, true_and]`.

### Refined proof outline — `hypersimplex_count_k_one` (~70–100 LOC, requires Sym bijection)

**Primary lemma.** `Sym.card_sym_eq_choose` (`Mathlib/Data/Sym/Card.lean:113`).

**Caveat — the docstring sketch under-estimates the work.**
`Sym.card_sym_eq_choose` yields `#(Sym (Fin d) n) = (d + n − 1).choose n`. Reaching the goal `(n + d − 1).choose (d − 1)` requires three independent steps:

1. **Bijection** `{x : Fin d → Fin (n + 1) | ∑ x_i = n} ≃ Sym (Fin d) n` — the "x_i = multiplicity of i" map. **This is NOT a one-liner in Mathlib**; it must be constructed (likely via `Finset.card_nbij'` between the filter and the `Sym` finset, modulo the `Multiset.count`-style API). Estimated ~50 LOC.
2. **Index commutation** `(d + n − 1) = (n + d − 1)` — trivial.
3. **Coefficient symmetry** `(n + d − 1).choose n = (n + d − 1).choose (d − 1)` from `Nat.choose_symm` plus `1 ≤ d` (from `hd : 1 ≤ d`). Estimated ~5 LOC.

**Fintype instance.** `Sym.fintype (α := Fin d) (n := n)` should be in scope when `Fintype α` is; verify on first build (likely automatic).

**Alternative: stars-and-bars directly** (without going through `Sym`). Construct an injection `{x : ∑ = n} → {S : Finset (Fin (n + d − 1)) | #S = d − 1}` via the prefix-sum map `x ↦ {x_0 + ··· + x_{i−1} + i : i ∈ Fin (d − 1)}`. RHS cardinality is `(n + d − 1).choose (d − 1)` directly via `Finset.card_powersetCard`. Total estimated ~80 LOC, but each step is more elementary.

**Recommendation.** Defer this sorry to S5 (or later). It is materially harder than the palindrome sorry and benefits from S4 ACT shaking out the Lean-4 idioms first.

### S4 ACT plan (Option A path; not committed by this PR)

* **S4 ACT** (preferred next, conditional on Option A): edit `proofs/Proofs/EhrhartCubeProvenOQ03.lean` lines 89–91 only; replace the `sorry` body with the involution proof above. Estimated +50/−1 LOC. Single Docker build (`./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ03`).
* **S5 ACT** (deferred, conditional on S4 ACT success): the `k = 1` case via Sym bijection or stars-and-bars (still TBD; ~80 LOC).

### Files modified (this PR)

* `research/problems/ehrhart-cube-proven-oq-03/state.md` — this Session 3 section.
* `research/problems/ehrhart-cube-proven-oq-03/knowledge.md` — append §S3 PREP hypersimplex-track audit.
* `src/data/research/problems/ehrhart-cube-proven-oq-03.json` — phase `S2_PREP` → `S3_PREP`, iteration `2` → `3`, `lastUpdate`, `currentState.{focus,since,nextAction,attemptCounts}`, `knowledge.{progressSummary,insights,nextSteps,builtItems}`.

### Out of scope (this PR)

* No `.lean` edits. Both sorries remain.
* No `meta.json` edits (gallery describes on-main hypersimplex; that description remains accurate).
* No JSON `title` / `tags` retitle (still in Option A vs B scope-decision territory).
* No new sibling slug creation.
* No commitment to Option A vs B — that decision remains with seeker / curator / human per Session 2 Decision Log.

## Session 4 — S4 ACT: discharge `hypersimplex_palindrome_k_d_minus_1` (researcher-3, 2026-05-14)

**Mode.** ACT. Single `.lean` edit at `proofs/Proofs/EhrhartCubeProvenOQ03.lean:79–91` (replaces the docstring sketch and the `sorry` body with a complete proof). +50 LOC, file 119 → 169. Build clean on first Docker iteration: `Build completed successfully (7743 jobs)`. Sorries 2 → 1.

**Outcome.** The palindrome sorry is now PROVEN. The hypersimplex track has its first axiom-free reference identity, on the Option-A continuation (no scope-decision flip; the on-main hypersimplex slot remains the slug's subject).

### Path chosen: Option A (continue hypersimplex)

S3 PREP (researcher-4, PR #18923) deferred Option A vs B to seeker/curator/human triage. This session takes Option A on the narrowest justification: a single bearer-clean sorry (`hypersimplex_palindrome_k_d_minus_1`) is now provable in ≤ 60 LOC, the proof has zero scope-decision content (it only touches the existing hypersimplex namespace's reference identity), and shipping it does NOT preclude Option B for the larger Barvinok plan (which would still spin off to `oq-05` if chosen). The k=1 sorry (`hypersimplex_count_k_one`) remains for a future S5+ ACT and would also remain unaffected by an Option B fork.

### Proof construction

The S3 PREP outline (state.md §Refined proof outline — `hypersimplex_palindrome_k_d_minus_1`) used `Finset.card_nbij' φ φ` (4 field obligations: 2 × `Set.MapsTo`, 2 × `Set.LeftInvOn`/`RightInvOn`). On inspection of `Mathlib/Data/Finset/Card.lean` at the lake-pinned SHA, the specialization `Finset.card_equiv` (line 403) is cleaner when the bijection is a self-inverse involution:

```
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : #s = #t
```

This has 1 obligation (the iff) versus 4. The shipped proof bundles φ as an `Equiv` via `{ toFun := φ, invFun := φ, left_inv := hφφ, right_inv := hφφ }` where `hφφ : ∀ x, φ (φ x) = x`, then applies `card_equiv` with the iff closed by `omega` after the linear-arithmetic bridge `d * n = n * 1 + n * (d - 1)`.

**Proof skeleton (in shipped order):**

1. `hbnd : ∀ x i, (x i : ℕ) ≤ n` — from `(x i).isLt : (x i : ℕ) < n + 1` by omega. Used twice.
2. `let φ : ... := fun x i => ⟨n - (x i : ℕ), by ...; omega⟩` — the involution.
3. `hφφ : ∀ x, φ (φ x) = x` — pointwise `Fin.ext`; `n - (n - x_i) = x_i` by `omega` given `hbnd`.
4. `hsum : ∀ x, (∑ i, (φ x i : ℕ)) + (∑ i, (x i : ℕ)) = d * n` — `Finset.sum_add_distrib` + pointwise `(n - x_i) + x_i = n` + `simp only` chain through `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `smul_eq_mul`.
5. `let e : ... ≃ ... := { toFun := φ, invFun := φ, left_inv := hφφ, right_inv := hφφ }` — bundle as Equiv.
6. `unfold hypersimplexLatticeCount; refine Finset.card_equiv e ?_` — reduce to the iff.
7. Linear bridge `h_d1 : d * n = n * 1 + n * (d - 1)` via `Nat.add_mul` + `ring` from `d = 1 + (d - 1)` (which `omega` produces from `hd : 2 ≤ d`).
8. `omega` × 2 — closes both ↔ directions from `hsum x` + `h_d1` + the assumed sum-equality.

**Deviations from S3 PREP plan.**

- Used `Finset.card_equiv` (1 obligation) over `Finset.card_nbij'` (4 obligations). Both work; `card_equiv` is the right tool when the bijection is a self-inverse involution because the LeftInvOn/RightInvOn discharge collapses into one `hφφ` proof reused twice in the Equiv constructor.
- The S3 PREP "known hazard" (`omega` stall on `n * (d − 1)`) did NOT fire. Reason: the bridge `d * n = n * 1 + n * (d - 1)` is proven once as a hypothesis (`h_d1`) using `Nat.add_mul` + `ring`, then `omega` treats the `n * (d - 1)` term as an opaque atom — purely linear given `h_d1` + `hsum`. The S3 PREP's `Nat.mul_sub_one` backup was unnecessary.
- S3 PREP did NOT mention `set_option linter.unusedTactic false`; the file already had it at line 33 so no new linter overrides were needed.

### Files modified (this PR)

* `proofs/Proofs/EhrhartCubeProvenOQ03.lean` — replace `sorry` body at line 89-91 with the ~50-LOC proof; rewrite the surrounding docstring (line 79-90) to reflect the proven status; file 119 → 169 LOC.
* `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` — `leanFile.{lineCount,sorries}` (119 → 169, 2 → 1) and `meta.sorries` (2 → 1).
* `src/data/research/problems/ehrhart-cube-proven-oq-03.json` — phase `S3_PREP` → `S4_ACT`, iteration `3` → `4`, `lastUpdate`, `currentState.{since,iteration,focus,nextAction,attemptCounts.{total,currentApproach}}`, `leanFiles[0].{lineCount,sorryCount}`.
* `research/problems/ehrhart-cube-proven-oq-03/state.md` — this Session 4 section + header refresh.

### Out of scope (this PR)

* No `hypersimplex_count_k_one` discharge (the k=1 sorry remains, queued for S5+ ACT per the S3 PREP caveat).
* No new sibling slug creation; no rename of this slug's `title` / `tags` / `description` (the Option A vs B scope-decision territory in §Recommended Continuation Paths is left intact — Option B can still be chosen by a future iteration without rewinding this proof).
* No `meta.json` `status` change (`"formalized"` remains correct while sorries > 0).
* No `knowledge.md` edit (the S3 PREP bearer table and the §S3 PREP refined proof outline already match the shipped proof; appending an "S4 ACT — proof shipped" note would be redundant with this state.md section).
* No `S5 ACT` start on the k=1 sorry. That is materially harder (~80 LOC, needs a multiplicity bijection or stars-and-bars construction); per session-discipline norms it deserves a separate ACT iteration with its own pre-flight Mathlib bearer check on `Sym.card_sym_eq_choose` argument shape + `Finset.card_powersetCard`.

### Build

```
./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ03
...
⚠ [7743/7743] Built Proofs.EhrhartCubeProvenOQ03 (9.3s)
warning: Proofs/EhrhartCubeProvenOQ03.lean:75:8: declaration uses 'sorry'
Build completed successfully (7743 jobs).

=== Build succeeded ===
```

The single remaining `'sorry'` warning is at line 75 = `hypersimplex_count_k_one`, as expected.

### Decision Log

* **2026-05-14 S4 (researcher-3)**: Take Option A on the narrowest justification (one bearer-clean sorry, ≤ 60 LOC, no scope-decision content, leaves Option B available for the larger Barvinok plan). Reason: shipping a small axiom-free reference identity strictly improves the slug's state and does not foreclose any of S2 PREP's two recommended continuation paths.
* **2026-05-14 S4 (researcher-3)**: Use `Finset.card_equiv` over the S3-sketched `Finset.card_nbij'`. Reason: the involution form `φ ∘ φ = id` bundles directly as an `Equiv`, collapsing 4 field obligations to 1 iff goal; the proof is materially shorter and easier to read. Recorded for future hypersimplex-style proofs.
* **2026-05-14 S4 (researcher-3)**: Do NOT bundle the k=1 ACT into this PR. Reason: it is materially harder, needs a non-trivial Sym-or-stars-and-bars bijection (~80 LOC per S3 PREP caveat), and would dilute the review surface of a tight ~60-LOC palindrome ACT. Session-discipline norm: ship the small win, queue the bigger ACT.
