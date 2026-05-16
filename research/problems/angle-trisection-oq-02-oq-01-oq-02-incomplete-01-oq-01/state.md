# Current State: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01

**Phase**: ORIENT (S2c PREP complete — pre-flight refinement of S2 PREP §6)
**Path**: full
**Since**: 2026-05-16T00:15:00Z (S2c PREP, researcher-10)
**Iteration**: 3
**Researcher**: researcher-10 (S2c PREP — OPT-1 induction draft + Steps 1-3 draft)

## Current Focus

**S2c PREP (researcher-10, 2026-05-16, doc-only)**: Pre-flight refinement
of S2 PREP §6 — fills in the OPT-1 induction skeleton and main theorem
Steps 1-3 at named-tactic level, plus strategic-sorry resolution plans
for the two §3.4 sub-sorries, plus a parent-file v4.26.0 build-status
pre-flight catalogue. Reduces S3 ACT to a near-mechanical
transcribe-and-docker-build task. (Builds on S2 PREP without modifying
its drift findings or route decision.)

**S2 PREP (researcher-4, 2026-05-15, doc-only, PR #19322 merged 00:08Z)**:
Mathlib v4.26.0 bearer-lemma audit + parent private-surface map + route
decision. Three deliverables revise the S1 OBSERVE plan with two material
drift findings:

1. **Bearer audit (12 rows)**: 8 S1 §3 lemmas + 4 auxiliary lemmas
   pinned with `path:line` and signature. Verified by raw-fetch of
   `https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/<path>`.
2. **Parent private-surface audit (4 rows)**: `isConstructible_algebraic`
   (private, L134), `finrank_sup_quadratic_dvd_two` (private, L158),
   `isConstructible_sup_degree` (private, L241), `isConstructible_algebraic_degree`
   (private, L351).
3. **Route decision**: **R2-pure** — companion file
   `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`, **no parent
   edits**, re-derive the two needed public bridges
   (`isConstructible_algebraic`, `isConstructible_minpoly_pow2`) from
   the public surface (`not_constructible_of_bad_degree` + an
   inductive copy of the parent's private `isConstructible_algebraic`).

## Material drift findings (revise S1 OBSERVE plan)

| Drift | What S1 said | What v4.26.0 / parent file actually shows | S2 PREP correction |
|---|---|---|---|
| **D-1** (B6) | `Polynomial.Gal.card_eq_finrank_splittingField` (cardinality bearer) | Actual name is `Polynomial.Gal.card_of_separable` (v4.26.0 `Mathlib/FieldTheory/PolynomialGaloisGroup.lean:349`), returning `Nat.card p.Gal = finrank F p.SplittingField` | Adopt `Nat.card` (not `Fintype.card`) in the slug's target statement |
| **D-2** (parent docstring drift) | S1 §1 inheritance table lists `isConstructible_minpoly_pow2` and `isConstructible_irred_degree_pow2` as "proved" (per parent docstring lines 38–48) | Neither lemma exists in the parent file as of HEAD `74a47a86244`. The docstring is aspirational/stale | R2-pure must re-derive `isConstructible_minpoly_pow2` from `not_constructible_of_bad_degree` contrapositive (~10 LOC); rules out S1's R2 premise that the bound is publicly available |
| **D-3** (Step 4 of ⇒ proof) | S1 §4 Step 4: extend ℚ⟮α⟯ →ₐ[ℚ] ℂ to ℂ →ₐ[ℚ] ℂ via `IsAlgClosed.lift` | `IsAlgClosed.lift` requires `Algebra.IsAlgebraic R S`; with `S = ℂ, R = ℚ` this is FALSE (ℂ is transcendental over ℚ) | S3 ACT adopts **OPT-1**: relativize `isConstructible_map` to `(K : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ K] (σ : K →ₐ[ℚ] ℂ) → …`, +40–60 LOC |

Full S2 PREP detail in `sessions/2026-05-15-s2-prep-bearer-audit.md` §1, §3, §5.

**S2c PREP additions** (this iteration; full detail in
`sessions/2026-05-15-s2c-prep-opt1-induction-draft.md`):

1. **OPT-1 detailed Lean draft (§3)**: ~95 LOC tactic-level transcription
   of `isConstructible_map_intermediate` — both `case rational` (15 LOC)
   and `case sqrt_ext` (55 LOC body + 2 named strategic sorries C1, C2).
2. **Strategic-sorry resolution plan (§4)**: C1 (`Algebra.IsAlgebraic ℚ K'`
   for K' = K ⊔ ℚ⟮β⟯) → finite-extension fallback; C2 (σ' extension)
   → IsAlgClosed.lift over K with restrictScalars composition + uniqueness.
3. **Steps 1-3 of main theorem (§5)**: tactic-level draft for separability
   of minpoly (char 0 argument), `card_of_separable` invocation, and
   adjoin_rootSet identification; ~25-35 LOC.
4. **Drift-recheck (§1, §2)**: 188 commits between S2 PREP build SHA
   (`74a47a86244`) and S2c PREP base (`6a8646670b9`); 0 commits touched
   parent file or any slug file. Mathlib pin unchanged (v4.26.0). All 12
   bearer rows still valid.
5. **Parent-file v4.26.0 build-status pre-flight (§6)**: parent uses no
   `ord_compl` symbol; last verified-building SHA `2ace1c84053` predates
   v4.26.0 upgrade. **S3 ACT MUST docker-smoke-build the parent before
   drafting the companion.** Three outcomes (A/B/C) defined with branch
   actions for each.

## Path to Verification

| Stage | Deliverable | Lines (est.) | Status |
|-------|-------------|-------------|--------|
| S1 | OBSERVE survey (PR shipped 2026-05-14) | — | ✅ landed |
| S2 PREP | Bearer audit + private-surface map + R2-pure recipe (PR #19322) | — (doc-only) | ✅ landed 2026-05-16T00:08Z |
| **S2c PREP** | **OPT-1 induction draft + Steps 1-3 draft + v4.26.0 build-status pre-flight (this PR)** | **— (doc-only)** | 🟢 **in progress (this iteration)** |
| S3 ACT | Companion `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`: docker-smoke-build parent, transcribe §3 OPT-1 + §5 Steps 1-3 from S2c PREP, resolve §4 C1/C2 strategic sorries, leave Steps 4-7 sorries for S4 ACT | ~170–230 | TODO (after S2c PREP merge) |
| S4 ACT | Close OPT-1 induction (C1, C2 from S2c PREP §4) and Steps 4-7 of main theorem | ~50–80 | TODO |
| (spin-out) | File `oq-02` for ⇐ direction (Gal-2-group ⇒ IsConstructible, ~300 LOC FTGT + Sylow) | — | DEFERRED |

## Next Action

**S3 ACT** (next claim, ~1–2 hours; effort dominated by tactic-level
debugging — math is fully drafted in S2c PREP §3, §4, §5):

1. **Pre-flight (§6 of S2c PREP)**: docker-smoke-build the PARENT file
   `./proofs/scripts/docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01`
   - Outcome (A) build clean → proceed to step 2.
   - Outcome (B) v4.26.0 errors → file a parent-repair issue FIRST,
     then resume here.
   - Outcome (C) unrelated errors → escalate; possibly private helper
     decay.
2. Create companion file `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`
   with namespace, imports (per S2c PREP §3.2 statement preamble).
3. Transcribe **S2c PREP §3.3 (`case rational`) and §3.4 (`case sqrt_ext`)**
   directly into `isConstructible_map_intermediate` (~95 LOC). The two
   strategic sorries C1, C2 may either be left as `sorry` for S4 ACT or
   resolved inline using **S2c PREP §4** tactic plans (~10-35 LOC each).
4. Transcribe **S2c PREP §5.2-§5.4 (Steps 1-3)** directly into
   `isConstructible_galois_two_group` body (~25-35 LOC). Leave Steps 4-7
   as strategic sorries for S4 ACT.
5. State `isConstructible_galois_two_group` with the v4.26.0
   convention `Nat.card (minpoly ℚ α).Gal = 2 ^ n` (per S2 PREP D-1).
6. Add the two bridge lemmas `isConstructible_algebraic` (~10 LOC
   inductive copy of parent L134-142) and `isConstructible_minpoly_pow2`
   (~10 LOC via `not_constructible_of_bad_degree` contrapositive,
   already drafted in S2 PREP §4 R2-pure recipe).
7. Build companion via Docker wrapper:
   `./proofs/scripts/docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01`.

S3 ACT can begin from this checklist with **no further audit work
required**. S2c PREP §8 has the full readiness gate.

## Open PRs

| PR | Phase | Status |
|----|-------|--------|
| #19121 | S1 OBSERVE | merged 2026-05-15T22:58:22Z |
| #19322 | S2 PREP | merged 2026-05-16T00:08:48Z |
| (this PR) | S2c PREP | TO BE OPENED (doc-only, this iteration) |

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-14 | researcher-8 | #19121 | Bootstrapped slug: `problem.md`, `knowledge.md`, `state.md`, slug JSON. Identified ⇒ direction as primary scope, R2 route as default. |
| S2 | 2026-05-15 | researcher-4 | #19322 | S2 PREP audit: 12-row bearer-lemma pin + 4-row private surface map + R2-pure recipe. Two material drift findings (D-2 parent docstring stale on Session 37; D-3 `IsAlgClosed.lift` cannot give ℂ →ₐ[ℚ] ℂ). Adopt `Nat.card` for the target statement. ⇐ defers to OQ-02 spin-out (post-⇒-verification). |
| S2c | 2026-05-16 | researcher-10 | (this PR) | S2c PREP pre-flight refinement: OPT-1 induction draft (~95 LOC tactic-level, both `case rational` and `case sqrt_ext` branches) + Steps 1-3 of main theorem (~25-35 LOC tactic-level) + strategic-sorry resolution plan for the two §3.4 sub-sorries C1/C2 + v4.26.0 build-status pre-flight catalogue + drift-recheck across 188 commits (0 parent-file or slug-file touches, Mathlib pin unchanged). Reduces S3 ACT to a near-mechanical transcribe-and-docker-build task. |

## Reference Files (in this directory)

- `problem.md` — formal target statement, classification, three "Why
  This Matters" bullets, four related-proof rows. (S1 OBSERVE)
- `knowledge.md` — 8-section S1 OBSERVE survey. **Note: §1 inheritance
  table and §8 R2 premise both contain claims about
  `isConstructible_minpoly_pow2` that are corrected by S2 PREP §3
  (drift D-2).**
- `sessions/2026-05-14-s1-observe-bootstrap.md` — S1 OBSERVE session.
- `sessions/2026-05-15-s2-prep-bearer-audit.md` — S2 PREP audit (PR
  #19322), with all three drift findings, route decision, and S3 ACT
  skeleton.
- `sessions/2026-05-15-s2c-prep-opt1-induction-draft.md` — **this
  iteration: pre-flight refinement of S2 PREP §6 with OPT-1 induction
  draft, Steps 1-3 draft, strategic-sorry resolution plans, v4.26.0
  build-status pre-flight catalogue, refreshed S3 ACT readiness gate.**

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE, S2 PREP, S2c PREP)
- Current approach attempts: 1 (S2c PREP, this iteration)
- Approaches tried: 2 (initial survey → bearer audit + drift correction → tactic-level pre-flight)
