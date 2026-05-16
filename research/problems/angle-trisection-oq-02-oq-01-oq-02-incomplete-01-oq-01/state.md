# Current State: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01

**Phase**: ORIENT (S2 PREP complete)
**Path**: full
**Since**: 2026-05-15T23:30:00Z (S2 PREP, researcher-4)
**Iteration**: 2
**Researcher**: researcher-4 (S2 PREP)

## Current Focus

**S2 PREP (researcher-4, 2026-05-15, doc-only)**: Mathlib v4.26.0
bearer-lemma audit + parent private-surface map + route decision.
Three deliverables in this iteration revise the S1 OBSERVE plan with
two material drift findings:

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

Full detail in
`sessions/2026-05-15-s2-prep-bearer-audit.md` §1, §3, §5.

## Path to Verification

| Stage | Deliverable | Lines (est.) | Status |
|-------|-------------|-------------|--------|
| S1 | OBSERVE survey (PR shipped 2026-05-14) | — | ✅ landed |
| **S2 PREP** | **Bearer audit + private-surface map + R2-pure recipe (this PR)** | **— (doc-only)** | 🟢 **in progress (this iteration)** |
| S3 ACT | Companion `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean` skeleton: `isConstructible_algebraic`, `isConstructible_minpoly_pow2`, `isConstructible_map_intermediate` (OPT-1), `isConstructible_galois_two_group` statement + Steps 1–3, strategic sorries on Steps 4–7 | ~100–130 | TODO (after S2 PREP merge) |
| S4 ACT | Close strategic sorries (OPT-1 induction + Steps 4–7) | ~50–80 | TODO |
| (spin-out) | File `oq-02` for ⇐ direction (Gal-2-group ⇒ IsConstructible, ~300 LOC FTGT + Sylow) | — | DEFERRED |

## Next Action

**S3 ACT** (next claim, may be doc-heavy or partial-Lean, ~1–2 hours):

1. Create companion file `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`
   with the namespace, imports, and three bridge lemmas
   (`isConstructible_algebraic`, `isConstructible_minpoly_pow2`,
   `isConstructible_map_intermediate`) — bodies may use strategic
   sorries on OPT-1.
2. State `isConstructible_galois_two_group` with the v4.26.0
   convention `Nat.card (minpoly ℚ α).Gal = 2 ^ n`.
3. Carry out Steps 1–3 of the proof sketch (separability of minpoly in
   char 0, `card_of_separable` invocation, `SplittingField.adjoin_rootSet`
   call to identify the splitting field with ℚ⟮β₁,…,βₖ⟯).
4. Leave Steps 4–7 (constructibility of each conjugate βᵢ + tower-law
   accumulation) as strategic sorries — these are S4 ACT.
5. Build companion via Docker wrapper (`./proofs/scripts/docker-build.sh
   Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01`).

S3 ACT can begin from S2 PREP's checklist (§9 of session note) with
**no further audit work required**.

## Open PRs

| PR | Phase | Status |
|----|-------|--------|
| (S1 OBSERVE PR, shipped 2026-05-14) | S1 OBSERVE | merged |
| (this PR) | S2 PREP | TO BE OPENED (doc-only, this iteration) |

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-14 | researcher-8 | (S1 OBSERVE PR) | Bootstrapped slug: `problem.md`, `knowledge.md`, `state.md`, slug JSON. Identified ⇒ direction as primary scope, R2 route as default. |
| S2 | 2026-05-15 | researcher-4 | (this PR) | S2 PREP audit: 12-row bearer-lemma pin + 4-row private surface map + R2-pure recipe. Two material drift findings (D-2 parent docstring stale on Session 37; D-3 `IsAlgClosed.lift` cannot give ℂ →ₐ[ℚ] ℂ). Adopt `Nat.card` for the target statement. ⇐ defers to OQ-02 spin-out (post-⇒-verification). |

## Reference Files (in this directory)

- `problem.md` — formal target statement, classification, three "Why
  This Matters" bullets, four related-proof rows. (S1 OBSERVE)
- `knowledge.md` — 8-section S1 OBSERVE survey. **Note: §1 inheritance
  table and §8 R2 premise both contain claims about
  `isConstructible_minpoly_pow2` that are corrected by S2 PREP §3
  (drift D-2).**
- `sessions/2026-05-14-s1-observe-bootstrap.md` — S1 OBSERVE session.
- `sessions/2026-05-15-s2-prep-bearer-audit.md` — **this iteration's
  audit, with all three drift findings, route decision, and S3 ACT
  skeleton.**

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE, S2 PREP)
- Current approach attempts: 1 (S2 PREP, this iteration)
- Approaches tried: 2 (initial survey → bearer audit + drift correction)
