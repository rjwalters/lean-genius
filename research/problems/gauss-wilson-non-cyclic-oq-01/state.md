# State — gauss-wilson-non-cyclic-oq-01

## Current phase

S2 ACT complete (researcher-9, 2026-05-12). Phase A theorem
`prod_univ_eq_prod_two_torsion` shipped in
`proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` (≈35 lines, 0 sorries).

## Iteration log

### S2 ACT — 2026-05-12 (researcher-9)

**Result:** Phase A delivered as a standalone Lean file with 0 sorries.

**Built:**
- `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` — ~35 lines.
  Single theorem `prod_univ_eq_prod_two_torsion : ∀ G [CommGroup G]
  [Fintype G] [DecidableEq G], ∏ x : G, x = ∏ x ∈ univ.filter (·^2 = 1), x`.
  Proof via `Finset.prod_involution` with `x ↦ x⁻¹` on the non-2-torsion
  half, mirroring the existing `WilsonsTheoremOQ04OQ02.prod_eq_prod_involutions`
  (same statement, distinct namespace).
- `proofs/Proofs.lean` — alphabetically inserted import line.

**Reuse note:** The same lemma already lives in
`WilsonsTheoremOQ04OQ02.lean` under the name `prod_eq_prod_involutions`.
The OQ-01 namespace re-statement is intentional so S3 (Phase B + Phase C)
does not have to pull in the Wilson development; OQ-01 is built up
phase-by-phase to maximize independence and Mathlib-PR-readiness of each
phase (Phase A and Phase B are both candidates for upstream contribution,
per S1 knowledge.md).

**Next action (S3):** ACT — create
`proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` implementing Phase B
(product over an elementary abelian 2-group of order ≥ 4 equals 1).
The Lean sketch in `knowledge.md` flags a `sorry` for the "card is a
power of 2" step; the right approach is either
(a) hand-roll a bijection with `Module F₂` and use the sum-over-vector-
    space-of-dim ≥ 2 result, or
(b) Sylow-style argument that `Monoid.exponent ∣ 2 ∧ Fintype.card H ≥ 4
    ⇒ Fintype.card H ≥ 4 ∧ Fintype.card H = 2^k for some k ≥ 2`, then
    pair-by-translation `x ↦ h₀ · x` and observe `h₀^(|H|/2) = 1` since
    `|H|/2` is even.
Target: ~80–120 lines, 0–1 sorries.

### S1 OBSERVE — 2026-05-12 (researcher-5)

**Result:** Doc-only S1 OBSERVE, no Lean changes.

**Built:**
- `research/problems/gauss-wilson-non-cyclic-oq-01/problem.md` — full open-question statement, three-phase decomposition (Phase A: prod_univ_eq_prod_two_torsion; Phase B: prod = 1 on elementary abelian 2-groups of order ≥ 4; Phase C: specialize to (ZMod n)ˣ via parent's card_sq_eq_one_ge_three + ZMod.isCyclic_units_iff), Mathlib readiness map, sibling-overlap analysis with OQ-03.
- `research/problems/gauss-wilson-non-cyclic-oq-01/knowledge.md` — 15-row numerical sanity table (n = 1..25 plus n ∈ {8, 12, 15, 16, 24}), Lean proof sketches for each phase, Mathlib API summary, gap analysis (three potential Mathlib PRs), S2 next-action skeleton (~30-line Phase-A-only file).
- `research/problems/gauss-wilson-non-cyclic-oq-01/state.md` — this file.
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-01.json` — gallery-facing problem JSON.

**Insights captured:**
1. The product formula is *strictly easier* than OQ-03's exact count: OQ-01 needs only the cyclic/non-cyclic dichotomy (already in Mathlib via `isCyclic_units_iff`), while OQ-03 needs CRT-based exact cardinalities.
2. Three-phase decomposition has a natural independence structure — Phase A is fully generic (any finite commutative group), Phase B uses only that the 2-torsion is an elementary abelian 2-group, and only Phase C touches `ZMod`. This makes Phase A and Phase B both candidates for upstream Mathlib contribution.
3. Mathlib's `prod_univ_units_id_eq_neg_one` already covers the special case where the underlying ring is a domain (so 2-torsion of units = ±1); OQ-01 generalizes this to all `ZMod n` by handling the case where the 2-torsion is larger.
4. The pairing involution `x ↦ x⁻¹` (Phase A) and `x ↦ h₀ · x` for fixed non-identity `h₀` (Phase B) are both available via `Finset.prod_involution`.

**Next action (S2):** ACT — create `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` implementing Phase A alone. Single self-contained statement `prod_univ_eq_prod_two_torsion (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] : ∏ x : G, x = ∏ x ∈ univ.filter (·^2 = 1), x`. ~30 lines, target 0–1 sorries. Build verification expected to be straightforward (uses only `Mathlib.Algebra.BigOperators.Group.Finset.Basic`). No dependency on the parent file or OQ-03 file.

## Blockers

None at this phase. Tier B fresh slug, seeker-added 2026-05-12T09:56Z; zero open PRs at S1 push time.

## Race awareness

OQ-01 is a sibling of the active OQ-03 (currently at ACT iter 2). The two share Mathlib infrastructure but produce different artifacts and have no merge-conflict potential. researcher-5 confirmed zero open PRs and zero recent (24h) merges on the OQ-01 slug at S1 commit time.
