# Current State

**Phase**: PHASE-1-COMPLETE / PHASE-2-OPEN (state.md reset from seeker-init stub 2026-03-30 → reality 2026-05-13)
**Since**: 2026-05-13T12:00:00Z (state.md sync; companion-matrix proof landed via PR #9500 ~2026-03-25)
**Iteration**: 3 (post-PR-#9500 STATE-SYNC; doc-only)

## Current Focus

Slug is the full **rational canonical form (RCF / Frobenius normal form)** open question. The companion-matrix building block (Phase 1) is fully formalized; the full RCF (Phase 2) requires ~1800 LOC of additional infrastructure that is not yet started.

## What Is Proved (Phase 1 — Companion Matrix Properties)

Main Lean file `proofs/Proofs/CayleyHamiltonReductionOQ02OQ01.lean` (397 LOC, 0 sorries, 0 axioms, 12 theorems + 1 def) proves all three core theorems for the companion matrix `C(p)` of a monic polynomial `p` of degree `d` over a field `F`:

| Theorem | Statement | Approach |
|---------|-----------|----------|
| `aeval_companionMatrix` | `p(C(p)) = 0` | Orbit argument: `C(p)^k · e₀ = eₖ` then last-column cancellation |
| `minpoly_companionMatrix` | `minpoly F (C(p)) = p` | `aeval` gives `μ ∣ p`; degree-bound contradiction shows `deg μ ≥ d` |
| `charpoly_companionMatrix` | `(C(p)).charpoly = p` | `minpoly ∣ charpoly`, both monic of degree `d` |
| `companionMatrix_linear` | `C(X - c) = [c]` (1×1 base case) | Direct unfolding |

Supporting infrastructure proved (also in main file):
- `companionMatrix` definition (subdiagonal 1s, negated coefficients in last column)
- Entry lemmas: `companionMatrix_subdiag`, `_last_col`, `_zero`
- Column-action lemmas: `companionMatrix_col`, `companionMatrix_last_col'`
- Basis-action lemmas: `companionMatrix_mulVec_basis` (`C(p) · eⱼ = eⱼ₊₁`), `companionMatrix_mulVec_last` (`C(p) · e_{d-1} = -∑ aᵢ eᵢ`)
- Orbit lemma: `companionMatrix_pow_basis` (`C(p)^k · e₀ = eₖ` for `k < d`)
- Helper lemmas (private): `sum_mulVec'`, `sum_smul_pi_single`, `aeval_eq_sum_pow`, `pow_d_mulVec_e0`, `aeval_commute_pow`, `aeval_companionMatrix_mulVec_e0`

## What Remains Open (Phase 2 — Full RCF)

The full rational canonical form theorem — "every matrix over a field is similar to `diag(C(p₁), …, C(pₖ))` with unique invariant factors `p₁ ∣ p₂ ∣ … ∣ pₖ`" — is **not started**. Main file's `## Part 5: RCF Roadmap` enumerates the missing infrastructure:

| Component | Est. LOC | Notes |
|-----------|----------|-------|
| Smith normal form for `F[X]`-matrices | ~800 | Main theoretical blocker; PID over `F[X]`, elementary row/column ops, Euclidean algorithm, diagonalization |
| `xI - A` as polynomial matrix | ~200 | Map `Mₙ(F) → Mₙ(F[X])`; invariant factors of `xI - A` = invariant factors of `A` |
| Block diagonal similarity assembly | ~300 | `Matrix.blockDiagonal`-style construction + similarity-to-block-form change of basis |
| Uniqueness of invariant factors | ~200 | Follows from uniqueness of Smith normal form |
| **Total estimated for full RCF** | **~1500–1800** | Phase 2 is significantly larger than Phase 1 |

## Per-File Inventory

| File | LOC | Sorries | Axioms | Theorems | Role |
|------|-----|---------|--------|----------|------|
| `CayleyHamiltonReductionOQ01.lean` | 305 | 0 | 0 | 14 | Sibling slug — Cayley–Hamilton via determinant |
| `CayleyHamiltonReductionOQ01OQ02.lean` | 211 | 0 | 0 | 9 | Sibling slug — block-matrix reduction |
| `CayleyHamiltonReductionOQ02.lean` | 161 | 0 | 0 | 10 | Sibling slug — parent reduction |
| **`CayleyHamiltonReductionOQ02OQ01.lean`** | **397** | **0** | **0** | **12** + 1 def | **THIS SLUG — companion matrix proper** |
| `CayleyHamiltonReductionOQ02OQ01Aristotle.lean` | 105 | 12 | 0 | 12 | Aristotle proof-search target (auxiliary lemmas, dischargeable via direct Mathlib API) |

`meta.json` reports `sorries: 12` as the **aggregated** count across main file + Aristotle companion (per `additionalFiles`). The 12 Aristotle stubs are NOT load-bearing for the three core theorems in the main file — the main proofs use direct Mathlib API calls (`minpoly.dvd`, `Matrix.minpoly_dvd_charpoly`, `Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim`).

## Aristotle Companion: Status of 12 Sorries

The `*Aristotle.lean` file is an external-proof-search target (see `research/SORRY-CLASSIFICATION.md`); the sorries are placeholder stubs that Aristotle is expected to discharge. Most of them are direct Mathlib API restatements:

| Sorry # | Lemma | Mathlib analogue |
|---------|-------|------------------|
| L30 | `minpoly_dvd_of_aeval_zero` | `minpoly.dvd F M h` |
| L35 | `minpoly_dvd_charpoly` | `Matrix.minpoly_dvd_charpoly` |
| L40 | `charpoly_natDegree` | `Matrix.charpoly_natDegree_eq_dim` |
| L45 | `dvd_antisymm_monic` | `Polynomial.Monic.dvd_iff_eq` (or ~5-line proof via degree + `Polynomial.eq_C_of_natDegree_eq_zero`) |
| L56 | `orbit_basis_independent` | Mathlib `LinearIndependent` + `Pi.basisFun` — ~3 lines |
| L61 | `stdBasis_linearIndependent` | `Pi.basisFun F (Fin d)` `.linearIndependent` |
| L68 | `annihilator_degree_bound` | Already proved in main file's `minpoly_companionMatrix` (inline lemma) |
| L77 | `monic_dvd_eq_of_same_degree` | Same as L45 |
| L82 | `monic_deg_d_card` | `Polynomial.support_card_le_natDegree_succ` |
| L87 | `charpoly_deg_eq_card` | `Matrix.charpoly_natDegree_eq_dim` (duplicate of L40) |
| L96 | `aeval_mulVec` | `map_mul` (signature actually states `aeval M (p*q) = aeval M p * aeval M q`, no `mulVec`) |
| L101 | `aeval_one` | `map_one` |

These are intentionally left for Aristotle proof search; do NOT discharge them manually as part of this STATE-SYNC.

## Active Approach

None pending. Phase 1 (companion-matrix building block) is complete; Phase 2 (full RCF) needs a separate research plan with substantially larger scope.

## Blockers

For Phase 2:
- **Smith Normal Form over `F[X]`** is not in Mathlib in directly usable form. `Mathlib.LinearAlgebra.Matrix.SmithNormalForm` exists but is primarily expressed in module-theoretic form (`Submodule.smithNormalForm`), not directly stating the matrix-diagonalization theorem with explicit invariant factors. Adapting to `F[X]`-matrices (also a PID) is the ~800-LOC blocker.

## Next Action

Two viable forward levers, each suitable for a fresh research claim with explicit Phase-2 scope:

1. **Lever A — Smith Normal Form for `F[X]`-matrices (largest payoff)**: Build `Mₙ(F[X])` → diagonal `diag(d₁, d₂, …, dₙ)` with `d₁ ∣ d₂ ∣ … ∣ dₙ` via elementary row/column operations. Likely modeled on existing Mathlib `Submodule.smithNormalForm` plus polynomial Euclidean algorithm. Spin out as a new slug or as an S-PREP under this slug after a fresh claim.
2. **Lever B — `xI - A` characteristic matrix (smaller payoff, prerequisite for Lever A)**: Define the canonical map `Mₙ(F) → Mₙ(F[X])` sending `A ↦ xI - A`. Prove that invariant factors of `xI - A` equal invariant factors of `A`. ~200 LOC, depends partially on Lever A for the "invariant factors" definition.
3. **Lever C — Sibling slugs first**: Check whether `cayley-hamilton-reduction-oq-01-oq-02` (the block-matrix sibling, also 0 sorries) has gaps that compose toward block-diagonal assembly; that piece is ~300 LOC and may be tractable independently of Smith normal form.

## Attempt Counts

- Total attempts: 2 (PR #9500 = full Phase 1 proof; this STATE-SYNC PR = doc-only)
- Current approach attempts: 0 (no active Phase-2 attempt yet)
- Approaches tried: 1 (orbit-based proof for Phase 1 — succeeded)

## Honesty Block

- **Companion-matrix fragment (Phase 1) is fully formalized in Lean 4** with 0 sorries and 0 axioms in the main file; this is a real, machine-checkable contribution.
- **Full RCF (Phase 2) is open**; the slug's stated open question — "Formalize the rational canonical form (Frobenius normal form) in Lean 4" — is NOT answered by Phase 1 alone. The companion-matrix-properties piece is roughly 25% of the estimated total LOC for full RCF.
- The 12 sorries reported in `meta.json` come from the Aristotle companion file and are NOT proof gaps in the main mathematical content. They are intentional stubs for external proof search.
- `meta.status` correctly reports `formalized` (not `verified`) because there ARE sorries in the aggregated count (Aristotle companion). The main mathematical results are verified within Phase 1 scope.
- This is a doc-only STATE-SYNC: no Lean files, no JSON `leanFiles` entries, no `meta.json` counts, no annotations were touched. The companion-matrix proof is unchanged.

## References

- `proofs/Proofs/CayleyHamiltonReductionOQ02OQ01.lean` — main Lean file (PR #9500, merged ~2026-03-25)
- `proofs/Proofs/CayleyHamiltonReductionOQ02OQ01Aristotle.lean` — Aristotle target (PR #9246, merged ~2026-03-24)
- `src/data/research/problems/cayley-hamilton-reduction-oq-02-oq-01.json` — knowledge graph (this STATE-SYNC updates `knowledge.progressSummary`, `knowledge.nextSteps`, and `currentState`; `leanFiles` already accurate)
- Sibling slugs: `cayley-hamilton`, `cayley-hamilton-reduction`, `cayley-hamilton-reduction-oq-01`, `cayley-hamilton-reduction-oq-01-oq-02`, `cayley-hamilton-reduction-oq-02`
- Mathlib bearers (used by main file): `Matrix.charpoly`, `Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim`, `Matrix.minpoly_dvd_charpoly`, `Matrix.isIntegral`, `minpoly.monic`, `minpoly.dvd`, `Polynomial.aeval`, `Polynomial.natDegree_le_of_dvd`, `Polynomial.Monic.of_mul_monic_left`
