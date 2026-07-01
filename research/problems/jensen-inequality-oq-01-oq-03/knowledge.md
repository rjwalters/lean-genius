# Knowledge Base: jensen-inequality-oq-01-oq-03

Unweighted n-variable AM–GM inequality and its equality case, obtained as the
uniform-weight (wᵢ = 1/|s|) specialization of the parent gallery entry
`jensen-inequality-oq-01` (weighted AM–GM + equality characterization).

---

## Problem Understanding

Parent `jensen-inequality-oq-01` proved, via strict convexity of `exp`:
- `weighted_amgm_le`   : `∏ zᵢ^wᵢ ≤ ∑ wᵢ·zᵢ`               (nonneg data, weights ≥ 0 sum 1)
- `weighted_amgm_eq_iff`: `∏ zᵢ^wᵢ = ∑ wᵢ·zᵢ ↔ ∀ j k, zⱼ = zₖ` (weights > 0)
- `weighted_amgm_lt_of_ne`: strict form for positive non-constant data.

Goal here: descend to the classical unweighted statement
`(∏ zᵢ)^(1/n) ≤ (∑ zᵢ)/n`, equality iff all equal, by taking uniform weights.

---

## Insights

- The unweighted AM–GM is exactly the `wᵢ = 1/n` slice of the weighted one; no
  new analysis is required, only algebra to reshape the weighted means.
- **Key rewrite** `Real.finset_prod_rpow s z hz r : (∏ i∈s, z i ^ r) = (∏ i∈s, z i) ^ r`
  collapses the product of individual n-th roots into the single n-th root of the
  product (needs `∀ i∈s, 0 ≤ z i`). This is the geometric-mean side.
- Arithmetic side: `∑ i∈s, (|s|)⁻¹ · z i = (|s|)⁻¹ · ∑ z i` via `← Finset.mul_sum`,
  then `← div_eq_inv_mul` gives `(∑ z i)/|s|`.
- Uniform weights sum to 1: `Finset.sum_const` → `|s| • (|s|)⁻¹` → `nsmul_eq_mul`
  → `mul_inv_cancel₀` (needs `(↑|s|) ≠ 0`, i.e. `s.Nonempty`).
- The equality-case RHS `∀ j k, zⱼ = zₖ` is weight-independent, so it transfers
  verbatim — no strict-convexity argument repeated.
- `Fin n` packaging: `s = Finset.univ`, `|univ| = n` (`simp`/`Fintype.card_fin`),
  `Finset.univ_nonempty` from `haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩`, and
  `simpa` collapses `∀ j ∈ univ` to `∀ j` via `Finset.mem_univ`.

## Dead Ends

None — the direct uniform-weight specialization worked on the first attempt.

---

## Session 2026-07-01 (Session 1) — Unweighted AM–GM + equality case [COMPLETED]

**Mode**: FRESH
**Outcome**: completed — new gallery entry, VERIFIED 0-axiom.

### What I Did
- Read parent `Proofs/JensenInequalityOQ01.lean`; imported it directly.
- Proved 5 public results + 1 private helper in `Proofs/JensenInequalityOQ01OQ03.lean` (103 lines):
  `sum_uniform` (helper), `unweighted_amgm_le`, `unweighted_amgm_eq_iff`,
  `unweighted_amgm_lt_of_ne`, `amgm_fin_le`, `amgm_fin_eq_iff`.
- Verified with `lake env lean` (Docker unavailable — host containerd storage I/O
  error; single-file compile against prebuilt Mathlib oleans is the safe fallback).
- `#print axioms` on all 5 public results: only `[propext, Classical.choice, Quot.sound]`.

### Files Modified
- `proofs/Proofs/JensenInequalityOQ01OQ03.lean` (new, 103 L, 6 theorems, 0 axioms)
- `src/data/proofs/jensen-inequality-oq-01-oq-03/{meta,annotations}.json` (new)

### Next Steps
- Follow-up open questions recorded in meta: (1) quantitative stability (AM–GM gap
  bounded below by data variance); (2) descended weighted equality case for general
  rational weight vectors via majorization / Schur convexity.
