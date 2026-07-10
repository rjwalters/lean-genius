# Knowledge Base: descartes-rule-of-signs-oq-01-oq-03

## Session 2026-07-09 (researcher-2) — AXIOM ELIMINATION on base file (8→7)

**Mode**: AXIOM HUNT (RICH family, score 20). My slug's on-target file
`DescartesRuleOfSignsOQ01OQ03.lean` (871 lines, 30 thm) is saturated (r6 §7 invariances).
Pivoted to the family's base `DescartesRuleOfSigns.lean`, which carried 8 axioms including
three CONCRETE `example_*` "axioms" that are not deep results at all.

**Discharged `x_cubed_minus_x_positive_roots_axiom` → theorem** (`countPositiveRoots (X³-X)=1`):
factor `X³−X = X(X−1)(X+1)`, compute `.roots` via Mathlib `roots_mul`/`roots_X`/`roots_X_sub_C`
= `{0,1,−1}`, filter `(· > 0)` leaves `{1}`, card 1. **Self-contained (pure Mathlib root API, no
downstream helper) so it discharges IN the base file** — base axiomCount 8 → 7. `#print axioms`
= `[propext, Classical.choice, Quot.sound]` only. Kept the `_axiom` name (now a theorem) so the
wrapper `x_cubed_minus_x_positive_roots` still resolves.

Recipe: `hpe : X + C 1 = X - C (-1) := by rw [map_neg, sub_neg_eq_add]` to reuse `roots_X_sub_C`
for the `(X+1)` factor; nonzero side-conditions via `X_ne_zero` / `X_sub_C_ne_zero` /
`mul_ne_zero`; finish `simp only [Multiset.filter_add, Multiset.filter_singleton]; norm_num`.

**The other two concrete axioms** `example_x2_minus_1_sign_changes` (=1) and
`example_x2_plus_1_sign_changes` (=0) are ALSO not deep — they are already PROVED axiom-free
downstream in `DescartesRuleOfSignsOQ01OQ03.lean` (~lines 481/502) using its
`countSignChanges_three_mid_zero_pos/zero` helpers. They persist in the base ONLY because
`signChangesInCoeffs` is noncomputable (classical `Fin n × Fin n` filter) and the base file
cannot import the downstream helpers (circular). Eliminating them at the base needs the Fin-3
enumeration helpers copied in, or the base `axiom`+local `example` simply deleted (nothing outside
depends on them). ACTIONABLE next: either inline the two helpers to prove them in the base, or
delete the redundant base axioms — base would then reach 5 axioms (the remaining 5 —
`descartes_upper_bound`, `descartes_parity`, `descartes_negative_roots`,
`alternating_signs_max_roots`, `derivative_reduces_sign_changes` — are the genuinely deep
Descartes-proof content).

**Verification (docker DOWN — containerd meta.db/blob I/O, NOT disk).** Direct `lean` elab vs
pinned Mathlib v4.26.0 (see [[reference-docker-down-lean-elab-verification-path]]): exit 0, only
2 pre-existing `unused variable hp` warnings. Meta `descartes-rule-of-signs` synced 8→7 axioms.
