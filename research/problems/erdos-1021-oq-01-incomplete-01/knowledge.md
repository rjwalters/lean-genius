# Knowledge: erdos-1021-oq-01-incomplete-01

## Status: COMPLETED (verified, 0 axioms, 0 sorries)

Created `proofs/Proofs/Erdos1021OQ01Incomplete01.lean` — a self-contained, Mathlib-only,
fully verified companion to the OPEN question OQ-01 of Erdős #1021 (does ex(n,G_k)=o(n^{3/2})
for k≥4?). It does NOT resolve OQ-01; it machine-checks the unconditionally provable
scaffolding the parent survey (`Erdos1021OQ01.lean`) left as placeholders.

### Proved (9 theorems, 0 axioms, 0 sorries)
- `littleO_imp_asympBounded`: o(g) ⟹ O(g) (take ε=1) — n=0-free core of the parent's
  `oq01_strictly_beyond_kst`.
- `asympBounded_not_imp_littleO`: O(g) ⇏ o(g) (witness f=g=n^{3/2}).
- `gap k = 1/(k-1)`, `lowerExp k = 3/2 - gap k`:
  - `gap_pos`, `gap_ne_zero` (k≥2): gap positive/nonzero for every finite k.
  - `gap_strictly_decreasing`, `lowerExp_strictly_increasing`: monotone in k.
  - `gap_tendsto_zero`, `lowerExp_tendsto`: gap→0, lowerExp→3/2 — discharges the parent's
    `lower_bound_exponent_tendsto` sorry.
  - `lowerExp_lt_upper`: 3/2-1/(k-1) < 3/2 for every finite k.

### Not proved (open/external, deliberately not assumed)
- OQ-01 itself (open for all k≥4).
- KST upper bound and probabilistic lower bound (deep external inputs).

### Techniques
- ε=1 instantiation for o⟹O.
- `Filter.Tendsto.inv_tendsto_atTop` ∘ (`tendsto_natCast_atTop_atTop` shifted by -1) for 1/(k-1)→0.
- `one_div_lt_one_div_of_lt` for reciprocal monotonicity.
